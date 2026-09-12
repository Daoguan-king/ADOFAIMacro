// ─────────────────────────────────────────────────────────────
// Fork 修改声明（Daoguan-king，2026-09；AGPL-3.0 §5a）
// 手法模拟分片算法重写：
//  - 分片时长连续映射 max(半拍, 60/(2×阈值))，消除速率刚超过阈值时的 2 倍跳变
//  - 切点改为“距标称片长距离 − 事件间隙”综合评分，吸附到事件边界：
//    不再把手速双押/和弦拆到两只手，也不会与相邻单音并成三押
//  - 逐事件局部速率（scrFloor.speed 倍率），变速谱不再网格失配
//  - 空片不再切换手；段边界仅在有效键位配置变化时重置手序
//  - 新增 BuildTechniqueHitEventsEx 导出（旧 BuildTechniqueHitEvents 保留兼容）
// ─────────────────────────────────────────────────────────────
#define TECHNIQUE_SIMULATOR_EXPORTS
#include "TechniqueSimulator.h"
#include <vector>
#include <algorithm>
#include <cmath>
#include <cstring>
#include <memory>
#include <map>
#include <objbase.h>

using namespace std;

// ─────────────────────────────────────────────
//  全局配置
// ─────────────────────────────────────────────
static TechniqueConfig g_config;

// ─────────────────────────────────────────────
//  时间片信息
// ─────────────────────────────────────────────
struct PieceInfo {
    int    evCount;
    int    hand;        // 0=左, 1=右
    double pieceLen;
    double startTime;
    double endTime;
    int    evStart;
    int    multiplier;

    PieceInfo(int ec, int h, double pl, double st, double et, int es, int mult = 0)
        : evCount(ec), hand(h), pieceLen(pl), startTime(st), endTime(et), evStart(es), multiplier(mult) {
    }
};

// ─────────────────────────────────────────────
//  有效配置（全局 or 分段覆盖）
// ─────────────────────────────────────────────
struct EffectiveConfig {
    const unsigned char* leftKeys;   int leftKeyCount;
    const unsigned char* rightKeys;  int rightKeyCount;
    int** leftKeyOrders;  int* leftOrderLengths;  int leftOrderCounts;
    int** rightKeyOrders; int* rightOrderLengths; int rightOrderCounts;
    const double* leftPressTimes;
    const double* rightPressTimes;
    double bpmLimit;
};

static EffectiveConfig ResolveConfig(int floorIdx, int* outSegIdx = nullptr)
{
    EffectiveConfig ec{};
    // 默认：全局配置
    ec.leftKeys = g_config.leftKeys;
    ec.leftKeyCount = g_config.leftKeyCount;
    ec.rightKeys = g_config.rightKeys;
    ec.rightKeyCount = g_config.rightKeyCount;
    ec.leftKeyOrders = g_config.leftKeyOrders;
    ec.leftOrderLengths = g_config.leftOrderLengths;
    ec.leftOrderCounts = g_config.leftOrderCounts;
    ec.rightKeyOrders = g_config.rightKeyOrders;
    ec.rightOrderLengths = g_config.rightOrderLengths;
    ec.rightOrderCounts = g_config.rightOrderCounts;
    ec.leftPressTimes = g_config.leftPressTimes;
    ec.rightPressTimes = g_config.rightPressTimes;
    ec.bpmLimit = g_config.bpmLimit;

    int found = -1;
    for (int i = 0; i < g_config.segmentCount; i++) {
        auto& seg = g_config.segments[i];
        if (floorIdx >= seg.startFloor && floorIdx <= seg.endFloor) {
            ec.bpmLimit = seg.bpmLimit;
            if (seg.hasKeyOverride) {
                // 左手覆盖（仅当实际提供了按键时）
                if (seg.leftKeys && seg.leftKeyCount > 0) {
                    ec.leftKeys = seg.leftKeys;
                    ec.leftKeyCount = seg.leftKeyCount;
                    ec.leftKeyOrders = seg.leftKeyOrders;
                    ec.leftOrderLengths = seg.leftOrderLengths;
                    ec.leftOrderCounts = seg.leftOrderCounts;
                    ec.leftPressTimes = seg.leftPressTimes;
                }
                // 右手覆盖
                if (seg.rightKeys && seg.rightKeyCount > 0) {
                    ec.rightKeys = seg.rightKeys;
                    ec.rightKeyCount = seg.rightKeyCount;
                    ec.rightKeyOrders = seg.rightKeyOrders;
                    ec.rightOrderLengths = seg.rightOrderLengths;
                    ec.rightOrderCounts = seg.rightOrderCounts;
                    ec.rightPressTimes = seg.rightPressTimes;
                }
            }
            found = i;
            break;
        }
    }
    if (outSegIdx) *outSegIdx = found;
    return ec;
}

// ─────────────────────────────────────────────
//  工具函数
// ─────────────────────────────────────────────

// 二分统计 [start, endTime) 区间内的事件数
static int CountEventsInRange(const vector<double>& times, int start, double endTime)
{
    if (start >= (int)times.size()) return 0;
    int left = start, right = (int)times.size() - 1, result = start;
    while (left <= right) {
        int mid = (left + right) >> 1;
        if (times[mid] < endTime) { result = mid + 1; left = mid + 1; }
        else { right = mid - 1; }
    }
    return result - start;
}

// ─────────────────────────────────────────────
//  分片基础时长
//  连续映射：不短于“速度阈值”对应的最小交替周期（60/(2*limit)）。
//  旧实现用八度折叠（rate 刚超过 limit 时片长 2 倍跳变），
//  会导致铺面 BPM 略微超过阈值时手法突变，此处改为连续钳制。
// ─────────────────────────────────────────────
static double GetBasePieceLength(double bpm, double speed, double limit)
{
    double rate = bpm * speed;
    if (rate < 1e-9) rate = 1e-9;
    double halfBeat = 60.0 / (2.0 * rate);
    double minPeriod = (limit > 1e-9) ? (60.0 / (2.0 * limit)) : 0.0;
    return halfBeat > minPeriod ? halfBeat : minPeriod;
}

// 计算松键时刻偏移量
static double CalculateReleaseTime(double pStart, const PieceInfo& cur, const PieceInfo& next,
    double t, double ratio)
{
    if (next.pieceLen > cur.pieceLen + 5e-6) {
        if (pStart + cur.pieceLen > cur.endTime + 5e-6)
            return (next.endTime - t) * ratio / 2.0;
        else
            return (pStart + cur.pieceLen * 2.0 - t) * ratio / 2.0;
    }
    else {
        if (pStart + cur.pieceLen + 5e-6 < cur.endTime)
            return (pStart + cur.pieceLen + next.pieceLen - t) * ratio / 2.0;
        else
            return (next.endTime - t) * ratio / 2.0;
    }
}

// 修正同键重叠（按下前必须先松开上一次）
static void FixSameKeyOverlaps(vector<HitEvent>& events)
{
    if (events.empty()) return;

    sort(events.begin(), events.end(),
        [](const HitEvent& a, const HitEvent& b) { return a.TriggerTime < b.TriggerTime; });

    map<unsigned char, int> pending;
    int n = (int)events.size();

    for (int i = 0; i < n; i++) {
        auto& ev = events[i];

        if (ev.ReleaseOnly) {
            if (ev.ReleaseKeyCode != 0) pending.erase(ev.ReleaseKeyCode);
            continue;
        }

        unsigned char kc = ev.KeyCode;
        if (kc == 0) continue;

        auto it = pending.find(kc);
        if (it != pending.end()) {
            auto& relEv = events[it->second];
            if (relEv.TriggerTime >= ev.TriggerTime)
                relEv.TriggerTime = ev.TriggerTime - 1e-6;
            pending.erase(it);
        }

        for (int j = i + 1; j < n; j++) {
            auto& fwd = events[j];
            if (fwd.ReleaseOnly && fwd.ReleaseKeyCode == kc && !fwd.IsHoldRelated) {
                pending[kc] = j;
                break;
            }
        }
    }

    sort(events.begin(), events.end(),
        [](const HitEvent& a, const HitEvent& b) { return a.TriggerTime < b.TriggerTime; });
}

// ─────────────────────────────────────────────
//  导出函数：SetTechniqueConfig
// ─────────────────────────────────────────────
void SetTechniqueConfig(TechniqueConfig* config)
{
    if (config) g_config = *config;
}

// ─────────────────────────────────────────────
//  导出函数：BuildTechniqueHitEventsEx
//
//  speedMuls: 逐事件速度倍率（相对基准 BPM，来自 scrFloor.speed）；
//             为 nullptr 时回退到全局 speed 参数（保持旧行为）。
// ─────────────────────────────────────────────
HitEvent* BuildTechniqueHitEventsEx(
    double* entryTimes,
    int* pressTypes,
    int* floorIndices,
    double* speedMuls,
    int     eventCount,
    double  bpm,
    double  speed,
    int* outEventCount)
{
    *outEventCount = 0;
    if (eventCount == 0 || !entryTimes || !pressTypes || !floorIndices)
        return nullptr;

    try {
        vector<double> evTime(entryTimes, entryTimes + eventCount);
        vector<int>    evPress(pressTypes, pressTypes + eventCount);
        vector<int>    evFloor(floorIndices, floorIndices + eventCount);

        // ── 初始阈值（取第一个事件所属分段）────────────────────
        double lastSegLimit = g_config.bpmLimit;
        int    lastSegIdx   = -2;  // -2 = 未初始化
        if (g_config.segmentCount > 0 && eventCount > 0) {
            int segIdx;
            auto ec0 = ResolveConfig(evFloor[0], &segIdx);
            lastSegLimit = ec0.bpmLimit;
            lastSegIdx   = segIdx;     // 首次不触发边界重置
        }
        double baseLen = GetBasePieceLength(bpm, speedMuls ? speedMuls[0] : speed, lastSegLimit);

        double nowT = 0.0;
        int    nowD = 0;
        int    hand = (g_config.handPreference == 0) ? -1 : 1; // -1=左主, 1=右主
        int    mult = 0;
        long long mCnt[16] = {};
        long long mCntPre[16] = {};
        int  canMulti = 0;
        bool needBack = false;

        // 段边界处用于比较“有效键位是否变化”
        const unsigned char* prevLeftKeys = g_config.leftKeys;
        int prevLeftKeyCount = g_config.leftKeyCount;
        const unsigned char* prevRightKeys = g_config.rightKeys;
        int prevRightKeyCount = g_config.rightKeyCount;
        if (g_config.segmentCount > 0 && eventCount > 0) {
            int segIdx0;
            auto ecInit = ResolveConfig(evFloor[0], &segIdx0);
            prevLeftKeys = ecInit.leftKeys;  prevLeftKeyCount = ecInit.leftKeyCount;
            prevRightKeys = ecInit.rightKeys; prevRightKeyCount = ecInit.rightKeyCount;
        }

        vector<PieceInfo> pieces;
        pieces.reserve(static_cast<std::vector<PieceInfo, std::allocator<PieceInfo>>::size_type>(eventCount / 4) + 4);

        // ── 时间片划分 ────────────────────────────────────────
        while (nowD < eventCount) {

            // 根据当前地板索引解析有效配置及段索引
            int curSegIdx;
            auto ec = ResolveConfig(evFloor[nowD], &curSegIdx);

            // 段边界：仅当有效键位配置变化时才重置连续状态（手交替·倍乘·回溯）。
            // 只改 BPM 阈值的分段不应打断手序：历史 bug——配置档里残留的
            // [0,0] 空分段会在第 2 个事件处触发重置，导致起始手连按两次。
            if (curSegIdx != lastSegIdx) {
                bool keysChanged =
                    ec.leftKeys != prevLeftKeys || ec.leftKeyCount != prevLeftKeyCount ||
                    ec.rightKeys != prevRightKeys || ec.rightKeyCount != prevRightKeyCount;
                if (keysChanged) {
                    hand = (g_config.handPreference == 0) ? -1 : 1;
                    mult = 0;
                    memset(mCnt, 0, sizeof(mCnt));
                    memset(mCntPre, 0, sizeof(mCntPre));
                    canMulti = 0;
                    needBack = false;
                }
                prevLeftKeys = ec.leftKeys;   prevLeftKeyCount = ec.leftKeyCount;
                prevRightKeys = ec.rightKeys; prevRightKeyCount = ec.rightKeyCount;
                lastSegLimit = ec.bpmLimit;
                lastSegIdx = curSegIdx;
            }

            // 局部速率：逐事件速度倍率来自 scrFloor.speed（SetSpeed/BPM 事件已折算）。
            // 连续钳制基础片长（见 GetBasePieceLength），避免阈值处手法突变。
            double localSpeed = speedMuls ? speedMuls[nowD] : speed;
            baseLen = GetBasePieceLength(bpm, localSpeed, lastSegLimit);

            // 防止死循环
            if (pieces.size() > (size_t)eventCount * 64) break;

            double pLen = baseLen / pow(2.0, mult);
            if (pLen < 1e-9) pLen = 1e-9;

            int cnt = CountEventsInRange(evTime, nowD, nowT + pLen * 0.995);
            int csH = (hand == 1) ? 1 : 0;
            int maxK = (csH == 0) ? ec.leftKeyCount : ec.rightKeyCount;
            int mainHand = (g_config.handPreference == 0) ? -1 : 1;
            bool isOffHand = (hand != mainHand);

            // 按键数超限：提升倍乘
            if (cnt > maxK) {
                if (canMulti == 1 && isOffHand) needBack = true;
                if (mult < 7) { mult++; mCnt[mult] = 0; continue; }
                else { cnt = maxK; }
            }

            // 回溯到上一片（由主手重新处理）
            if (needBack && !pieces.empty()) {
                needBack = false;
                hand = mainHand;
                auto& prev = pieces.back();
                nowT = prev.startTime;
                nowD = prev.evStart;
                memcpy(mCnt, mCntPre, sizeof(mCnt));
                mult = prev.multiplier + 1;
                if (mult > 7) mult = 7;
                pieces.pop_back();
                canMulti = 0;
                continue;
            }

            // ── 事件边界对齐（距离 + 间隙综合评分）───────────────
            // 在标称片长对应的“事件数 ± 窗口”内选切点：
            //   score = |切点时长 − 标称片长| − 切点间隙
            // 纯“最大间隙”会把手速双押与相邻单音并成三押；
            // 纯“最近距离”会把快双押/和弦从中间切开；加权兼顾两者。
            // speedChangeTolerance 控制窗口宽度：0=仅邻近（按簇分组），
            // 越大越倾向合并相邻簇成长连打（0.5 → 窗口 ±3）。
            // 切点取“下一事件时刻”（cut-before），下一片直接从该事件起步。
            double pieceLen = pLen;
            if (cnt == 0) {
                // 空片（长间隔）：延伸至下一事件前，且不切换手，
                // 避免旧实现“每个空片翻一次手”导致的相位漂移。
                double gapEnd = evTime[nowD];
                if (gapEnd > nowT + 1e-12) {
                    pieces.emplace_back(0, csH, gapEnd - nowT, nowT, gapEnd, nowD, mult);
                    nowT = gapEnd;
                    canMulti = 1;
                    continue;
                }
            }
            else {
                int win = 1 + (int)(g_config.speedChangeTolerance * 4.0 + 0.5);
                int lo = cnt - win; if (lo < 1) lo = 1;
                int hi = cnt + win;
                if (hi > maxK) hi = maxK;
                if (hi > eventCount - nowD) hi = eventCount - nowD;
                if (lo > hi) lo = hi;
                int    bestK = lo;
                double bestScore = 0.0, bestB = 0.0;
                for (int k = lo; k <= hi; k++) {
                    double gap, b;
                    if (nowD + k < eventCount) {
                        gap = evTime[nowD + k] - evTime[nowD + k - 1];
                        b   = evTime[nowD + k];      // 切在下一事件之前
                    } else {
                        gap = (eventCount >= 2)
                            ? (evTime[eventCount - 1] - evTime[eventCount - 2]) : pLen;
                        b   = evTime[eventCount - 1] + gap;
                    }
                    double score = fabs((b - nowT) - pLen) - gap;
                    if (k == lo || score < bestScore) {
                        bestK = k; bestScore = score; bestB = b;
                    }
                }
                cnt = bestK;
                pieceLen = bestB - nowT;
            }

            // 提交时间片
            memcpy(mCntPre, mCnt, sizeof(mCnt));
            pieces.emplace_back(cnt, csH, pieceLen, nowT, nowT + pieceLen, nowD, mult);

            // 更新级联倍乘计数器
            for (int c = mult; c > 0; c--) {
                mCnt[c] += (long long)pow(2, 16 - (mult - c));
                mCnt[c] %= (1LL << 18);
            }
            while (mult > 0 && mCnt[mult] == 0) mult--;

            nowD += cnt;
            nowT += pieceLen;
            hand = -hand;
            canMulti = 1;

            // 微误差矫正
            if (nowD < eventCount && fabs(evTime[nowD] - nowT) < pLen * 0.01)
                nowT = evTime[nowD];
        }

        // 哨兵片
        if (!pieces.empty()) {
            auto& lp = pieces.back();
            pieces.emplace_back(0, 1 - lp.hand, lp.pieceLen,
                lp.endTime, lp.endTime + lp.pieceLen, nowD);
        }

        // ── 生成 HitEvent 列表 ────────────────────────────────
        vector<HitEvent> output;
        output.reserve(static_cast<std::vector<HitEvent, std::allocator<HitEvent>>::size_type>(eventCount) * 2);

        bool          activeHold = false;
        unsigned char activeHoldKey = 0;
        int           lastSegIdxEvent = -2;

        for (size_t pcnt = 0; pcnt + 1 < pieces.size(); pcnt++) {
            auto& cur = pieces[pcnt];
            auto& next = pieces[pcnt + 1];
            double pStart = (pcnt > 0) ? pieces[pcnt - 1].endTime : 0.0;

            for (int i = 0; i < cur.evCount; i++) {
                int    idx = cur.evStart + i;
                int    press = evPress[idx];
                double t = evTime[idx];

                // hold 尾：松开当前长按键
                if (press == -1) {
                    if (activeHold) {
                        HitEvent ev = {};
                        ev.TriggerTime = t;
                        ev.KeyCode = 0;
                        ev.ReleaseOnly = TRUE;
                        ev.IsHoldRelated = TRUE;
                        ev.ReleaseKeyCode = activeHoldKey;
                        output.push_back(ev);
                        activeHold = false;
                        activeHoldKey = 0;
                    }
                    continue;
                }

                // ── 按当前地板解析有效键位配置 ──────────────────
                int curFloor = (idx < (int)evFloor.size()) ? evFloor[idx] : evFloor.back();

                // ── 段边界：释放活跃 hold 键 ──
                int curSegIdx;
                auto ec = ResolveConfig(curFloor, &curSegIdx);
                if (curSegIdx != lastSegIdxEvent) {
                    if (activeHold && lastSegIdxEvent != -2) {
                        HitEvent relEv = {};
                        relEv.TriggerTime = t - 0.000001;
                        relEv.KeyCode = 0;
                        relEv.ReleaseOnly = TRUE;
                        relEv.IsHoldRelated = TRUE;
                        relEv.ReleaseKeyCode = activeHoldKey;
                        output.push_back(relEv);
                        activeHold = false;
                        activeHoldKey = 0;
                    }
                    lastSegIdxEvent = curSegIdx;
                }

                const unsigned char* keys = (cur.hand == 0) ? ec.leftKeys : ec.rightKeys;
                int                  keyCount = (cur.hand == 0) ? ec.leftKeyCount : ec.rightKeyCount;
                int** orders = (cur.hand == 0) ? ec.leftKeyOrders : ec.rightKeyOrders;
                int* orderLens = (cur.hand == 0) ? ec.leftOrderLengths : ec.rightOrderLengths;
                int                  orderCounts = (cur.hand == 0) ? ec.leftOrderCounts : ec.rightOrderCounts;
                const double* pressTimes = (cur.hand == 0) ? ec.leftPressTimes : ec.rightPressTimes;

                // 保护：若 keyCount 为 0，跳过
                if (!keys || keyCount <= 0) continue;

                int oi = min(cur.evCount - 1, keyCount - 1);
                int ki;
                if (oi < orderCounts && orders && orders[oi] && i < orderLens[oi])
                    ki = orders[oi][i];
                else
                    ki = i % keyCount;
                ki = max(0, min(ki, keyCount - 1));

                unsigned char kc = keys[ki];
                double        ratio = (pressTimes && ki < keyCount) ? pressTimes[ki] : 0.8;
                BOOL isHoldHead = (press == 2) ? TRUE : FALSE;

                // 若已有长按键且新事件是 hold 头，先强制释放
                if (isHoldHead && activeHold) {
                    HitEvent relPrev = {};
                    relPrev.TriggerTime = t - 0.000001;
                    relPrev.KeyCode = 0;
                    relPrev.ReleaseOnly = TRUE;
                    relPrev.IsHoldRelated = TRUE;
                    relPrev.ReleaseKeyCode = activeHoldKey;
                    output.push_back(relPrev);
                    activeHold = false;
                    activeHoldKey = 0;
                }

                // 按下事件
                HitEvent pressEv = {};
                pressEv.TriggerTime = t;
                pressEv.KeyCode = kc;
                pressEv.ReleaseOnly = FALSE;
                pressEv.IsHoldRelated = isHoldHead;
                pressEv.ReleaseKeyCode = 0;
                output.push_back(pressEv);

                if (isHoldHead) {
                    activeHold = true;
                    activeHoldKey = kc;
                    continue; // hold 头不插入定时松键，等待 hold 尾事件
                }

                // ── 计算松键时刻 ──────────────────────────────────
                double dur = CalculateReleaseTime(pStart, cur, next, t, ratio);
                double rel = t + dur;

                if (next.hand != cur.hand || next.evCount == 0) {
                    if (rel >= next.endTime) rel = next.endTime - 1e-6;
                }
                else {
                    if (rel >= cur.endTime) rel = cur.endTime - 1e-6;
                }
                if (rel <= t) rel = t + (next.endTime - t) * 0.4;

                HitEvent releaseEv = {};
                releaseEv.TriggerTime = rel;
                releaseEv.KeyCode = 0;
                releaseEv.ReleaseOnly = TRUE;
                releaseEv.IsHoldRelated = FALSE;
                releaseEv.ReleaseKeyCode = kc;
                output.push_back(releaseEv);
            }
        }

        // 确保最后的长按键被释放
        if (activeHold && !pieces.empty()) {
            HitEvent finalRel = {};
            finalRel.TriggerTime = pieces.back().endTime;
            finalRel.KeyCode = 0;
            finalRel.ReleaseOnly = TRUE;
            finalRel.IsHoldRelated = TRUE;
            finalRel.ReleaseKeyCode = activeHoldKey;
            output.push_back(finalRel);
        }

        FixSameKeyOverlaps(output);

        // ── 分配 CoTaskMem 并返回 ─────────────────────────────
        size_t   byteSize = output.size() * sizeof(HitEvent);
        HitEvent* result = (HitEvent*)CoTaskMemAlloc(byteSize);
        if (!result) { *outEventCount = 0; return nullptr; }
        memcpy(result, output.data(), byteSize);
        *outEventCount = (int)output.size();
        return result;

    }
    catch (...) {
        *outEventCount = 0;
        return nullptr;
    }
}

// ─────────────────────────────────────────────
//  导出函数：BuildTechniqueHitEvents（旧接口，兼容保留）
// ─────────────────────────────────────────────
HitEvent* BuildTechniqueHitEvents(
    double* entryTimes,
    int* pressTypes,
    int* floorIndices,
    int     eventCount,
    double  bpm,
    double  speed,
    int* outEventCount)
{
    return BuildTechniqueHitEventsEx(
        entryTimes, pressTypes, floorIndices, nullptr,
        eventCount, bpm, speed, outEventCount);
}

// ─────────────────────────────────────────────
//  导出函数：FreeHitEvents
// ─────────────────────────────────────────────
void FreeHitEvents(HitEvent* events)
{
    if (events) CoTaskMemFree(events);
}

// ─────────────────────────────────────────────
//  DLL 入口
// ─────────────────────────────────────────────
BOOL APIENTRY DllMain(HMODULE, DWORD, LPVOID) { return TRUE; }