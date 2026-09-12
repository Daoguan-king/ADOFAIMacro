// ─────────────────────────────────────────────────────────────
// Fork 修改声明（Daoguan-king，2026-09；AGPL-3.0 §5a）
// 手法模拟分片算法重写：
//  - 分片时长量化到局部半拍：超过阈值时取 h·round(rate/limit)，
//    既避免八度折叠在阈值处的 2 倍跳变，又保持与谱面节拍网格对齐
//    （修复 SetSpeed 提速后片长失配、被切成 3-1-1 碎块的问题）
//  - 切点改为“距标称片长距离（欠长加倍）− 事件间隙”综合评分，
//    吸附到事件边界：不再把手速双押/和弦拆到两只手，也不会把
//    可合并的连打簇提前换手（旧实现偶发 3-1-1）
//  - 逐事件局部速率（scrFloor.speed 倍率），取“下一事件”所属层速率：
//    事件 i→i+1 的间隔由第 i+1 层速度决定，变速段首片不再沿用旧速率
//  - 慢速段（速率未超阈值）片长不超过到下一事件的间隔（下限阈值半拍）：
//    低 BPM 下更细网格的慢音符（45° 砖等）不再被并进同一只手
//  - 换手仅在“实际音符速率”（按事件间隔折算，音符/分钟；90° 砖是砖 BPM
//    的 2 倍、45° 砖 4 倍、直线砖 1 倍）超过阈值时进行；未超阈值保持
//    单手连续敲击（低 KPS 段单指连打），不再全程左右交替
//  - 空片不再切换手；段边界仅在有效键位配置变化时重置手序
//  - 片内事件数超过单手按键数时，直接取满 maxK 个事件（用满全部按键再换手），
//    替代旧的 2 的幂细分（旧实现在极高 BPM 下会停在只用 3 键之类的尺寸）
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

    PieceInfo(int ec, int h, double pl, double st, double et, int es)
        : evCount(ec), hand(h), pieceLen(pl), startTime(st), endTime(et), evStart(es) {
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
//  局部半拍 h = 60/(2*rate)。速率超过阈值时把片长量化到 h 的整数倍
//  k = round(rate/limit)（至少 1）：换手频率仍受阈值约束，且片长始终
//  落在谱面节拍网格上。此前的“连续钳制”直接取 60/(2*limit)，一旦
//  SetSpeed/BPM 事件改变局部速率，片长就与事件网格失配，"距离−间隙"
//  评分会把变速段切成 3-1-1 之类的碎块（表现为速度事件一开手法就变）。
// ─────────────────────────────────────────────
static double GetBasePieceLength(double bpm, double speed, double limit)
{
    double rate = bpm * speed;
    if (rate < 1e-9) rate = 1e-9;
    double halfBeat = 30.0 / rate;
    if (limit <= 1e-9) return halfBeat;
    double k = floor(rate / limit + 0.5);
    if (k < 1.0) k = 1.0;
    return halfBeat * k;
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
        double baseLen = GetBasePieceLength(bpm,
            speedMuls ? speedMuls[(eventCount > 1) ? 1 : 0] : speed, lastSegLimit);

        double nowT = 0.0;
        int    nowD = 0;
        int    hand = (g_config.handPreference == 0) ? -1 : 1; // -1=左主, 1=右主

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

            // 段边界：仅当有效键位配置变化时才重置连续状态（手交替）。
            // 只改 BPM 阈值的分段不应打断手序：历史 bug——配置档里残留的
            // [0,0] 空分段会在第 2 个事件处触发重置，导致起始手连按两次。
            if (curSegIdx != lastSegIdx) {
                bool keysChanged =
                    ec.leftKeys != prevLeftKeys || ec.leftKeyCount != prevLeftKeyCount ||
                    ec.rightKeys != prevRightKeys || ec.rightKeyCount != prevRightKeyCount;
                if (keysChanged) {
                    hand = (g_config.handPreference == 0) ? -1 : 1;
                }
                prevLeftKeys = ec.leftKeys;   prevLeftKeyCount = ec.leftKeyCount;
                prevRightKeys = ec.rightKeys; prevRightKeyCount = ec.rightKeyCount;
                lastSegLimit = ec.bpmLimit;
                lastSegIdx = curSegIdx;
            }

            // 局部速率：事件 i 的时刻是“进入第 i+1 层”的时间，事件 i→i+1
            // 的间隔由第 i+1 层的 speed 决定；分片起点的速率取下一事件倍率
            // （末事件回退当前），否则变速段第一片会沿用旧速率、切分错位。
            double localSpeed;
            if (speedMuls) {
                int si = (nowD + 1 < eventCount) ? nowD + 1 : nowD;
                localSpeed = speedMuls[si];
            } else {
                localSpeed = speed;
            }
            baseLen = GetBasePieceLength(bpm, localSpeed, lastSegLimit);

            // 慢速段（局部速率未超阈值）：片长不超过到下一事件的间隔，
            // 下限取阈值半拍。否则低 BPM 下"半拍"可能长达 1 秒，会把
            // 45° 等更细网格的慢音符也并进同一只手（能用 2 键却用 4 键），
            // 长按释放时刻也会被拖到整片长度。
            if (bpm * localSpeed <= lastSegLimit && nowD + 1 < eventCount) {
                double gap = evTime[nowD + 1] - evTime[nowD];
                double minPeriod = (lastSegLimit > 1e-9) ? (30.0 / lastSegLimit) : 0.0;
                double cap = (gap > minPeriod) ? gap : minPeriod;
                if (baseLen > cap) baseLen = cap;
            }

            // 防止死循环
            if (pieces.size() > (size_t)eventCount * 64) break;

            double pLen = baseLen;
            if (pLen < 1e-9) pLen = 1e-9;

            int pieceStartD = nowD;   // 本片起始事件（换手判定用）

            int cnt = CountEventsInRange(evTime, nowD, nowT + pLen * 0.995);
            int csH = (hand == 1) ? 1 : 0;
            int maxK = (csH == 0) ? ec.leftKeyCount : ec.rightKeyCount;

            // 按键数超限：本片直接取满该手全部按键（maxK 个事件）。
            // 旧实现按 2 的幂细分片长，片内事件数可能停在 maxK 以下
            // （例如 5 指只用 3 指），且随速率升高不单调；高密度下应让
            // 单手滚完所有手指再换手。pLen 对准第 maxK 个事件的切点，
            // 使下面的评分保持该片长而不是把它缩回更小的片。
            if (cnt > maxK) {
                cnt = maxK;
                int cut = nowD + maxK;
                if (cut < eventCount)
                    pLen = evTime[cut] - nowT;
            }

            // ── 事件边界对齐（距离 + 间隙综合评分）───────────────
            // 在标称片长对应的“事件数 ± 窗口”内选切点：
            //   score = 切点时长对标的偏离 − 切点间隙
            // 纯“最大间隙”会把手速双押与相邻单音并成三押；
            // 纯“最近距离”会把快双押/和弦从中间切开；加权兼顾两者。
            // 欠长（换手早于标称片长）代价加倍：宁可把当前手速簇完整
            // 收进一片，也不要在可合并时提前换手（否则 SetSpeed 提速段
            // 会被切成 3-1-1 式碎块）。
            // speedChangeTolerance 控制窗口宽度：0=仅邻近（按簇分组），
            // 越大越倾向合并相邻簇成长连打（0.5 → 窗口 ±3）。
            // 切点取“下一事件时刻”（cut-before），下一片直接从该事件起步。
            double pieceLen = pLen;
            if (cnt == 0) {
                // 空片（长间隔）：延伸至下一事件前，且不切换手，
                // 避免旧实现“每个空片翻一次手”导致的相位漂移。
                double gapEnd = evTime[nowD];
                if (gapEnd > nowT + 1e-12) {
                    pieces.emplace_back(0, csH, gapEnd - nowT, nowT, gapEnd, nowD);
                    nowT = gapEnd;
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
                    double dev = (b - nowT) - pLen;
                    double score = ((dev < 0.0) ? (-dev * 2.0) : dev) - gap;
                    if (k == lo || score < bestScore) {
                        bestK = k; bestScore = score; bestB = b;
                    }
                }
                cnt = bestK;
                pieceLen = bestB - nowT;
            }

            // 提交时间片
            pieces.emplace_back(cnt, csH, pieceLen, nowT, nowT + pieceLen, nowD);

            nowD += cnt;
            nowT += pieceLen;

            // 换手策略：按“本片起始音符的实际速率”（音符/分钟）判断是否换手，
            // 不能直接用谱面 BPM——90° 砖一块 = 半拍，实际音符密度是砖 BPM 的
            // 2 倍（45° 砖 4 倍、直线砖 1 倍），用事件间隔换算可同时覆盖
            // SetSpeed 变速与任意角度。未超阈值时保持单手连续敲击（低 KPS
            // 段即单指连打），超过阈值才左右交替。
            if (nowD < eventCount) {
                int j = pieceStartD + 1;
                while (j < eventCount && evTime[j] <= evTime[pieceStartD] + 1e-9) j++; // 跳过同刻和弦
                if (j < eventCount) {
                    double gap = evTime[j] - evTime[pieceStartD];
                    if (gap > 1e-9 && 60.0 / gap > lastSegLimit)
                        hand = -hand;
                }
            }

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