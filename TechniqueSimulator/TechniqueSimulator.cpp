// ─────────────────────────────────────────────────────────────
// Fork 修改声明（Daoguan-king，2026-09；AGPL-3.0 §5a）
// 手法模拟分片算法重写：
//  - 分片时长量化到局部半拍：超过阈值时取 h·round(rate/limit)，
//    既避免八度折叠在阈值处的 2 倍跳变，又保持与谱面节拍网格对齐
//    （修复 SetSpeed 提速后片长失配、被切成 3-1-1 碎块的问题）
//  - 分片基础时长改为跟随“实际音符间隔”gapNext × round(音符速率/(2·阈值))：
//    非 90° 砖 / SetSpeed 组合下局部半拍的整数倍与实际音符间隔不整除，
//    量化片长会跨过下一个音符，把单音与紧跟的双押/和弦并到同一只手，
//    造成换手相位漂移（雪花谱由 R2 L1 R1 L3… 恢复为稳定的 R2 L1 R1 L1）；
//    对 90° 砖（间隔=局部半拍）与旧公式完全一致，不影响常规谱面
//  - 切点改为“距标称片长距离（欠长加倍）− 事件间隙”综合评分，
//    吸附到事件边界：不再把手速双押/和弦拆到两只手，也不会把
//    可合并的连打簇提前换手（旧实现偶发 3-1-1）
//  - 逐事件局部速率（scrFloor.speed 倍率），取“下一事件”所属层速率：
//    事件 i→i+1 的间隔由第 i+1 层速度决定，变速段首片不再沿用旧速率
//  - 慢速段（速率未超阈值）片长不超过到下一事件的间隔（下限阈值半拍）：
//    低 BPM 下更细网格的慢音符（45° 砖等）不再被并进同一只手
//  - 换手仅在“实际音符速率”（按事件间隔折算，音符/分钟；90° 砖是砖 BPM
//    的 2 倍、45° 砖 4 倍、直线砖 1 倍）超过阈值时进行；未超阈值切回并
//    保持起始手（主手）连续敲击（低 KPS 段单指连打），不再全程左右交替
//  - 按压时长以“本片音符跨度 + 最小内部间隔”为上限：片尾跨暂停/长空拍时
//    不会一直按住；另提供 pressDurationMode=1 切换旧版 1.3.0.30 折叠时长
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

// “同一时刻”判定容差：游戏里双押/和弦各砖的 entryTime 可能相差几十微秒
// （角度取整误差），手法上应视为同刻。1ms 远小于任何真实音符间隔。
static const double kSameMomentEps = 1e-3;

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

// 事件 idx 处的“实际音符速率”（音符/分钟）：取该事件之前最近的间隔
// （即它所在的节奏），第一个音符回退到向后间隔；同刻和弦跳过。
// 无可用间隔返回 0。
// 用“之前”的间隔可避免把快段最后一个音误判成慢音（它后面紧跟慢段），
// 90° 砖一块 = 半拍，因此该速率是砖 BPM 的 2 倍（45° 砖 4 倍、直线砖 1 倍）。
static double LocalNoteRate(const vector<double>& evTime, int idx)
{
    int n = (int)evTime.size();
    int k = idx - 1;
    while (k >= 0 && evTime[idx] <= evTime[k] + 1e-9) k--;   // 跳过同刻和弦
    double gap = 0.0;
    if (k >= 0) gap = evTime[idx] - evTime[k];
    if (gap <= 1e-9) {                                        // 首音：回退向后间隔
        int j = idx + 1;
        while (j < n && evTime[j] <= evTime[idx] + 1e-9) j++;
        if (j < n) gap = evTime[j] - evTime[idx];
    }
    return (gap > 1e-9) ? (60.0 / gap) : 0.0;
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

// 旧版（1.3.0.30）按压时长基准：把速率八度折叠进 (limit/2, limit]，
// 再取该速率对应的半拍。片长恒在 [60/(2*limit), 60/limit)，因此慢谱
// 的按键也是一次短按，不会一直按到下一个音符。仅用于 pressDurationMode=1。
static double GetLegacyPressLength(double bpm, double speed, double limit)
{
    double r = bpm * speed;
    if (r < 1e-9) r = 1e-9;
    if (limit > 1e-9) {
        while (r > limit)         r /= 2.0;
        while (r <= limit / 2.0)  r *= 2.0;
    }
    return (r > 1e-9) ? (30.0 / r) : 0.0;
}

// 计算松键时刻偏移量（按分片结构）
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

// 该音与前后相邻“不同时刻”音符的较小间隔（同刻和弦跳过后取另一侧，
// 孤立音回退 fallback）。用于限制按压时长，避免跨暂停/长空拍一直按住。
static double GetLocalPressInterval(const vector<double>& evTime, int idx, double fallback)
{
    int n = (int)evTime.size();
    double gp = 0.0, gn = 0.0;
    int k = idx - 1;
    while (k >= 0 && evTime[idx] <= evTime[k] + 1e-9) k--;
    if (k >= 0) gp = evTime[idx] - evTime[k];
    int j = idx + 1;
    while (j < n && evTime[j] <= evTime[idx] + 1e-9) j++;
    if (j < n) gn = evTime[j] - evTime[idx];

    double unit;
    if (gp > 1e-9 && gn > 1e-9) unit = (gp < gn) ? gp : gn;
    else                        unit = (gp > gn) ? gp : gn;
    if (unit <= 1e-9) unit = fallback;
    return unit;
}

// 按“实际音符间隔”计算折叠按压基准（仿人可见的最短按压，约半拍），
// 与 GetLegacyPressLength 的区别是：速率由真实音符间隔 60/gap 折算，而不是
// 局部地板 BPM(bpm*speed)。匀速谱面（各音符间隔相同、但 SetSpeed 让局部
// speed 不同）因此得到一致的按压时长；同刻双押/和弦也共享同一基准，不会
// 出现同一双押里一个键按 45ms、另一个按 63ms 的情况。
static double GetNoteFoldedPressLength(const vector<double>& evTime, int idx, double limit)
{
    int n = (int)evTime.size();
    double gp = 0.0, gn = 0.0;
    int k = idx - 1;
    while (k >= 0 && evTime[idx] <= evTime[k] + kSameMomentEps) k--;
    if (k >= 0) gp = evTime[idx] - evTime[k];
    int j = idx + 1;
    while (j < n && evTime[j] <= evTime[idx] + kSameMomentEps) j++;
    if (j < n) gn = evTime[j] - evTime[idx];

    double unit;
    if (gp > 1e-9 && gn > 1e-9) unit = (gp < gn) ? gp : gn;
    else                        unit = (gp > gn) ? gp : gn;

    double r = (unit > 1e-9) ? (60.0 / unit) : 0.0;
    if (r < 1e-9) r = 1e-9;
    if (limit > 1e-9) {
        while (r > limit)         r /= 2.0;
        while (r <= limit / 2.0)  r *= 2.0;
    }
    return (r > 1e-9) ? (30.0 / r) : 0.0;
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
        const int mainHand = (g_config.handPreference == 0) ? -1 : 1; // -1=左主, 1=右主
        int    hand = mainHand;
        bool   anyNote = false;   // 是否已经产生过音符（首音/段首保持起始手）

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
                    hand = mainHand;
                    anyNote = false;   // 新键位段首片回到起始手
                }
                prevLeftKeys = ec.leftKeys;   prevLeftKeyCount = ec.leftKeyCount;
                prevRightKeys = ec.rightKeys; prevRightKeyCount = ec.rightKeyCount;
                lastSegLimit = ec.bpmLimit;
                lastSegIdx = curSegIdx;
            }

            // 换手策略（在生成当前片之前决定本片用哪只手）：
            //  - 实际音符速率 > 阈值：与上一片交替（快段左右手轮流）；
            //  - 未超阈值：回到起始手（主手），慢段尽量用主手，而不是
            //    沿用快段结束时停在的那只手；
            //  - 首个音符 / 新键位段首片保持设置的起始手。
            //  实际速率按事件间隔折算（音符/分钟）：90° 砖是砖 BPM 的 2 倍。
            if (anyNote) {
                double curRate = LocalNoteRate(evTime, nowD);
                if (curRate > 0.0)
                    hand = (curRate > lastSegLimit) ? (-hand) : mainHand;
            }

            // 局部速度（仅用于异常回退；按压时长在生成阶段按 idx 重新取）
            double localSpeed;
            if (speedMuls) {
                int si = (nowD + 1 < eventCount) ? nowD + 1 : nowD;
                localSpeed = speedMuls[si];
            } else {
                localSpeed = speed;
            }

            // 基础片长跟随“实际音符间隔” gapNext，而不是把 floor 半拍量化：
            // 事件网格才是决定换手相位的网格。非 90° 砖 / SetSpeed 组合下，
            // 局部半拍的整数倍与实际音符间隔不整除，量化片长（如 4×半拍=
            // 86ms）会跨过下一个音符（79ms），把单音与紧跟的双押/和弦并到
            // 同一只手，导致换手相位漂移——雪花谱表现为 R2 L1 R1 L3… 而
            // 不是稳定的 R2 L1 R1 L1。
            // 片长 = gapNext × k，k = round(音符速率/(2·阈值))：对 90° 砖
            // （音符间隔 = 局部半拍）与旧公式完全一致，不影响常规谱面。
            double gapNext = 0.0;
            {
                int j = nowD + 1;
                while (j < eventCount && evTime[j] <= evTime[nowD] + kSameMomentEps) j++;
                if (j < eventCount) gapNext = evTime[j] - evTime[nowD];
                if (gapNext <= 1e-9) {   // 末音符：回退到前一个间隔
                    int k2 = nowD - 1;
                    while (k2 >= 0 && evTime[nowD] <= evTime[k2] + kSameMomentEps) k2--;
                    if (k2 >= 0) gapNext = evTime[nowD] - evTime[k2];
                }
            }
            if (gapNext > 1e-9 && lastSegLimit > 1e-9) {
                double noteRateLen = 60.0 / gapNext;
                double kk = floor(noteRateLen / (2.0 * lastSegLimit) + 0.5);
                if (kk < 1.0) kk = 1.0;
                baseLen = gapNext * kk;
            } else {
                baseLen = GetBasePieceLength(bpm, localSpeed, lastSegLimit);
            }

            // 防止死循环
            if (pieces.size() > (size_t)eventCount * 64) break;

            double pLen = baseLen;
            if (pLen < 1e-9) pLen = 1e-9;

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
            if (cnt > 0) anyNote = true;

            nowD += cnt;
            nowT += pieceLen;

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
                // 默认：按分片结构计算，再以“本片自身音符跨度 + 最小内部间隔”
                // 为上限截断——片尾跨暂停/长空拍时不会把整段时间一直按住。
                // pressDurationMode=1：旧版（1.3.0.30）风格，基于八度折叠后的半拍。
                double dur;
                if (g_config.pressDurationMode == 1) {
                    dur = GetNoteFoldedPressLength(evTime, idx, ec.bpmLimit) * ratio;
                } else {
                    dur = CalculateReleaseTime(pStart, cur, next, t, ratio);
                    double span = 0.0, mi = 0.0;
                    if (cur.evCount > 1) {
                        int first = cur.evStart, last = cur.evStart + cur.evCount - 1;
                        span = evTime[last] - evTime[first];
                        mi = evTime[first + 1] - evTime[first];
                        for (int q = first + 1; q < last; q++) {
                            double g = evTime[q + 1] - evTime[q];
                            if (g < mi) mi = g;
                        }
                    } else {
                        mi = GetLocalPressInterval(evTime, idx, cur.pieceLen);
                    }
                    double cap = ratio * (span + mi);
                    if (dur > cap) dur = cap;

                    // 仿人下限：不低于“实际音符间隔折叠基准 × 比例”（约 40~80ms）。
                    // 极快连打时避免短到看不出按键（实测真人约 50ms）。
                    // 注意：用实际音符间隔而不是局部地板 BPM，保证匀速谱面
                    // （含双押/和弦）按压时长一致，不随 SetSpeed 忽长忽短。
                    double floorDur = GetNoteFoldedPressLength(evTime, idx, ec.bpmLimit) * ratio;
                    if (dur < floorDur) dur = floorDur;
                }
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