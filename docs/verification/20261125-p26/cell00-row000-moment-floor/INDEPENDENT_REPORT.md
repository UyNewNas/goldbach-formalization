# Row0 Q80/new-Q96 候选独立只读审查

审查了 SOURCE_REVIEW.json 固定的四个候选与现有 HigherMomentsPrefix 参数；未编译、未运行数值、未修改候选。未发现实质数学、范围或原数据绑定遗漏。

- Encoding 的九个 gaps 与十组各九个 deviations 用闭合等式绑定实际已通过的 vertices 与 topsOf row；Nat 尺度保留非零义务，不靠 host 生成值或 hash 替代此等式。gapScale/所有 deviationDenominators 参数在 bridge 中顺序正确。
- Factor00 的六个矩等式使用现成 prefixMoment；Q80 等式使用原 factorFloorQ80，两个 floor 边界为整数≤exact·2^80<整数+1，符号和缩放方向正确。此源审查未逐个重读另外九个 factor 的 literal 数值；组合层明确分别引用全部十个已验 owner，数值信用来自其独立 kernel 回执。
- PrefixFloorChecks 保留原五合取：十个 first moments、十个 Q80、两项旧 floor、新字段等于 max(old,new)。总 T 是原十个 Q80 整数之和除以2^80；new evaluator 保持原 cubic correction。旧两项直接复用已通过的实际 moment/geometry 证书。
- OriginalFloorBridge 对现成 normalizedMoment_eq_encoded 的 d/s/k 和 hd/hs/hk 参数顺序准确。gapEvaluator 的 k∈range5 给 k+2≤6，故使用的所有 degree 都在原 theorem 范围内。实际 floor 公式连接没有新增假设，也没有把 lower bound 偷换为精确 floor 等式。
- 原 rationalMoment 和旧 namespace 接头所需对象缺失时，整桥仍明确 SOURCE_ONLY；不得将 prefix 数值证书视为该桥已编译，不得据此声称 Archive 原 aliases、其余 cells、完整分析积分端点已经连接。

这份记录只提供源码语义/接口审查，不替代 normal/kernel 或 P1 strict 验收。
