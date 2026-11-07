# P5.6 → h34：实际 rank-two frontier 逆向与固定前缀状态唯一性

2026-11-07；仓库 `UyNewNas/goldbach-formalization`；工作分支 `chatgpt/p5-h34-request-admission-20261105`。
接续远端 HEAD：`21040641c0c9d4044850a791eaa95a3004dd5ae4`。数学源码提交：`9f269ad9f761ee9e775d2b909c4a21ffb3abcb77`。
源码 blob：`d35c1f5cee2edcabbb0751020d47bbaf3e54d754`。
**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**

手稿固定为 `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`，
`paper/source/manuscript-body.tex`，blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`。
原 c/K、root norm 7/2、row norm 12、alpha、同 Q、闭结点、指定单元/scalar 差异均不改变。

## 实质增量

新增 `Part5OriginalH430RankTwoFrontierConverse.lean`（258 行 Lean 源码，
4 条公开候选定理和 2 条 private 归纳辅助证明）。

此前 `ActualRankTwoFrontierSupport` 只将原始 q 的 Rosser-retained 二层素因子
单向提升为实际 `firstExitDepthFrontier 2` 成员。本轮直接对原本的
skip/select 递归做反向归纳，不依赖额外 frontier-to-owner 公理：

- `one_step_frontier_is_next`：在此前缀长度恰比目标 rank 少 1 时，
  将实际 frontier 成员逆推出经过 policy 检验的原始下一个候选；
  同时处理跳过当前素数及策略失败的分支。
- `two_step_frontier_is_two_nexts`：从空前缀、初始正号、质量 1 的真实递归，
  抽出同一物理 Q 下两次通过 Rosser 策略的真实枚举候选。
- `actual_rank_two_frontier_implies_retained_original_second`：若
  实际二层 frontier 状态的有序前缀恰为 `[ell,arithmeticPrime z]`，
  则其两级枚举与策略检测构成真正的 `retainedOriginalSecond`。
- `retained_original_second_iff_actual_rank_two`：
  由上述逆向及上轮单向支持组成精确的历史保留 ↔ 实际二层 frontier
  对应（对象是“历史准入/存在性”，不是 q 付款）。
- `actual_frontier_state_determined_by_prefix`：对正 rank、固定根载体与
  同一物理 policy，任意两个成员的有序 selectedPrefix 相同便是同一个
  完整状态值；证明复用真实正负号奇偶、历史质量乘积及剩余严格素数后缀。
- `retained_original_second_unique_frontier_state`：
  经保留的 [ell,p] 对应唯一的二层**状态值**（`∃!`）。

## 明确未完成的稿内边界

“唯一状态值”并非“列表位置只出现一次”，更不是不同 q/tag 可重复领取
该历史权重的所有权。原始整数 q 并未被假定为素数；
逆向 frontier 本身不推出 ell|q、原始 q 粗糙性或完整 U3/U4 count 付款。
同 (tag,p,ell) 可能服务多个原始 q；不同 U3/U4 tag 可能有不同物理 Q。
不生成针对某个 q 的特殊历史状态，也不把 signed Euler 负修正当成正付款。

稿内仍黄：full/selected/inherited 实际 owner、原始 (tag,p,q) 完整
selected-count 及根计数权重、list-position/多 q/tag 容量、
真实 z0/lower/upper、截止点/策略失败/无素因子/非事件拒收、
signed Euler 定向支付、全部动作 CLOSED-CELL 归纳、
base/switched/seed/floor、反馈积分—Theta—计数对应、
稿内 PP/same-rho、native-history 和 430+11 共同嵌套因果细化。

## 验证与下一动作

已经提交独立 source-only 文件并按远端 blob SHA 回读；
仅进行了静态禁用占位符扫描和括号计数检查。
**没有 Lean elaboration、编译、kernel replay、传递公理审计、
finite/numerical430 认证，也没有启动 CI**。有限认证为 UNEVALUATED，
不产生绿节点与形式化验收信用。没有改 P1.4/P3.6、生产模块、
工具链、手稿或 CI 设置，也没有新增稿外数论输入。

下一轮：从本次“真实 frontier 双向准入 + 同前缀唯一状态值”出发，
建立真实原始 (tag,p,q,ell) 关联的有限入射计数与去重/容量支付，
并贯穿 full/selected/inherited，不能重复消耗同一状态质量；
不能匹配者必须留作显式未付款项。

**完整h34稿内证明仍未闭合。**
