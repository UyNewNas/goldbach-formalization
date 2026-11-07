# P5.6 → h34：原始 U3/U4 带标签二层键的有限纤维容量账本

2026-11-07。仓库 `UyNewNas/goldbach-formalization`，分支
`chatgpt/p5-h34-request-admission-20261105`。

- 接续远端基线：`c7d163db038d439ed48d12454f9a3af803fe900d`（不是初始入口 0a3fa5a）。
- 本轮数学源码提交：`a5438071cecd9c2eb2e2a793a0f58497c9f2af10`。
- 源码 blob：`632e1b6cbdaa5d41a048bdfdc0ea206762c7e58e`。
- 单个新 Lean 文件：`Part5OriginalH430TaggedRankTwoFibreCapacity.lean`，
  303 行、9 条 theorem 声明、6 个定义。
- 固定手稿：`UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`，
  `paper/source/manuscript-body.tex`，blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`。
- **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**。

## 从上一轮真实停点推进

上一轮 `RankTwoFrontierConverse` 仅证明：
同一物理 Q 下第二层 Rosser 保留 ↔ 真正 `firstExitDepthFrontier 2` 中前缀 [ell,p] 存在，
并得到同前缀的历史**状态值**唯一。这并未证明历史列表位置唯一，更没有把多个 q 的原始算术单位计数支付为历史质量。

本轮避免重复建立抽象准入接口，直接在原始 `originalTagged N` 与
`selectedOriginalRootStage`、`hasRetainedOriginalSecond` 上构造有限源集合 `retainedReceipts`。
每一个真实带标签 `(tag,p,q)` 接收器，只在确有 Rosser-retained 的 q 素因子时
选择一个现存 `ell`，其 `Prime`、`ell ∣ q` 和 `retainedOriginalSecond`
由 `chosen_second_factor_spec` 源码候选证明给出。
这是逻辑选取现存素因子，不是声称 q 本身为素数。

`chosenRankTwoKey` 保留 (U3/U4, p, ell) 三个维度，刻意丢掉仅用于算术接收器的 q，
而且不把 U3 与 U4 在重叠 p 上合并。该键使用现有 `TaggedReceiver` 载体，
但键的第二坐标是 ell，不是 q。

新增稿内候选源码：

1. `key_receipt_has_actual_rank_two_frontier`：
   每个有限键纤维成员都具有原始 q 素因子、原始 N^a 粗糙性窗口、
   真正二层递归状态、正确正号和乘积质量；
   逐标签实际 `originalPhysicalQ` 保持不变。
2. `chosen_key_weighted_partition`：
   对任意加法交换幺半群权重，原始 retained 接收器加权和精确按不同
   (tag,p,ell) 键、再按其各自 q 纤维双重求和；不丢失 q/tag 重复出现。
3. `key_representative_spec`、`representative_mem_key_fibre`、
   `key_fibre_signed_split`：
   每个非空键纤维只选一个源接收器作为纯账本代表，
   其余全部存入显式 `erase representative` 残差。
4. `retained_source_representative_and_surplus` 和
   `retained_source_capacity_card`：
   给出任意带符号原始权重和自然数计数的精确「每键一个代表 + 完整 q 溢出」恒等式。
5. `original_source_with_tagged_key_surplus_and_unpaid`：
   把代表/溢出账本真正接入上一轮**整个原始 U3+U4 五类账本**，
   截止点失败、Rosser 根失败、二层政策拒收、无候选素因子及 q 溢出全都保留。

精确计数的形式是（`R`=真实 retained 接收器集合，`K`=实际标签-根-二层素因子键集合，
`F_k`=对应全部 q 纤维，`r_k`=该纤维一名代表）：

[
\#R = \#K + \sum_{k\in K}\#(F_k\setminus\{r_k\}).
]

这**没有**证明每个 `k` 有一份可用于支付的历史质量：
同一个 (tag,p,ell) 只允许一个账本代表；甚至不同 tag/p 的真实历史状态也
尚未完成跨物理 Q 的全局容量比较，故 **不能** 将右侧 `#K`
直接替换为历史可付款质量或声明 `#K` 全部已付款。

## 验证和范围边界

- 远端已回读数学源码 blob，`c7d163db038d439ed48d12454f9a3af803fe900d` 到 `a5438071cecd9c2eb2e2a793a0f58497c9f2af10` 的 compare
  恰有 1 个新增 source-only 文件、303 行、零删除、零既有文件修改。
- 静态源文本零 `sorry/admit/axiom/unsafe/native_decide`，括号/方括号/花括号计数平衡。
- **尚未 Lean elaboration、编译、kernel replay、传递公理审计、独立审阅，
  numerical430 有限认证亦为 UNEVALUATED**。不安排 CI，不改工具链。
- 没有新 PNT/Mertens/BV 等稿外定理；见 `EXTERNAL_INPUTS.md`。
- 未触碰 P1.4/P3.6、CI、生产模块或固定手稿，也未强推、合并主分支。

## 尚存的稿内义务与下一次真实动作

1. 本轮有限键只处理有 retained 二层素因子的原始接收器；
   **真正 full/selected/inherited 历史 owner、列表位置容量与跨根/跨标签状态碰撞仍未证明**。
   需将每个真实代表位置连接到对应历史状态的列表出现位置，并在无法独立付款时保留差额。
2. `chosenSecondFactor` 是选一保留素因子，不是原稿规定的历史 owner 选择规则。
   必须核对稿内 owner 选取/根权重及相应过滤，不能拿这个纯账本代表代替最终 owner。
3. 根截止点、Rosser 根失败、二层无资格/拒收、non-event 拒收与 q 溢出未支付；
   signed Euler 负历史修正仍不得反向充当正的拒收付款。
4. 实际 z0、lower/upper 阶段、完整原始 U3/U4 selected-count、
   全动作 CLOSED-CELL 与 base/switched/seed/floor、反馈积分—Theta—计数、
   稿内 PP/same-rho、native-history 与共同 430+11 因果细化未闭合。
5. 此 source-only 链须整体进行 Lean 编译、kernel replay、传递公理审计、
   有限认证后才能升级工程验证状态。

下一轮从这个 `(tag,p,ell) → q 纤维` 有限账本追踪实际
`full/selected/inherited` 列表中的一个独立出现位置，
不得用同一历史状态多次支付不同 q，也不得把代表资格当作已支付。

**完整 h34 稿内证明仍未闭合。**
