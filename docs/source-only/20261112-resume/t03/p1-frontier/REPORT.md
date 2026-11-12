# P1 第八层前沿高模数账单

**在 P1 原来的共同参数上，raw 外侧、87 个单元的三类叶代价、licensed 外侧均为零。** 对每个整数截止 `N^(3/5)≤X`，两棵完整策略用同一个 `highQTest X F` 得到的物理值相等，对所有实值测试 `F` 成立。这四份 Lean 源码未执行内核核验。

## 真实来源及模数范围

* 对 `actualRawFrontier` 中每一个八阶状态，原 `actual_eighth_frontier_admissible` 与全第六层的 `raw_currentSixth_le_initial_ceiling` 给八词粗积 `b8<D6≤N^(299/500)`。后继继承同一个八词。无 owner 时，它在该前缀的第六层 `D6` 上继续。有原 owner 时，raw 策略采用 `N^(newCap c t)`。原 `selectedExponent_bounds` 给出 `newCap<153/256<299/500`，包括在原 trim 以外的有 owner 状态。
* 把后继的这个固定层记为 `D`。当前八词在 `D` 已准入时，`ordinary_terminal_admissible` 控制每个真实后继。若八词未准入，要从正号八词作第一次 take，第九查询必须在同一个 `D` 接受完整奇数前缀。新素数严格小于所有已选素数，原 `ordinaryRosserPrefixAdmissible_tail` 随即推出八词已准入。因此这种后缀只能一路 skip，终端积仍等于 `b8`。证明适用于所有真实 raw 八阶状态，无须给第六与第八 cap 加顺序前提。[实际 raw 叶界](P4AOriginalFull87RawFrontierTerminalLevel.lean)
* raw 每个活跃小因子只使用该叶真符号的 `actualSmallRosserPlus_active` 或 `actualSmallRosserMinus_active`。其完整模数严格小于 `N^(epsilon+299/500)`。licensed 侧直接调用 P1 先前发布的 `actual_post8_live_full_modulus_lt_three_fifths`，其中 `delta=width r`、`FilteredSourceSupply s r n e q om` 及其实际载体均保持。对每笔 `leafHighQCharge` 先分 `beta=0` 与 `beta≠0`。后一情况给 `a*b≤X`，随后原绝对账单内的 `|F|` 因其严格截止取零。[两侧的逐叶绝对代价](P4AOriginalFull87FrontierLeafCharge.lean)

这些实际门限对应原稿的后继冻结层和既有有序奇数立方。原稿还要求完整模数幂次在局部乘积尺度上保持余量，并要求小筛层、rough cutoff 与细网格按顺序固定。[编译审计第 200–220 行](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/actual-k-compilation-joint-audit.tex#L200) · [第 327–356 行](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/actual-k-compilation-joint-audit.tex#L327) · [实际分布假设第 38–59 行](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/actual-k-distribution-joint-audit.tex#L38)

## 原账单的每次出现

`pairedCopies` 比较完整状态，保留相同状态重复出现的次数。用它已经发表的带符号恒等式分别测试 `(1_{x=s},0)` 和 `(1_{x=s},1_{x=s})`，得到原 raw 列表中 `s` 的次数等于 matched 次数加 raw-only 次数，原 licensed 列表的次数等于 matched 次数加 licensed-only 次数。所有次数非负，故 matched 状态确实同时出现在两种输入中，两种独有状态各出现在自己的输入中。`tagged_leaf_mem` 进一步沿原 `firstDisagreementLeaves` 的 skip、共同 take 以及首次单侧 take 取回带标签的 retained leaf，原 side tag 和叶子采用的奇偶符号分别读取。[真实两侧成员关系](P4AOriginalFull87FrontierLeafMembership.lean)

这给出了原 raw 外侧、licensed 外侧的每个真实状态，以及每个原单元的 matched、raw-only 和 licensed-only 绝对叶账单逐项为零。整个过程保留 unowned、owned-but-omitted 和 kept 列表的重数。非零项从模数范围排除，在绝对值以前没有用正负抵消。[三项账单与物理差](P4AOriginalFull87FrontierInvoicesZero.lean)

## 可用端点与参数

| 声明 | 结论 |
| --- | --- |
| `raw_frontier_leaf_product_lt`、`raw_live_full_modulus_lt` | 每个实际 raw 八阶后继的粗积 `<N^(299/500)`，活跃完整积 `<N^(epsilon+299/500)`。 |
| `actual_frontier_invoices_zero` | 同 `N,cap,w,z,L,X,F` 上原名三个绝对账单同时为零。这个结论使用原共同 schedule 的实际供给。 |
| `actual_physical_highq_difference_zero` | 调用已发 `a41918df` 的 `physical_highq_le_frontier`，把三项零值代入，导出 `physical R (highQTest X F)−physical S (highQTest X F)=0`。 |
| `exists_shared_physical_highq_zero` | 直接调用 `exists_shared_licensed_sixth_schedule`，先取正 source/box/sixth 误差及其同一组 `s,r,e0`，再 `∀e ∃q0 ∀q≥q0 ∀om≤1/100 ∃n0 ∀n≥n0 ∃m0 ∀m≥m0`。保留三项原遗漏界和 `FilteredSourceSupply`，在这同一次选择上交付所有合法目标与测试的完整差零。 |

目标满足 `1<N`，`w≤N^(53/13824)`，`N^mu≤z≤cap`，`L=N^epsilon`，`0<epsilon≤1/500`，`N^(3/5)≤X`。等号 `epsilon=1/500` 足够使用此处的严格 `X<a*b`。原分布论要求固定 `theta*<3/5` 时，须在 `N` 前取更小的 `epsilon` 并为局部尺度与细盒端点留余量。本包的最终整树等式在显示的 `X` 范围成立，其固定阈值并未自动降低。

完整物理差为零只识别高模数部分两棵树的值。两树共同的单树系数支撑、低模数带符号 PP 与互素均值、sharp 端点、动态 winner 的整盒和余量层外许可、原 archive saving 到各个指定策略的传递仍按其原职责核验。全有序 R17 和最终 finite-dispatch 的既有数值、密度及同系数计数结果均应在各自的原接口消费。P1.4 整体待核验，本包没有新增内核或 PP 完成凭证。[原同系数 PP](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/manuscript-body.tex#L258) · [sharp 推论的实际条件](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/manuscript-body.tex#L743)
