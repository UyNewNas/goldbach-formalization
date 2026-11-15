# P1 savingMiddle：实际第八层两支终端的 selected 支撑

结论：本轮只新增一个可由原稿补齐的有限支撑候选 `P1OriginalOwnedEighthSelectedSupport.actual_before_after_selected_support`。它属于**原稿省略推导的形式化接线**，不是新的分析假设。旧 `savingMiddle`、`comparisonMiddle`、P1.4 / Y07 / Y08 仍未闭合。

候选文件 10422 bytes，SHA256 `f06293d6190e5d29594b79501c30b7633b7e30b5618e1bc9d22d703c4f7a3305`，计算 Git blob `22e2272a341115aa51d563435b9e8df2c2ba35bd`。**未运行 Lean、Lake、LSP、candidate 或项目 helper；没有 elaboration/kernel/closure 验收。**

## 所选的最小未付结论

旧 `P1Original87SharpMiddleReserve.savingMiddle` 使用原 sixth-predecessor-minus-eighth 的 `full87PhysicalRhoChange`。已有 signed-normal-form 和 owned-source 恒等式将它定位到实际 `states` 中的 `beforeLeaves`、`afterLeaves`；本轮不重复这些等式，也不重新给一个“假设已知 middle 估计”的包装。

对其中任一实际 state 与任一侧的终端 leaf，令 P 为该 state 自己第六祖先的 `actualParent`，M 为 `finiteCap n c (point8 N state.selectedPrefix)`，I 为原 `selected c`。每个 Cell 的 mask 保持原样，不能统一替换成 mask138。

新候选恢复真实八素数 tuple p 和 `tail <+ state.remaining`，给出以下三项原像与支撑：

```text
leaf.selected.reverse = List.ofFn p ++ tail
actualDwellSupport (N^M) leaf.selected.reverse
actualDwellSupport (N^M / product(selected I p)) (selected Iᶜ p ++ tail)
```

同时返回原固定缓冲：

```text
M + width n < v (∑ i ∈ I, log_N (p i))
M + width n < 153/256
```

这是完整尾部的平方许可，强于仅给第八前缀或全局 N^0.599 的粗支撑；它仍不是整盒卷积展开。

## 为什么不是新增目标形前提

候选的 `FilteredSourceSupply` 是已有 `exists_shared_licensed_eighth_kernel_schedule` 的真实输出，其完整原类型在既有源中量化所有 N、真实素数 tuple 与原 owner trim。候选没有增加 `hOwner`、`hSupport`、`hParent`、desired W 或 PP 估计字段。

实际证明链为：

1. 对 `states` 原 filter 取出同一个 frontier 与 owner trim；用已有 `actual_rank_eight_state_canonical` 恢复原前缀、素性和 (
eg p_imid N)。
2. 真实第六层的 `actual_rank_eight_admissible` 给入站完整 upper Rosser 准入；`actualParent_residual` 与 `finiteCap_licensed` 给 P ≤ comparison < M。
3. 旧支先在 P 传播 ordinary 准入，再将**准入谓词**提高到 M；新支从同一入站历史在 M 传播。这里没有声称 signed saving 随 cap 单调。
4. 原 retained-leaf 递归恢复完整 tail，不把终端深度替成 8，不去重 occurrence。由原 decreasing prime carrier 和公开 `upper_set_dwell_support` 得完整平方支撑。
5. 直接复用已有任意 arity 的 `P4AFinitePPSelectedPrefixSquares.complete`。其两项实质输入——完整支撑及每个原 complement slot 的平方门——都在本候选内由真实源产生。

该通用 `complete` 的文件虽位于 `lower_pp`，调用类型只有 list、mask、实际素数坐标及平方不等式。没有使用 lower ALL16 的系数、`jointPresievedSigma` 或分布定理，因而没有把 lower ALL16 偷换成 upper 系数。

## 原实例与参数顺序

`s,r,n,e,q,om`、原 supplier 和 `4*width n<width r` 均在 N 前固定。有限 cap 的值仍由原函数读取；证明不重选 parent、owner、cap 字母表或历史。N 是坐标、目标删素及两个 ordinary level 的同一个 N。

`cap` 是原枚举 cap，定理对其任意取值成立，包含 `cap=2*N`；这里没有把物理目标改成 2N。该支撑引理没有外层 W、HB chart、K、kappa 或 sigma 参数，也未建立其统一阈值。后续若转到 singleton HB，仍须保留原 `PP 1 (2*N) N`、原 W、同 chart cutoff，并按原先 K/kappa 在 N0 前的顺序另行接线。

候选仅覆盖 saving 的 owned changed leaves。它不覆盖 `comparisonMiddle` 中全部 raw-minus-licensed 历史，更不认同最终矩形 `Params.rho` 与本历史 Δρ。

## 已有工作与去重

- `1006a047bd5dea9ebad05478b806e6232ec6b96b` 的 actual-parent residual-gap 源已读；它已经给精确残差差及双侧 invoice，没有给本终端 selected-complement 结论。本轮不重写它。
- `142dbf79667690b1006f9ff3729eaf16ee2d87c0` 所含 all-eighth-frontier-terminal 与所选 a023 源同 blob `dc21bd25...`。其真实 arbitrary-state canonical 恢复直接复用；其终端结论为 N^(299/500) 粗乘积。
- 旧 selected-canonical terminal 已在证明内部产生 ordinary admission；本候选复用其公开基础定理，补出对两侧、全部后续叶子可用的 full/selected D-well 输出。没有重新建立历史供应或遍历旧表。
- `71b47b3` 的 `P4AFinitePPSelectedPrefixSquares.complete` 已实现一般任意 arity 的 selected append 算术；本轮只调用。
- 隐藏 source-review 的定向搜索找到旧 `OriginalFourthPhysicalOwnedModulusSupport` 及其相同快照；它是 `producerPolicy4` 的 rank-four 合同，不含 owned87 两支 selected-complement 结论。另一个更宽的 `beforeLeaves/actualFrozenPost8Level` 文本扫描已中止，未据其无输出宣称全库不存在。

旧 `P4AFull87UnionMediumSupportObstruction` 的反例针对旧全量 union 系数，见其真实 `paid_union_nonzero_above_cap`。它使用原第三历史未激活的高 rank 支撑；不是本 saving 差的反例。本候选直接保留 active owned eighth 的 M + width n < 153/256，不会以换成 corrected fallback 系数来绕过该区别。

## 仍未付的最前一项

详见 `REMAINING_INTERFACE.md`。目前不能从逐实际 tuple 的平方许可直接推出：同一个原历史系数在整盒上是独立三因子卷积、其历史标签能作为盒标量取出，以及原系数到 boxed 系数的差在**带符号素数误差**上已支付。

已有 `fibre_scalar` 要求整个 tag+fine-word 相同；`original_factorial` 仍把 coefficient 留在 prime-tuple 和式内。已有 compiler 的 density/mean-scale 费用，也不是这个原 Δρ 的 signed-error 付款证明。完成这些接线后，仍需真实 `RestrictedMediumObligation` 的适用输入及分析结论；当前源中的该名字是定义，不是已付定理。

因此本轮将“真实 descendant 平方支撑”从未接接口推进到一个明确原稿内候选，把后续问题定位到同系数整盒构造及实际 restricted-medium 供应。它没有把整个 savingMiddle 判成一个纯语法问题，也没有给出该估计为假的结论。

`SOURCE_PINS.json` 固定 5 个直接 import、15 个关键或边界源及手稿当前字节；所有 20 个 Lean 来源的 tree/blob 身份已核对。此表不是递归闭包。旧 22 源审计、三选本、WSelected 七源、Sharp postimage 及所有既有 freeze 均未改动。历史 R22 kernel pass 不受本候选“未编译”标签影响。
