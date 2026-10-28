# certificate_floor：同一17572行mask的真实二维积分

本轮交付一个完整的 source-only Lean 文件：`P2HistoricalSavedFloorSelectedUnion.lean`，拟安装为 `ImbalancedChen/P2HistoricalSavedFloorSelectedUnion.lean`。没有编译、Lean/lake调用、大型checker、整数回放或额度查询，formal credit 为0。没有修改生产源码或旧draft。

## 核对结果与实际增量

已核对 `SavedTotal-Witness-Max`、`P2HistoricalSavedFloorRowsBinder` 和现有dependent `Row`。此前 witness 只提议用 `decide +kernel` 求和原始17572个整数；它尚未执行。原始 `rowSourceOutput_eq_components` 明确为 ordinary 输出与正 defect credit 之和。因此整数total相等不能推出 ordinary-only 的积分下界，也不能自动提供Wu-h控制。

进一步核对发现，现有 `P2HistoricalSavedFloorFullBinder` 已经给出每行完整 ordinary + guarded actual-Wu-h 的真实迭代积分下界，以及17572行的总和。其sf、log及parent geometry来自具体历史算法，但真实200-bank endpoint licences、逐行source-output整数等式和单独total等式仍需提供。本文件没有重复这些下界，而补齐下一项必要的几何与积分语义：

\[
\int_{\bigcup_{r:\mathrm{Row}} B_r}
 \bigl(K_{\mathrm{ordinary}}(t,u)+K_{\mathrm{guarded}\ h}(\delta,t,u)\bigr)\,d(t,u)
=\sum_{r:\mathrm{Row}}\mathrm{rowCompleteActualIntegral}(\delta,r).
\]

这里 `B_r` 使用同一原始row的真实网格坐标，取
`Ioc (rowTL r) (rowTR r) ×ˢ Ioc (rowUL r) (rowUR r)`。这是二维discarded-floor pair区域；没有将它混同于extra-gross的四维fiber union。

## 证明主线

1. `pairCell_unique_owner` 使用实际grid的 `tUpper_le_tLower`、`uUpper_le_uLower` 和 `indices_injective` 排除重复归属。半开区间让相邻网格边界也有唯一owner；没有假设行号等于网格编号。
2. ordinary密度在正坐标闭矩形上连续，由紧性给出联合可积，再限制到半开pair cell。实际lower-factor在 `s=2` 处分段的连续性直接复用现有定理。
3. guarded defect的联合可积从 `guardedDefect_joint_integrable` 取得；`indices_bounds` 构造原512网格的 `Fin 512`，`actual_savedParent_residual_bounds` 及已证的残量正性和上端≤5消去全部几何前提。没有新增可积性、Wu-h下界或floor下界假设。
4. `pairCell_setIntegral_eq_nested` 用product-space Fubini识别真正的二维set integral与原有有序interval iterated integral，保留同一密度及归一化。
5. `selectedUnionIntegral_eq_fullCompleteActualIntegral` 用已证pairwise disjoint与逐cell联合可积，应用有限union积分可加性。因此每个原始row恰好使用一次。
6. 最后两个corollary把现有full binder的完整saved-floor下界搬到同一真实union积分，并且只除一次4。它们明确保留原bank licences、17572逐行source检查和独立total检查。

核心union等式只要求 `0 < δ ≤ 1/10`；不要求bank licences、整数total、逐行checker或任何目标实数不等式。这是本轮实质消去的证明义务。

## 精确边界

本文件不声称完整saved整数被ordinary-only积分控制，也不从total相等推导Wu-h控制。它的density就是已有full binder的 ordinary + guarded actual-Wu-h density。

原稿锚点是 `manuscript-body.tex` 1121–1141的literal discarded floors和 `eq:current-literal-loss`，以及1000–1307的same-mask refinement。原稿指出零lower estimator不等于算术count为零；此处没有引入这样的推断。未发现需要上报的新增原稿数学反例或错误。当前未闭合项属于实现/语义绑定边界：

- 编译专员核对新文件和完整source-only import链的语法、elaboration与kernel；本轮只做静态源码审阅。
- 实际ordinary/log producer的17572项 `fullSourceRowCheck`，以及先前独立total witness的执行；本轮不执行大checker。
- 原始200-bank endpoint licences，guarded Wu-h与原稿算术enhanced family的识别，以及same-mask signed算术loss绑定。
- 独立ordinary upper proxy、extra fibre的净gain与最终current c均未在本模块证明。

`REGISTRY.json` 固定本文件、原稿、scope和被审查旧witness的SHA256，并按精确import路径记录146个本地传递依赖的字节hash与实际namespace。它不把磁盘上的source-only文件说成已编译可用。`complete_module=true` 指文件文本闭合；`task_complete=false` 表示完整unconditional certificate语义仍未闭合。
