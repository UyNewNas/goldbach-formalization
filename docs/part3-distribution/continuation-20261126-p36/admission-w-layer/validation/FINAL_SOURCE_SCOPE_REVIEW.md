# P3.6 最终源码数学范围复审

**复审结论：通过。** 对照基线 `b3f306cc3b430fc40c3b3ec4110d323443d2f609` 与冻结源码 `8495b3b274a046060faf2ce9020b2588665634c0`，以下四份已有 Lean 源码的修补均保留原假设、系数、支撑和目标不等式。本次只读复审核查这四份差异，未重新审查此前已独立核对的 `P3OriginalU5FullWLayer` 全文。

| 文件 | 核对结果 |
| --- | --- |
| [`P3OriginalU5AllSourceSquares.lean`](../../../../../ImbalancedChen/P3OriginalU5AllSourceSquares.lean) | `rank_four_supply` 中调整了 `simp` 与 `ring` 的执行方式。前缀词之和的等式、接受记录、原来源和实际选中掩码均保持原样。 |
| [`P3OriginalU5RootVInputs.lean`](../../../../../ImbalancedChen/P3OriginalU5RootVInputs.lean) | 换底分别使用 $qA(s)-A(qs)=(q-1)/2$ 和 $qC(s)-C(qs)=57(q-1)/64$。原条件 $1\le q\le1+\kappa$ 使两项损失均不超过 $\kappa$。单个与成对前缀仍通过原 `coordinate_power` 和 `physical_power_eq_local` 精确还原素数乘积。`none` 分支显式使用分情况后得到的自反等式，保留原来的 W 结论。 |
| [`P3OriginalU5CoarseRootV.lean`](../../../../../ImbalancedChen/P3OriginalU5CoarseRootV.lean) | 两个坐标的估计明确分别使用 $x_0=u$、$x_1=t$ 对应区间的上下界。`VariableEnvelope.B a` 就是原始 `level` 定义中 $W=153/256-3a/8$ 的实常量。代表点选 `none` 时，等式仅确定代表点位于 W 层；V 分支仍在整个闭格上保有原余量。 |
| [`P3OriginalU5RoughEndpoints.lean`](../../../../../ImbalancedChen/P3OriginalU5RoughEndpoints.lean) | `actualDwellSupport_upper_inflation` 的基准层显式取同一 `actualTrace` 的 cap，秩取 `roughRank epsilon`。输入是恒等映射下的完整粗词 `t.2 :: t.1 :: chosen`，输出按同一网格的 `upperAt` 取端点。root 来源仍得到 `auxCover − buffer/4` 的端点支撑。 |

**认领范围。** 全来源平方适用于 `P5OriginalU5CausalFinite.rho` 的非零实际项。附着原小因子后，有符号逐词供应保留完整模数词、最后实际来源和该来源的选中掩码。root-V 临界区间使用原来的缓冲与局部尺度 $1<x\le N\le x^{1+\kappa}$。粗词端点定理的秩和端点平方覆盖两枚外标及 `chosen`，小因子的素因子只在独立的完整词声明中附着。闭 W 等值层可以包含 V 优先路由的平局点；完整 W 层划分保留其实际补集。

**后续义务。** `roundedRho` 的同系数准入、全族物理共同 $Q$ 的覆盖与筛选补集支付、实际稿选策略的有符号主项和各稀疏查询的正质量仍须分别证明。高秩 U5/WT 还需要实际族的完整 (S)/(F)、整原子三因子分解及同系数 PP。

**形式验证状态。** 据主控提供的终态，本轮八个 owner 的原始 strict 编译、独立 kernel replay 和完整声明、类型及传递公理 audit 均以退出码 0 完成，状态为 `VERIFIED_OWNED`。上述运行由主控组织；本记录作者仅核对冻结源码的数学范围，未运行编译、重放或云任务。
