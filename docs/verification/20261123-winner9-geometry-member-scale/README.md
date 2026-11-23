# Winner9 一阶混合矩、物理几何与完整 Member 尺度

本批续接 `9d82fafcdaa7d0706064d3df94072adf1be28c73`，服务于原 1+1.7482 证明稿。新增验收 **7 个模块、56 条公开定理**：5 个模块在原活动范围内，2 个是必要的稿内辅助模块。其中原顶点数据模块包含 13 个定义、0 条公开定理，计作一个已验模块，不计作 13 条定理。

沿用此前已有收据，累计为 **39 个已验模块、319 条公开定理检查**。另有本批 4 个 Member 组合模块、10 条声明保持仅源码状态。原 **13 个黄色整叶及 23 个汇总父项的合同仍然开放**；本批没有关闭整叶，也没有改动线上看板。

## 源码与准确状态

| 模块 | 公开定理数 | 本批状态 |
|---|---:|---|
| `P2Winner9MixedKOneFiniteCollapse` | 5 | 已编译、独立内核与声明审计通过 |
| `P2Winner9PhysicalVertexInterpolation` | 19 | 已编译、独立内核与声明审计通过 |
| `P2Winner9Row21RawVertexData` | 0 | 已编译、独立内核与声明审计通过 |
| `P2Winner9SelectedRowEdgeGeometry` | 6 | 已编译、独立内核与声明审计通过 |
| `P2Winner9SelectedRowRealJacobian` | 23 | 已编译、独立内核与声明审计通过 |
| `P5OriginalH430CompleteScale` | 2 | 已编译、独立内核与声明审计通过 |
| `P5OriginalH430ResidueWindow` | 1 | 已编译、独立内核与声明审计通过 |
| `Part5OriginalH430AllMarkedPrimitive` | 4 | 仅源码，尚未编译 |
| `Part5OriginalH430CompleteMediumMember` | 2 | 仅源码，尚未编译 |
| `Part5OriginalH430HBMediumRectangles` | 2 | 仅源码，尚未编译 |
| `Part5OriginalH430SelectedHBMedium` | 2 | 仅源码，尚未编译 |

逐模块安装路径、原始字节数、SHA-256、Git blob 和现存源码位置见 [SOURCE_FILES.json](SOURCE_FILES.json)。未修改的原始数据源直接引用原提交，不重复上传。已验源中的历史 `SOURCE ONLY` 注释保留原字节；本表与验收清单给出当前选定字节的状态。四份未编译组合源位于 [源码候选目录](../../source-only/20261123-winner9-geometry-member-scale/ImbalancedChen)。

## 1. 实际积分与原有理一阶候选接通

`P2Winner9MixedKOneFiniteCollapse.actualMixedExpectation_eq_candidate` 对任意原 `SimplexData` 与每个 `j : Fin 10`，证明标准八维单纯形上的实际 Lebesgue 积分比值等于

$$
  \frac{\operatorname{mixedNumerator}(d,j,1)}
  {G\,U\,L^2\,(10\cdot11\cdot12)},\qquad
  G=\sum_{i=0}^8g_i.
$$

分子继续使用原有号偏差和原顶点间隙权重。该实数分式与有理 `momentOneCandidate` 的定义一致；原公开声明直接写展开分式，本批没有另加以 `Rat.cast momentOneCandidate` 为结论的包装定理。

证明先按相等指标的重数插入分解四重阶乘权，再逐个收缩有号有限和，最后用原正分母约分。原 5 个公开定理头、2 个公开定义和导入保持原字节。新增私有引理承担有限和推导，并对私有阶乘字面量补上自然数类型。原大枚举及求和化简的困难归类为可补的推导与形式化实现问题。本步只完成 `k=1`；`k=2,…,6`、实际行尺度与原数值下界仍有后续义务。

## 2. 两个真实种子单纯形的测度几何

物理插值模块使原十个因子、间隙、Y 及有号偏差共用同一个按原顺序排列的九顶点映射。后续三个几何模块把指定有理顶点的原边矩阵、非零行列式、实连续线性等价和真实支撑的 Lebesgue 测度接在一起。

本批验收了两个原行列式/体积等式、体积正性与非退化性；`source_integral`、`source_mixed_integral`、`source_upper_integral` 以及两条具体体积/积分结论使用同一个实边映射。行列式证明复用 Mathlib 的行倍加与行列式展开定理，证明带选主元的有限消元等价，再由内核规约核查两个既定有理等式。它处理零主元及整列为零的情形，保持原矩阵索引及体积常数。原 `Array.get!` 写法改为相同的默认索引语法，原 `8.factorial` 显式标注为自然数阶乘再作同一数域嵌入。公开合同的这些必要语法差异逐项列在 [原范围选源记录](ORIGINAL_GATE_SELECTION.json)，没有加上待证的行列式假设。

原 witness 中的两个单纯形编号为 **21 和 22**，其有序顶点分别为

- `21: [200, 188, 58, 49, 48, 21, 7, 6, 0]`；
- `22: [200, 188, 58, 49, 48, 21, 7, 2, 1]`。

冻结 witness 的 144 个坐标和两个体积已与原字面数据逐项匹配，记录在 [SELECTED_GEOMETRY_WITNESS.json](SELECTED_GEOMETRY_WITNESS.json)。这两个 simplex 编号与稿本账本增量编号 21、22 含义不同。宿主侧的原档案字面比对也不等同于一个 Lean 全档案查找定理。全部 87 个物理记录、每行整数尺度、较高次矩及 floor 仍需各自实例。

## 3. 原弱窗口两侧的尺度补证

两个已验辅助模块从原条件

$$c_0x\le N\le x^{1+\kappa}$$

出发覆盖 `x<N`、`x=N`、`x>N`。证明取 `y=min(x,N)`，仅在内部对 `q_y=log_y N` 使用 `q_y≥1`。原弱窗口直接供应辅助几何界；没有要求调用者另外证明更强的几何下界。回到真实尺度时保持 `x=UV`、原分子 N 和原 `N^(7/32)`，并给出所需四条严格大小条件。组合 Member 源使用稿件实际应用的 `κ≤σ/200`；原抽象命题的 `κ≤σ/100` 范围没有被混称为本批应用范围。

四个未编译组合源进一步连接同一增强 Member、每个活动 HB 组的每条非零有序因子词、原 firstMedium 的真实位置和该词自己的完整补积。两侧 `Forall₂ Owns` 在公开结论中保留位置，因此重复的 dyadic 标签不会抹掉被删除的实际槽。它们也给出两号 displayed 支持上的完整模数 `B*h` 互素性、精确 AP 计数与均值分解；空纤维继续保留均值项。

这些组合源码的具体适用边界和剩余分析义务见 [MEMBER_SCALE_AND_AP.md](MEMBER_SCALE_AND_AP.md)。它们尚未获得编译或内核验收信用。

## 验收、复用与剩余合同

每个成功源只编译一次。独立验收使用同一目标对象，并逐条读取完整类型与公理；公理并集限于 `Classical.choice`、`Quot.sound`、`propext`，没有 `sorryAx`。所有 56 条输出和目标对象身份见 [VERIFICATION_RESULTS.json](VERIFICATION_RESULTS.json)。其中也逐模块记录编译警告数；Jacobian 的四条是两个已被前序战术关闭的目标上留下的冗余 `ring` 警告，不影响内核验收。成功字节保留。这批对象与此前已有对象、数学源均按准确身份复用，没有重跑已成功的相同字节，也没有重跑旧数值生产程序。

两个独立数学审查分别覆盖原一阶矩/物理插值与新的几何链；Member 另有独立审查。详见 [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md)。Member 继承图的一份平滑门旧前像已替换为基线中的已验版本；16 条旧定理不重新编译或重复计为本批成果。六个新 Member 源和其导入图不因此增加任何验收声明。

原验收门槛仍是同一 44 个根与同一 1,664 个名称，最终 `P4AOriginalR17PaidIntegral.original_signed_density_and_count` 仍未验收。稿内所有黄节点继续由既有 [36 份任务合同](../20261123-yellow-leaf-continuation/ALL_YELLOW_TASKS.json) 覆盖，13 个叶项负责人已分配，父项按原完整覆盖关系汇总。本轮具体模型与推理强度登记于 [NODE_PROGRESS.json](NODE_PROGRESS.json)。本批提交不请求远程 CI，也不恢复 proof goal 或计划任务。
