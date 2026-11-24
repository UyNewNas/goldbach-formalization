# P2 Winner9 证明与核验

本轮基于 `e29498fabe378f2346380fa094954855e648cd89`，使用固定 Lean `v4.33.0-rc1` 和 Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。有限算术阶段的六个模块均通过严格编译、独立 `leanchecker` 重放和全部归属声明审计。

| 模块 | 已验证的结论 | 审计声明 |
| --- | --- | ---: |
| `P2Winner9FiniteMomentKernel` | 四个坐标的总次数、15 个等号分划的阶乘权重、有号加权和及一次卷积 | 70 |
| `P2Winner9HomogeneousRecurrence` | 任意界内次数的系数表等于原有限和。`homogeneousFast_eq_source` 适用于全部九元组和次数 | 22 |
| `P2Winner9MomentNormalization` | 将阶乘比例和原顶点的有号整数尺度化为证书分母 `G·U·L²·10·11·12` | 3 |
| `P2Winner9Row21RawVertexData` | 原第 21 行的坐标、标签及有理数据声明 | 16 |
| `P2Winner9Row21Arithmetic` | 从原数据重建均值、有号偏差与 Jensen 值，绑定次数 0 到 10 的系数，并验证 Q80 和 Q96 下取整 | 81 |
| `P2Winner9SelectedRowEdgeGeometry` | 第 21、22 行边矩阵的绝对行列式、保存体积和非退化性 | 427 |

第 21 行的两个原记录分别为 `16007085917676593648460` 和 `33473824252327663860`。证明在 Lean 内核中检查完整的整数交叉乘不等式。

[第 21 行原公式接线](row21-source-bridge/ImbalancedChen/P2Winner9Row21SourceBridge.lean) 把同一两次下取整代回原 `T10` 和十个有号曲率项。`total_numerator_denominator_eq` 比较未约分的分子与分母，`row21_raw_arithmetic_lower` 得到 Q96 值除以 `2^96` 后的有理下界。接线模块在归档的两份窄导入依赖中通过严格编译、内核重放和 56 条归属声明审计。两份依赖保留原数值定义，较大的组装模块末尾使用直接的不等式证明。

619 条审计记录只依赖 `propext`、`Classical.choice` 和 `Quot.sound`，且序列化清单与实际模块声明清单逐项一致。源码、对象哈希和各模块公理并集见 [VERIFICATION_RESULTS.json](VERIFICATION_RESULTS.json)。四条有限矩定理的类型及公理输出见 [finite-moment-axioms.log](finite-moment-axioms.log)。

## 第 21、22 行的实际积分

同版 Mathlib 已从固定源码构建。实际 Lebesgue 一阶混合矩、实数仿射像和 Jacobian 已通过编译和独立内核重放。第 21、22 行的 144 个有理坐标也已对照原始有序顶点表完成内核核验。[顶点与仿射映射接线](../../../ImbalancedChen/P2Winner9SelectedVertexBinding.lean)

对任意次数，单纯形上的实际带符号混合矩等于原证书的阶乘系数。有号偏差在展开中保持为整数。(T_{10}) 比较使用实际 gap 概率测度下的幂矩及 Jensen 差。Q6 的 70 个横向项在精确求和后作 Q80 下取整，再乘实际 Jensen 因子并作 Q96 下取整。[混合矩接线](../../../ImbalancedChen/P2Winner9MixedPowerSource.lean) · [物理行 (T_{10})](../../../ImbalancedChen/P2Winner9SelectedRowT10.lean)

以下整数均除以 \(2^{96}\)，给出同一原始物理密度在各支撑上的积分下界。

| 支撑 | 原曲率下界分子 | 原 Q6 下界分子 |
| --- | ---: | ---: |
| 第 21 行 | 33473824252327663860 | 33553775924834770601 |
| 第 22 行 | 6447903780770652011 | 6463231997558714529 |
| 两行支撑的并集 | 39921728033098315871 | 40017007922393485130 |

两行交叠落在一个 Lebesgue 零测仿射超平面内，故真实并集积分等于两行积分之和。[原曲率积分下界](../../../ImbalancedChen/P2Winner9SelectedRowCurvatureFloor.lean) · [原 Q6 积分下界](../../../ImbalancedChen/P2Winner9SelectedRowQ6Floor.lean) · [并集 Q6 下界](../../../ImbalancedChen/P2Winner9SelectedRowQ6Union.lean)

第一个原始数据块采用 16 段各 16 行的声明以控制 Lean 展开深度。逐行比对确认 256 条记录的字段和值及原顺序一致。档案接线在 Lean 中核验第 21、22 行的原始编号、顶点查表、均值和 `mixedSelected`，并直接证明对应支撑上的积分下界。[原档案接线](../../../ImbalancedChen/P2Winner9SelectedRowArchiveBinding.lean)

原始顶点表的 201 个索引均已核验 gap 非负、两个原始上界及十个因子的统一正下界。仿射插值将这组界延伸到由原表顶点构成的物理单纯形。[全表顶点界](../../../ImbalancedChen/P2Winner9SeedVertexAnalyticGuards.lean)

已证明从有理顶点及保存的 Jensen 因子构造整数尺度，并用可执行的有理公式计算幂矩、混合矩、(T_{10})、Q6 和一阶仿射矩。等式与原多项式求积形式相容，适用于满足顶点尺度条件的每一行。[整数尺度构造](../../../ImbalancedChen/P2Winner9RationalSimplexCaps.lean) · [精确矩公式](../../../ImbalancedChen/P2Winner9FastMomentDecoder.lean) · [一阶矩公式](../../../ImbalancedChen/P2Winner9RawFirstMomentDecoder.lean)

本次实际积分和全族预备工作的 43 个模块均通过严格编译、独立 `leanchecker` 重放和归属声明审计。973 条审计记录使用的公理限于 `propext`、`Classical.choice` 和 `Quot.sound`。逐模块源码和对象哈希见 `physical_closure` 字段。[验证记录](VERIFICATION_RESULTS.json)

```bash
lake build ImbalancedChen.P2Winner9SelectedRowQ6Union
lake env lean -t0 -DwarningAsError=true ImbalancedChen/P2Winner9SelectedRowQ6Union.lean
lake env leanchecker --verbose ImbalancedChen.P2Winner9SelectedRowQ6Union
```

完整 Winner9 仍需核验全部 11,026 个原始行的精确见证、支撑合法性及零测交叠，并将整族下界接入 P2 原 87 个积分终端。

## 2026-11-24 全族核验与终端 41

原档案的 11,026 条记录已逐字保留为 44 个 Lean 数据块，每页最多 16 行。生成器检查原档案的连续行号、记录格式及生成源码的一致性。每页的 Lean 证明核对行号、顶点索引、字段长度、历史最大值及 `curvatureRaw ≤ mixedRaw`，逐块证明使用同一索引规则拼接。[生成器](../../../verification/part2/materialize_winner9_blocks.py) · [拼接定理](../../../ImbalancedChen/P2Winner9SeedArchiveChecks.lean)

现在两条解析分支都适用于任意一行。统一行检查器读取实际顶点、存档均值与 Jensen 因子，按档案比较选择对数或 Q6 分支，再将经过核验的原始选定值转为同一单纯形上的物理积分下界。原始第 0 行的对数胜出证明给出 (1441053650834557285472/2^{96})。原始第 22 行已通过通用 Q6 检查。[统一行检查器](../../../ImbalancedChen/P2Winner9SelectedArchiveChecker.lean) · [第 0 行定理](../../../ImbalancedChen/P2Winner9RowZeroLog.lean)

Lean 对原始 201 个顶点逐一核验了全部 97 条编号门条件，并证明相应的原始门墙为 Lebesgue 零测集。终端 41 的 97 个字面门按原顺序逐项对照，原始密度表达式也已对齐。第 21、22 行的 (40017007922393485130/2^{96}) 下界已接到该终端的真实积分。[门条件](../../../ImbalancedChen/P2Winner9OriginalSourceGates.lean) · [终端定义](../../../ImbalancedChen/P2Winner9OriginalTerminal.lean) · [终端积分下界](../../../ImbalancedChen/P2Winner9ArchiveIntegral.lean)

原 Q6 精确求值保留全部带号项，按有理加法约分。检查器证明约分后的值等于原精确式，并保留 Q80、Q96 两次取整的验证。逐行比较器还保留十个对数项的有理下界验证。[精确约分](../../../ImbalancedChen/P2Winner9ReducedExactAssembly.lean) · [行算术](../../../ImbalancedChen/P2Winner9RowArithmeticChecker.lean)

11,026 个原始行的索引与字段拼接已通过严格编译和内核重放。第 0、1、2、3、21、22 行的选定数值证书已合并到终端 41，并以 Lean 严格编译、`leanchecker` 重放和公理审计核验下界 \(3793646749864309049480/2^{96}\)。[完整档案索引](../../../ImbalancedChen/P2Winner9CompleteSeedData.lean) · [终端 41 六行下界](../../../ImbalancedChen/P2Winner9Terminal41SixRows.lean)

整族数值核验、跨块支撑交叠及接入 P2 的 87 个原积分终端仍待完成。整族选定值的汇总草稿及其终端接线保存在 `docs/source-only`。当前构建在汇总证明的 Lean 递归深度处停止，终端接线也依赖整族行检查及零测交叠。[汇总草稿](../../source-only/20261124-p2-winner9/ImbalancedChen/P2Winner9LedgerBridge.lean) · [终端接线草稿](../../source-only/20261124-p2-winner9/ImbalancedChen/P2Winner9CompleteSeedTerminal.lean)

## 20261124 续作

新一轮已严格编译完整几何接口、44 个见证数据块及首末块检查；其余几何行、整族数值分页、账本修复和闭合终端仍待验收。完整记录、源码哈希、实际失败及云端 retained-job 上限见 [20261124 续作记录](../20261124-p2-winner9-continuation/README.md)。本段不改变上面的六行已验收下界，也不将完整 P2 标为完成。
