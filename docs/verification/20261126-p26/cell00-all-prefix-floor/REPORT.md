# Cell00 全56行：degree-six prefix moments、Q80与新Q96数值证书

## 已完成范围

本包完成cell00余55行的有限prefix moment/floor证书与全部56行的全称汇总。其中rows001–004在本轮开始前已分别通过normal和独立leanchecker；本轮核对其源码、对象、日志、依赖及原输入hash，未重新编译。rows005–055的51个新合并owner本轮首次通过；row000此前已过的12个owner及全部56行的旧算术证书原样复用。

精确发布白名单为55个`P2OriginalSaving19Cell00RowNNNPrefixFloorChecks`（NNN=001..055）和1个`P2OriginalSaving19Cell00AllPrefixFloorChecks`，共56个模块。本轮首次验收52个模块，既有4个模块只读复用。最终导入闭包共479个项目模块；bootstrap包含424个可复用owner，其中423个在最终汇总闭包内。没有重编这些供应者。

全cell00现在具有3360个degree1–6 prefix moment值等式、560个第一矩编码、560个原保存Q80字段的精确floor绑定和560组显式下界≤/严格上界<。每行保存新Q96仍等于`max(old,new)`，旧Q96的两个原等式继续保留。原九顶点顺序、全部10个因子和全部56行均未省略。

## 全称接口及精确总和

最终命名空间为`ImbalancedChen.P2OriginalSaving19Cell00AllPrefixFloorChecks`。`all_bounded_prefix_floor_checks`和`all_raw_prefix_floor_checks`无成功guard前提地量化所有`Fin 56`，保留原五条floor公式。`all_Q80_bounds`量化`Fin 56 × Fin 10`，同时保留下界与严格上界。`all_gap_encoding`、`all_deviation_encoding`及非零公分母证明汇总原实际数据编码，供独立语义桥调用既有`normalizedMoment_eq_encoded`。

| 已由Lean证明的cell00保存字段总和 | 整数值 |
|---|---:|
| old Q96总和 | 1052519148976369882 |
| new Q96总和 | 1055527309463438251 |
| new减old的replacement增量 | 3008160487068369 |

这些总和只涉及同一56行原字段，增量来自`sum_sub_distrib`，未将旧值与新值相加制造收益。完整有理数分母仍为2^96。

## 验收证据

56个发布owner全部有normal及独立leanchecker成功receipt。每个合并行owner打印122条定理，汇总打印14条，本包共6724条。公理并集仅`propext`、`Classical.choice`、`Quot.sound`。计数不重复包括row000既有包的122条；若合并查看全cell00数值层，行证书加汇总共有6846条打印项。

成功normal累计563.677秒，kernel累计332.708秒；最大采样RSS为2,937,606,144B（约2.736GiB）。每个进程预算固定4GiB、180秒、单线程。本代理保持最多1个Lean/leanchecker进程；父代理另行协调共享机器其他任务。

原normal日志中stderr进度与stdout公理消息可能在一行中穿插；早期runner的单行提取器因而会漏计一条打印。冻结审计只在解析视图中移除`P26_ROW...`进度片段，随后逐个匹配所有源码`#print axioms`目标及完整公理列表。原日志与原receipt未改写。

## 唯一失败与最小修复

所有51个新增逐行owner一次通过，无失败重编。汇总`assemble-v1`在有限分支后的量词目标内未能用`rw`匹配`boundedRowVertex_eq`，最终报错并且无olean。失败快照、命令、日志和receipt完整保留，错误恢复项未被接受。

`assemble-v2`仅将4组汇总proof中的rewriter步骤换为`congrArg`、`congrArg₂`与`Eq.mpr`的显式等式运输。原声明、数值字面量、选择向量、所有原行引用及五项floor公式均未改动；不增加任何假设。最终normal与kernel均通过。修复的精确前后hash在`generation/all_rows_transport_repair.json`。

## 原手稿与尚未闭合的边界

本包依据release-20261106英文numerical-appendix的`num:simplex-moment`（177–196行），仓库`chen-imbalanced-semiprimes` commit `a988cba584d803ae2856a0de50efb582f4f3dd6a`；原文件SHA256为`bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`。稿件给出单纯形单项式积分公式。本包复用既有prefix表示和数据编码，不声称稿件另有新的prefix/Newton估计。

已接受的是concrete decoded cell00上原prefix evaluator的有限数值证书。`bridge-candidate/ImbalancedChen/P2OriginalSaving19Cell00AllOriginalFloorBridge.lean`提供单个全称语义桥候选，逐项调用既有`HigherMomentsPrefix.normalizedMoment_eq_encoded`和Q96 namespace等式，并保留原raw三层lookup的版本；该文件不属于本包已编译闭包。不能从纯数值证书推断原rationalMoment语义桥、Archive aliases、OriginalRowIndex的原FloorChecks、单纯形积分下界、其余12个cell或P2.6端点已经完成。

独立只读源码审查来自`/root/p26_existing_audit`，原文转录在`review/`。其初审对应修复前汇总和未编译语义桥的明确SHA，确认全56行选择顺序、同一分支同一原行、九点顺序、560组Q80界和五合取没有缩弱；静态审查不替代编译验收。修复后的最终源码验收由上述normal/kernel回执承担。

## 交付与复用

`PUBLICATION_SOURCES.json`列出56个已过源码的精确白名单；`PUBLICATION_FILES.json`列出对应源码及证据文件的发布路径。`SOURCE_MANIFEST.json`绑定每个源码、对象、双receipt；`FULL_SOURCE_CLOSURE.json`保留479模块完整导入、源码/对象和原复用验收链；`VALIDATION.json`汇总公理、预算、成功记录与失败记录。

Python Fraction和生成脚本只提出字面量，所有数值结论来自Lean证明。原输入文件前后hash一致。本代理未修改主工作树、未提交或push、未调用云编译、未重标旧P1供应者验收，也未声称P1 strict全owned审计完成。
