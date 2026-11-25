# Saving19 RowNumerics：机械抽取与独立行算术接口

## 当前结果

已完成一个新 owner 源码 `P2OriginalSaving19RowNumerics`，以及单独保存的 `Original28918` 接线 overlay。原八项有理坐标声明、`PhysicalQ` 的 Decidable instance 保持原 namespace、名称、类型与定义字节；原 `RowDataChecks` 的十项条件没有删减。新接口只接受真实 Schema 的 `GeometryRow` 和九个有理八维顶点，determinant 规范仍是 `Matrix.det`。

**本地 normal/kernel 验证尚未完成。** 精确本地对象名检索未找到 Q96 三个供应者的 `.olean`；按照 Root 授权仅准备其三源环境时，第一项 `P2PositiveAffineSimplexLogJensen` 在读取 import 阶段即因缺少 `Mathlib.Analysis.Convex.Integral.olean` 停止。运行 0.207 秒，采样峰值 193458176 B，未生成对象。其余两个 setup 供应者及新 owner 未运行。没有扩大预算、重建 Mathlib 或216分析供应者，也没有提交 P1。

因此，此包当前是**经过静态比较的源码候选**，不能称为 locally accepted。完整 Original28918 overlay 也单独保持 source-only 状态。后续若实际运行验证，必须保留本次失败基线，不能覆写为成功。

## 新 owner 与原声明的归属

新文件：`ImbalancedChen/P2OriginalSaving19RowNumerics.lean`。

以下声明从原 `P2OriginalSaving19Original28918.lean` 移入，仍在原 `ImbalancedChen.P2OriginalSaving19Original28918` namespace：

- `QPoint`
- `comparisonQ`、`newQ`、`thirdQ`、`totalQ`、`gapQ`、`factorsQ`
- `PhysicalQ` 及 `instance (t : QPoint) : Decidable (PhysicalQ t)`

`EXTRACTION_MANIFEST.json` 固定每段原 byte offset、长度与 SHA。生成器检查每段在新文件中恰好出现一次。原 `rawVertex` alias、`realPoint`、所有 cast 定理、row-specific 数值函数、`RowDataGuard`、`RowDataChecks`、全称 guard 和后续 analytic 构造全部留在 overlay 中。

新 namespace `ImbalancedChen.P2OriginalSaving19RowNumerics` 定义：

```lean
edgeOf          (v : Fin 9 → QPoint) : Matrix (Fin 8) (Fin 8) ℚ
gapSumOf        (v : Fin 9 → QPoint) : ℚ
massOf          (g : GeometryRow) : ℚ
meansOf         (g : GeometryRow) (j : Fin 10) : ℚ
topsOf          (g : GeometryRow) (j : Fin 10) : ℚ
computedMeanOf  (v : Fin 9 → QPoint) (j : Fin 10) : ℚ
RowDataChecksFor (v : Fin 9 → QPoint) (g : GeometryRow) : Prop
```

这些是普通数据参数，不是最终下界或数据真实性的假设。新 owner 没有声明任何实际 row 的 `RowDataChecksFor` 已成立。

## 十项条件的精确保留

`RowDataChecksFor` 是原 `RowDataChecks` 作以下参数替换后的结果：原 `rawVertex r` 换为 `v`，原 `rawGeometryRow r` 换为 `g`，原 row-specific helper 换为对应的 `...Of` helper。新接口另把 numeral field 形式 `8.factorial` 显式写为 `Nat.factorial 8`，不改其值。静态脚本已断言除这一个明确语法规范化以外整个合取表达式逐字一致，十项分别为：

1. edge matrix determinant 非零；
2. 九点全部满足原完整 `PhysicalQ`；
3. gap 总和严格为正；
4. 原 physical volume 等于 determinant 绝对值除以 8!；
5. 原 mean gap 等于 gap 总和除以 9；
6. 十个原 weighted factor means 等于原公式计算结果；
7. 每个 factor maximum 支配九点值；
8. 每个 factor maximum 在九点中实际取得；
9. 原 Jensen rational 字段等于既有 `oldEvaluator`；
10. 原 geometry Q96 floor 字段等于既有 `oldFloorQ96`。

没有替换保存的 maxima/means/volume，没有删掉 attainment，也没有引入新的 floor、fastDet 或 prefix 实现。fastDet 当前 P1 readiness 仍由 Root 的只读任务另行核查；本 owner 不依赖该 donor。

## 两层接头与尚未接受的边界

新 owner 内含 `rowDataChecksFor_iff_originalForm`。它量化任意索引类型 `R`、两个数据选择器 `rawVertex` / `rawGeometryRow` 和一个 `r : R`；右侧以七个局部 `let` 精确保留原 row-specific 函数，随后是原十项合取。证明项仅为 `Iff.rfl`，既不使用 Archive 成功定理，也不要求某行 guard 为真。该源码尚未由 Lean 验证，本报告不赋予该证明项已接受的信用。

完整 overlay 添加 `rowDataChecksFor_iff_original`，把这个泛型桥实例化到原 `OriginalRowIndex` 与原 getter。除此之外，只增加一个 import 并删除已经迁出的原字节。脚本将新 import 和桥删除后，结果与“原文件只删获准迁出的片段”严格逐字相等。原 `RowDataChecks` 切片 SHA 保持 `1c0825496d7a015008a55dd0e33985429b4cdd319e5fc32fa09ef059ad3db04f`。

**当前生产 Archive `f48ba6e6…` 仍内嵌 Schema 定义。** 新 RowNumerics 导入真正的 ArchiveSchema，故完整 overlay 只能在后续 Schema-based Archive facade 迁移后使用；现在同时导入会遇到重复 FQN。此包没有修改生产 Archive，也没有临时替换或隐藏其声明来伪造一次编译成功。overlay 的后续 source/object 闭包需要重新冻结和独立验收。

原文件中的全称 `original_data_checks`、`original_saved_vertex_values` 仍是原待验证 proof request，不因本次纯定义抽取而获得信用。独立审查指出 numeral field 形式与此前已发现的 factorial 风险同形；Root 随后授权的唯一轻量语法 probe 已实际确认：`#check (8.succ : Nat)` 与 `#check (8.factorial : ℚ)` 均报 `unexpected identifier after decimal point`，而 `#check (Nat.factorial 8 : ℚ)` 正常输出其有理数类型。运行 1.125 秒，峰值 1656520704 B，无对象生成，记录位于 `diagnostics/FactorialSyntax.lean` 和 `logs/factorial-syntax-*`。

因此新版在新接口和泛型桥的两处写明 `Nat.factorial 8`，显式表达原来要用的 8!，不改任何有理比例或条件。原版 source-only 候选与 manifest 留在 `history/row-numerics-v1-source-only/`。完整 overlay 中两处继承的 `8.factorial` 原文仍按批准范围保持；它们是另一个明确的后续 parser 修复点，**不能把这些未 elaborated 的原文字段叫作已有效的 Lean contract**。这里的“十项原义务不变”指原源所表达的数学条件和指定字节，绝非声称旧源码已可编译。后续修复原 overlay 必须另留明确 diff。

## 依赖与本地环境准备

新 owner 的项目源闭包只有 6 项：

- 新 `P2OriginalSaving19RowNumerics`；
- 原样 `ArchiveSchema` 与 `SourceJson`；
- 原样 `P2OriginalLogMomentQ96Checker`、`P2DegreeSixLogGapSoundness`、`P2PositiveAffineSimplexLogJensen`。

`ArchiveSchema` 和 `SourceJson` 的已有精确本地对象从 `archive-schema/objects/` 复制到独立 local 子树，源与 production 对照一致，**没有重编**。本地 Mathlib pin、Lean runtime 与原诊断环境保持一致；所有新运行仍是 4 GiB RSS /180 s /1线程，没有预算增加。

三个 Q96 供应者的原样源码只放在 `local/`，作为获准环境准备输入，不是新的形式化成果或新的待发布版本。首项 setup 失败已保存在 `attempts/setup-jensen-v1/` 与 `logs/normal-setup-jensen-v1-*`。这次失败只说明当前本地缓存缺少对应 Mathlib import，不能推断 P1 中同源对象不可用或原 theorem 有数学问题。

`run_local.py` 从已使用的 `archive-schema/run_check.py` 有界运行模式调整路径而来，只允许新 owner 与这三个 setup 模块；不会覆盖成功对象，不接受任意 module 名，不运行 Lake 或递归重建依赖。该脚本不是 P1 strict 审计器。本轮 compiler 调用只有缺缓存失败的 setup 与 Root 授权的独立 numeral-field 语法 probe；new-owner normal、独立 leanchecker、owned types/axioms 均未执行。

## 实际 cell00 的义务保持开放

本包不读取或重解码 geometry/moment 原件，不提供任何宿主数学数据，也不重复 Root 的 Moment00 shape 工作。

下游必须用真实 `Geometry00Decoding.concreteGeometry00` 的原 row.vertexIds 顺序得到九点，保持实际 row ID 与 MomentRecord 对应。原 cell/row shape、全部 lookup bounds 与 parse/decode 等式将由它们自己的 owner 提供，排除 `!` 和 `getD default` 的 fallback。manuscript agent 正在处理 Geometry00 typed records；Root 正在提供 Moment00 元数据、56行 IDs 与10 floor slots 的 shape 证明。没有用这些进度消息代替最终回执。

原 `FloorChecks` 五项没有在本包中移动或修改。后续仍需原 `HigherMomentsPrefix` 的正式接受，以及实际 gap/deviation 编码和闭合 Q80/Q96 等式；Q80 的上下界或精确 floor 等式均不得降低。原 all13 guards、28,918行数值检查、pulling、积分与端点仍未由本包证明。

## 来源与发布范围

原 `Original28918` 源 SHA：`ed126d258139d3ee671f164852f816255138657a035f74af67a0f610637c24b4`。

新 owner 与 overlay 应分开发布/验收：新 owner 可以先使用当前真实 P1 Schema/Q96 ready 对象进行单 owner 验证；overlay 暂存 docs/candidate 路径，等待 Archive facade 迁移，不能立即覆盖生产 Original28918 后宣称已编译。`PUBLICATION_FILES.json` 只列新 owner、source-only overlay、脚本与本轮必要记录；local 对象不作源码交付。

此次是 release-20261106 原有 exact rational calculation 的必要模块表示调整。数学范围与稿件定位沿用 `row-arithmetic-interface-review/` 的只读报告；没有扩张到新估计、全覆盖或稿外结论。
