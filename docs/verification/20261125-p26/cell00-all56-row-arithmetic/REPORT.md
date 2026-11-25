# Cell00 全部 56 行：精确原始 row arithmetic

## 结论与实际数据绑定

最终 owner `P2OriginalSaving19Cell00AllRowArithmetic` 已通过本地 normal 和独立
leanchecker。四个无假设定理在 namespace
`ImbalancedChen.P2OriginalSaving19Cell00AllRowArithmetic`：

- `all_bounded_row_data_checks`：对全部 `r : Fin 56`，原有界实际 vertices/row
  满足完整十项 `RowNumericsPure.RowDataChecksFor`。
- `all_raw_row_data_checks`：同一个结果接回 `concreteGeometry00` 原数组和原 row
  vertexIds 的三级索引公式；用已过的无 fallback 等式，不假设默认值正确。
- `all_moment_old_matches_geometry`：每条原 moment 的旧 Q96 字段等于对应实际
  geometry row 的 Jensen floor。
- `all_moment_old_eq_evaluator`：每条旧 moment floor 等于原公式的精确
  `oldFloorQ96 (massOf (boundedRow r)) (meansOf (boundedRow r))`。

全部十项包括 56 个非零 Matrix.det 与体积/8!等式，504 个按原行顺序选取的
PhysicalQ 点，56 个正 gap 总和及 meanGap，560 个 weighted means，5040 个
maxima domination，560 个 maxima attainment，56 个精确 Jensen 有理数和旧 Q96。
这里的点出现次数不是不同顶点数量；实际 cell00 的 28 个顶点未被增删或重排。

## 表示与来源

row0 和轻量 pure helpers 使用已冻结的上一包，无重新编译。新 row1–55 每行一个
owner，原先各个小 proof 保留为 21 个独立声明，统一放进一个模块以免反复载入相同
环境。每行引用其已 decoded 的 `geometryRowsTypedNNN` 和原 `vertexIds` 所指的
原 typed vertex 数组；生成器只机械摘录 index，不运行 host 数学预检查。
两条闭合 rfl/FinCases 等式绑定真正的 boundedRow/boundedRowVertex。全数值检查
仍用原 Rat/Int 运算和 `decide +kernel`；行列式只借既有 fastDet 原 proof 改写回
同一个 Matrix.det 规范。最后 owner 仅组合不透明已过定理，不重跑任何 row 判断。

Pure 命名空间的 13 个 Q96 定义、fastDet 原算法/proof、完整十合取来源和独立
审查都在 row0 基包固定。它们保留原公式的泛型量词与 rounding 方向。
旧 Q96/Consumer/Core 分析对象未更换；接回旧命名空间的 rfl/Iff.rfl bridge
不在本轮接受范围。原稿依据与有限代数表示界限沿用基包记录，没有新的分析估计。

## 验证和逐批冻结

新 55 个 row owner 加最终 assembly 共 56 个新 owner、112 次成功调用。
其余 353 个已通过 source/object 逐字复用，最终项目闭包 409 个 owner，canonical：
`5ca17e875cbb80d11d04839e57840e1838a6f468d48b4a2508eea7340c16a410`。

每调用固定 4 GiB RSS、180 秒、1 线程；Lean 4.33.0-rc1 / commit
62eed1db4d67327ec8120be05f1a1b0847d74561，Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1。累计成功 normal 382.297s、
独立 kernel 269.040s；normal 峰值 2819223552 B，kernel 峰值 2418208768 B。
本轮失败 0 次。全部 1159 个打印的依赖集合
仅含标准 propext、Classical.choice、Quot.sound，无新 axiom 或成功占位。

| 新行范围 | owner数 | normal 秒 | kernel 秒 | 最高 RSS B |
|---|---:|---:|---:|---:|
| [1, 7] | 7 | 43.902 | 33.475 | 2819182592 |
| [8, 15] | 8 | 50.831 | 36.795 | 2818899968 |
| [16, 23] | 8 | 52.082 | 36.792 | 2819207168 |
| [24, 31] | 8 | 58.168 | 41.480 | 2819223552 |
| [32, 39] | 8 | 58.883 | 40.355 | 2818994176 |
| [40, 47] | 8 | 56.356 | 39.192 | 2818830336 |
| [48, 55] | 8 | 58.420 | 37.727 | 2817601536 |

每批 checkpoint 固定其源、normal/kernel 回执和无对象 delta whitelist；任何
已通过行、原 row0 或纯 helper 都没有重新编译。原 fixture、所有复用 source/object
以及每次目标的 source/object 前后指纹均在回执中核对。剩余边界在 RESULT 中列明。

## 未声明完成的义务

这是 cell00 全部 row arithmetic 和旧 moment floor 第 3、4 项，不是完整
FloorChecks。十个 Q80、原 degree≤6 rationalMoment 对应以及新 Q96 的
`max old new` 仍由独立任务处理。未声称其它 12 cell、28918 行全局和、
Archive/Core aliases、pulling/ownership、实际积分端点或 P1 strict 已完成。
本轮没有发现实际数据的算术反例；原余下证明义务保持原样，不用新假设覆盖。
