# R01：原 Winner9 实际矩与物理仿射换元

本批 11 个原活动模块、111 条公开定理全部通过本地编译、独立内核验收、完整公开类型与传递公理检查。原数值附录要求的测度始终是实际 Lebesgue 测度。原函数、积分域、行列式与物理顶点定义保留。

| 模块 | 公开定理数 | 主要结论 |
| --- | ---: | --- |
| P2AffineSimplexMomentLaw | 35 | 三维四面体任意自然指数矩、中心矩及有限维仿射积分换元 |
| P2Winner9NestedEightSimplexMoment | 2 | 原嵌套 beta 积分的八维阶乘公式 |
| P2Winner9SimplexCoordinateSlice | 12 | 标准单纯形真实切片及坐标变换的体积保持 |
| P2Winner9ActualEightSimplexMoment | 3 | 实际 Lebesgue 积分等于嵌套积分，得到全部自然指数的八维阶乘矩 |
| P2Winner9CurvatureExactMomentFloor | 5 | 在原精确整数比较条件下给 Q80/Q96 定向舍入语义 |
| P2Winner9CurvatureFullExactAssembly | 6 | 原 T10 与 curvature 的精确有理组装 |
| P2Winner9MixedDegreeSixExactAssembly | 6 | 原 70 个带符号项的 T10+Q6 及舍入语义 |
| P2Winner9MixedZeroCoefficientCurvatureLink | 8 | 原零次混合项、curvature 与 chronological increment 的精确连接；原字节通过 |
| P2Winner9MixedDegreeOnePolynomialMoment | 4 | 一次项的有理卷积和候选分数归一 |
| P2Winner9BarycentricMixedDegreeOne | 12 | 实际一阶带符号混合期望等于显式有限阶乘和 |
| P2Winner9PhysicalAffineTransfer | 18 | 八维物理仿射像的积分、体积、gap mass 与混合比率搬运 |
| 合计 | **111** | 11 个原模块 |

## 修复内容

常见失败是导数与积分 API 的点值形式、有限求和下标归一化、函数应用展开，以及宽泛化简将 70 项有理表达式透明展开到心跳上限。修复使用原表达式的专门恒等式，并将通用有理舍入引理先证明后特化。成功字节和已有对象不重复编译。

实际三维积测度的 Haar 实例由 Mathlib 的产品测度实例构造，测度仍为原 `volume`。实际八维矩经闭域可积性、保测度坐标拆分、Fubini 和零维积测度的 Dirac 表述得到。

十个模块有源修复，MixedZero 唯一以原字节通过。公开头的字节差异仅有以下几种：

- Affine 两个入口把原未限定的 `IsAddHaarMeasure` 明确为 `Measure.IsAddHaarMeasure`。
- Barycentric 四个入口将 `9.factorial` 明确为自然数阶乘；最后一个有限和公式补齐原未配平括号，表达带符号系数乘阶乘比例。
- Physical 三个入口将 `8.factorial` 或 `9.factorial` 明确为自然数阶乘。

这些差异逐项保留在源选说明中，其余公开头保持原样。全部定义体、变量上下文、原项目导入图保持原义与原字节。Barycentric 的 11 个定义、Physical 的 21 个定义或缩写均未改变。

## 验收边界

实际八维体积为 `1/8!`，物理像体积为 `|det L|/8!`。带权比率中的 Jacobian 在原假设下相消。`SimplexData` 的 Jensen 分子允许为零，相关证明只需该因子非负及分母严格正，不能从数据结构推出严格正性。

实际一阶阶乘和与有理 `momentOneCandidate` 现在分别有已验端点；二者的最后相等仍是原 `P2Winner9MixedKOneFiniteCollapse.actualMixedExpectation_eq_candidate` 的未验义务。高阶混合解释、`P2Winner9PhysicalVertexInterpolation` 的实际函数插值、所选行的 `selectedVertexMatch`、具体 edge 数据和原行下界亦保留。

本批没有把通用物理换元当成原 87 个物理行的验收，也没有得到完整 1,664 项原门或最终 signed density/count 结论。十个实改源的反向可达并集为 222 项，与原 729 个旧对象候选集合没有交集；原仿射单一源的反向可达为 216 项。

准确源码、对象哈希和全部声明的完整类型、公理见 [SOURCE_FILES.json](SOURCE_FILES.json) 与 [VERIFICATION_RESULTS.json](VERIFICATION_RESULTS.json)。

