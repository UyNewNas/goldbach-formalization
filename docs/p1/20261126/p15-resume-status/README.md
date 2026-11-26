# P1.5 续作状态：2026-11-26

记录时间：2026-11-26 09:26（Asia/Shanghai）。P1.5 整体仍未闭合。本轮已发布的数学源码及原验收记录继续保留；新一批三个目标的提交在 MCP 连接阶段返回 `UNAVAILABLE / HTTP 429`，没有获得任务编号或新增 Lean 验收。公开连接观察见 [CONNECTION_OBSERVATIONS.json](CONNECTION_OBSERVATIONS.json)。该连接错误不改变此前成功的编译结论。

## 已发布的稿内推进

| 内容 | 发布源与当前结论 |
| --- | --- |
| 原 singleton 剩余 Type I 的活项几何 | `6067deae48cbdc0095ac12acc47e24a6ef29cb69` 中的 `P1OriginalSingletonRemainingTypeIGeometry.lean`，从原非零支撑和真实图尺度导出统一数值门槛，再从无 medium 的一长／两长选择中排除一长。源码已写出，待 Lean 验收。 |
| 两个原历史计数的修正项归约 | `e70bd4994a95f45cc2c75b6bae2213bcb2f99d91` 中的 source-only `P1OriginalHistoricalAtlasCorrectionReduction.lean`，保留两个历史策略的原符号、原剩余类、精确互素均值及共同阈值，用原 OneLong、trim、proper-power 结果把计数误差归约到 `Σ (mediumAtlas + remainingTypeIAtlas)`。等待旧 OneLong 依赖的正式采用及编译。 |
| 原 rough / cutoff / reserve 源码采用 | `6067deae48cbdc0095ac12acc47e24a6ef29cb69` 保留已存在源码的精确来源和修复历程。未以本轮来源登记冒充新编译。 |
| 当前上下文的 21 个目标执行入口 | `e70bd4994a95f45cc2c75b6bae2213bcb2f99d91`，26 个本地 Python 检查通过。固定 360 个项目源码的来源；实际只处理显式选择目标的依赖范围，复用各模块原始验收。 |

相关证明与审查：[活项几何](../../20261125/p15-singleton-remaining-typei-geometry/README.md)、[历史修正归约](../p15-historical-atlas-correction-reduction/README.md)、[当前执行入口](../p15-current-corrections/README.md)。这些源码检查不替代 Lean elaboration、内核回放或完整 owned 声明检查。

## 已有验收继续按原身份复用

下表列出已记录的原任务范围，避免再次编译相同证明。各行分别保留自己的源提交、模块范围和回执，不能用新分支 HEAD 替换其验收身份。

| 范围 | 原任务 | owned / public | 验收记录 |
| --- | --- | --- | --- |
| 实际第四／第五均值 23 个 owner | `job_01a0f20b7d60446bab9131098773bd2f` | 378 / 349 | [actual-means](../../20261125/p15-actual-means/README.md) |
| 初始 4 个实际输入 owner | `job_1ed0e0c8d4ee466f8444aff044abe510` | 47 / 44 | [initial-four](../../20261125/p15-singleton-proper-power/evidence-initial-four/) |
| 当前 P1 上下文 Atlas 10 个 owner | `job_5f42ad18fde84377987c244daf0b5bfc` | 242 / 229 | [Atlas 回执](../../20261125/p15-current-public-acceptance/ATLAS10_PUBLIC_ACCEPTANCE.json) |
| `Part3FiniteLambdaOverLogCore` | `job_0c98f60f3fbe4aaa8d3e23fcf53dbcb8` 的已接受 owner | 13 / 13 | [Core 回执](../../20261125/p15-current-public-acceptance/CORE_PUBLIC_ACCEPTANCE.json) |
| `Part3BrunWeights` | `job_41c06d666c6642889cc27d82ee281eb7` 的已接受 owner | 28 / 24 | [Brun 回执](../../20261125/p15-current-public-acceptance/BRUN_PUBLIC_ACCEPTANCE.json) |
| `PrimeProductsMellinExactMeanInsertion` | `job_8d58f7741c56448980ca0984ae5c0239` | 数量待公开汇总 | [原成功终态](../../20261125/p15-original-atlas-proper-power/MELLIN_COMPILE_ACCEPTANCE_OBSERVATION.json) |

Mellin 原成功任务绑定源 `21789da92213323d645122cfcc7dff9c10dc82d6`，normal、named-kernel、full-owned 均已完成。本轮尝试的 `mellin-current` 只读汇总不重跑这些证明；其提交也遇到相同连接错误，因此未填写尚未收集的 owned/public 数量。

Core 和 Brun 所在整批任务后来在别的 owner / 前置依赖处停止，其已完整接受的单个 owner 保持原结论。这里没有将整批任务标记为成功。

## 当前可执行的最小编译批次

已提交尝试使用源 `e70bd4994a95f45cc2c75b6bae2213bcb2f99d91`，明确选择：

1. `ImbalancedChen.P1OriginalSingletonSupportData`。
2. `ImbalancedChen.P5OriginalPrimeChartHBWitnesses`。
3. `ImbalancedChen.P1OriginalSingletonCutoffData`。

这三项的当前项目依赖范围为 130 个模块。安装器只补原路径缺失且与冻结 Git 源一致的选定源码；验收入口先校验原依赖回执与对象，再对未验收目标运行原 normal / kernel / full-owned 流程。冲突、缺失依赖或未完成旧回执会停止。当前没有新任务在排队。

21 个目标中，18 个的当前依赖范围不经过尚未接受的 19 个 P3 项目 owner；另外 3 个 proper-power 相关目标仍需要该前置范围。新的活项几何不在这版 21 项白名单内，后续应另做明确来源绑定。

## 复用现成外部产物

此前 P3 已有五个 Fouvry native 模块的真实对象、伴随文件及 Lake trace，P1/P3 对应源码相同。本轮恢复了原观察，没有重做这些外部定理。新的 [receiver 检查](../p15-fouvry-existing-artifact-reuse/README.md) 只准备四项实际依赖哈希查询及三个直接父模块的元数据检查；它尚未在云上执行，没有复制对象、改写 trace 或改变运行策略。

现有证据仍不足以宣布 P1 的 `CompleteWeil` 整体可用。后续需要核对 P1 实际依赖上下文，再决定现成产物能否采用。

## 历史单长归约的采用边界

对新历史归约进行了有界依赖核对：读取并核对 11 份现有源码的指纹，验证了两条直接 import 路径。两条路径均到达先前已登记的缺源停止点：

- `HistoricalOneLongRemainder → OneLongConsumer → OneLongGeometry → P5OriginalOneLongMertensChartHarmonic`。
- `HistoricalOneLongRemainder → OneLongConsumer → OneLongGeometry → OneLongRestoration → OneLongFiniteE5 → P5OriginalOneLongActualChartE5`。

完整模块名、路径、SHA 与原停止点记录见 [HISTORY_ADOPTION_BOUNDARY.json](HISTORY_ADOPTION_BOUNDARY.json)。本轮没有重新搜索原九个缺源，也没有重试此前返回 404 的 blob；上述两条路径已足以确定当前归档不能直接构成完整可采用闭包。这是现有源码和集成边界，不能据此推断手稿存在数学反例。

`OneLongConsumer`、`OneLongRectangle`、`OneLongCoefficients` 及 `PhysicalKernelSmoothing` 的原 FREEZE / REGISTRY / PUBLIC_SOURCE_MANIFEST 明列 source-only，不能从相邻已验收项目外推其编译信用。已验收的 TrueD 两个 owner 与历史 pointwise owner 保留 `d20acdf…` 的原完整验收。

未来接入时还须保留两项已经完成的声明迁移：历史 remainder 的 rough 调用可改导入当前 `P1OriginalSingletonAtlasRoughPrime`，继续使用原 namespace 下的 `eventually_original_singleton_roughPrimeReserve_sum_zero`，证明正文无需重写；历史 `MiddleSmoothing` 应采用已登记的 provider postimage，使 `remainingModuli`、`smoothRemaining`、`policyRemaining` 继续由已验收的 `P1OriginalHistoricalMiddlePointwiseData` 唯一持有。直接搬入旧完整 provider 会重复定义这些声明。

## 整体 P1.5 仍需完成的数学连接

1. 把完整 signed medium 分布估计应用到原实际物理族，保留实际策略的因子分解及 `MediumIndex` 许可。复用 P3.4/P3.5 的已有工作和后续供应端，不另开同一谱证明。
2. 在已写出的 singleton 两长几何上接入原同系数字典，支付 rough 还原、各端点 strip、短系数质量、模数矩、Fourier L1 / tail 和外层有限预算。
3. 将两个历史计数的修正归约和上述实际分布估计合并到同一参数选择、同一充分大阈值，完成终局调用。

详细合同及 1106 手稿定位见 [REMAINING_BOUNDARY.md](../../20261125/p15-remaining-original-distribution/REMAINING_BOUNDARY.md)。本轮审查没有给出手稿反例；当前源码连接和供应端未闭合应按实际状态记录。项目看板的节点验收状态本轮未修改。
