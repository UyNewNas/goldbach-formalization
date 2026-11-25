# P2.1 历史证据复用范围

在提交 `a929011ec95843553fc2e10b7291c8077e0952c0` 上，尖锐 112-bit 节点递推及整个闭区间 `[2,12]` 的有理查询已有与当前源码逐字节一致的历史编译、内核回放、类型和公理记录。具体 40 块读表器有可定位的源码，已核实的逐块回执覆盖完整的第 00 和 01 块。下列状态是此次比对的历史基线；新运行的结果应按其各自回执记载。

[REUSED_EVIDENCE.json](REUSED_EVIDENCE.json) 按模块记录当前 SHA-256、仓库相对路径、历史普通编译、内核、类型和公理证据以及历史输出对象的路径和散列。对正文使用的终点，它保留 Lean 签名中的完整量词和前提。同批其余声明的完整类型和传递公理可在各记录的 `types_and_axioms` 中复核。此前的对象哈希不证明本轮实际加载过对象。

## 数学结论及前提

| 来源 | 已核实的结论与条件 |
|---|---|
| `ActualThirdOriginalCoupledRecurrence`、`LocalCurvature`、`SharpChord`、`Weights`、`WeightedCurvature`、`LiteralNodes`、`RationalQuery`（后六项同前缀） | 对任意 `i ≥ 32768` 和该闭单元内的实数，实际 L、H 分子有尖锐的 112-bit 弦误差界。有限递推使用加权积分余项，源码中的 `actualWeightedCellRemainders` 无需余项假设。实际节点包络适用于 `32768 ≤ i ≤ 196608`。对 `q : ℚ` 仅需 `2 ≤ q ≤ 12`，既有 112-bit 也有 160-bit 查询界。原整数表示仅需 `b > 0`、`2*b ≤ a`、`a ≤ 12*b`。右端点另有精确网格定理。10 月 24 日七个模块的 owned 审计覆盖私有与生成声明；公理并集为 `propext`、`Classical.choice`、`Quot.sound`。历史回放采用正常导入环境信任。 |
| 具体存储表 | 第 00、01 块各有 64 页、每页 64 行，合计覆盖更新行 32769 至 40960。两块证明对未读尾块函数全称量化。已核实其数据、局部检查器、页转移、初始前缀等供应模块。完整源码在 `All40CheckedTable` 定义 `literalCheckedBlockTable` 并汇总 40 块。给定合法行号可推出更新与包络；读表等于 Lean 字面递推的函数等式不需要外部输入。公开查询 `All40PublicQuery.compact_query_encloses` 只需 `2 ≤ q ≤ 12`。这些全表终点仍需要完整执行回执。 |
| `P2BuchstabRationalSemantics` | `check_sound` 需要 `check m cs = true` 及合法节点索引。整单元结论另需相邻节点均存在及实数落在闭单元中。源码有 `halfMeshSeed_checked` 具体实例。旧表的每项满足检查条件需要单独证据。 |
| `P2ContinuousSieveRational` | Suzuki 下函数的有理节点界适用于 `2 ≤ q ≤ 4`，上函数初始公式适用于 `1 < q ≤ 3`，差值节点界适用于 `2 ≤ q ≤ 3`；二次尾界适用于 `3 ≤ s`。11 月 23 日该模块及 Buchstab 模块有同源码正常编译、指定模块内核回放及全部公开声明的类型与传递公理结果。 |
| 有理区间及历史 Q80 对数 | `RationalLogCertificate` 和 `PairedFibreIntegral` 有直接 owned 审计。已核实的 `P2HistoricLogRangeReduction` 和 `P2HistoricLogPointInterpreter` 覆盖历史 `bit_length` 分支、32 项整数循环、逐步上下取整及分母 65 的尾项。点查询需正整数输入，`logI_contains` 需要初始有理数按 Q80 舍入后下端严格为正；`1 ≤ q` 可直接推出这个条件。该解释器及范围规约的同源码正常、kernel、公开类型/公理回执来自 11 月 23 日。 |

## 余下的有限检查及外部执行身份

从 `ImbalancedChen.Certificates.OriginalNodeArraysV1.All40PublicQuery` 出发有 114 个本项目模块（含自身），其源码均可定位。`docs/source-only/20261024-code-only/batch4/source-manifest.json` 将第 02 至 39 块的 38 个 Data、38 个 FullCheck 和两个 All40 模块共 78 个源码标为 `SOURCE_ONLY_UNCOMPILED_ZERO_PROOF_CREDIT`。本次以原字节核对了全部 78 个 SHA-256。第 02 块从 40961 起，第 39 块止于 196608；这些源码的存在与历史全表回放属于不同的证据。重新取得对象时应据实际对象及依赖选取缺少的检查，保留两个全表终点的普通编译、内核回放和完整类型/公理结果。

`P0RationalQueryPublicAPI.rangeQuery_sound` 已写出公共区间形式，其前提为 `2 ≤ lo ≤ hi ≤ 12` 和 `x ∈ [lo,hi]`。`storedPointQuery_sound` 另外接受一个 `CheckedBlockTable`。相应具体见证由上述 All40 汇总源码给出。公理清洁的条件定理本身不能补充有限检查。

对外部执行身份，保存的初始四列有逐字节对照记录，Block01 另有 4096 行的 16384 个字段逐字面比对记录。两者位于 JSON 的 `external_comparisons`。完整历史 producer 的身份需指明是 P112/P160 独立实现还是原 P80 实现，并按实际程序、输入、调用分支、整数舍入和所引用的输出绑定。独立实现和原 P80 实现分别使用不同的种子及区间算法；`docs/source-only/20261102-resume-30j/compact_leaf/REPORT.md` 第 15 行记录了这个区别。`All40CheckedTable` 的递推等式只涉及其附带的 Lean 字面表。通用 64 项 `P5U7Q80Backend` 的包络可靠性也未给出与原 32 项输出逐位一致的定理。

## 历史对象位置

10 月 24 日的直接编译回执在 `command -o` 中给出旧 WSL 工作区的绝对路径，位于 `/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation/.lake/proof-continuation/lib/lean/`。其 owned 审计回执另存有 `inputs_before.owned_object_parts` 散列。11 月的 Suzuki 记录使用 `/workspace/blue-p6-build/.lake/build/lib/lean/`，Buchstab、Q80 历史对数及范围规约记录使用 `/workspace/blue-member-build/.lake/build/lib/lean/`。更早的基础模块另有 `/workspace/scratch/535d89efd063/p0-round2/validation/.lake/build/lib/lean/` 记录。各对象的完整路径与 SHA-256 见机器清单。本次没有访问历史云端，也没有在本轮导入、重编或回放这些对象。

表达问题集中在整数商、余数、尺度与闭区间端点；对应转换已有定理。有限表的剩余工作以现成检查源码和既有回执为起点。实质待证的是在所声明范围内绑定具体历史程序执行与产物，以及任何仍被需要的旧 Buchstab 表行实例；现有证据未显示手稿数学不等式本身有反例。
