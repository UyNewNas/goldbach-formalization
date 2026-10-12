# Part 0 Round 4：模块台账候选

共同证明基线 `1a80c1bcce67886f699d097fc37fd245cd3620bf`；手稿 `ba6ec11d800eccc54406490631895e174de85766`。

前一实际核验集成 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2`。本文件仅汇总固定源码与已执行原始回执；**本轮新集成 SHA 的规范门仍待 root 执行**。

固定组件 **37**：**23** 已具可复用的完整组件证据，**14** 未完全接收。23 中的 19 已在上轮根门通过，本批新增 4（P1 permit 1 + P2 3）。另 2 个 P1 第五层源从未固定候选变成固定未编译候选。

## 类型口径

恢复上轮 591 项 = 586 项实际 pp.all + 5 项完整默认 Meta.ppExpr（Buchstab）。老 393 分区为 388 + 5；上轮实际 CI 新 198 均为 pp.all。旧 140 项 P1 默认输出（其中 7 项曾省略）已经由该实际 198 输出中的对应记录替换。

本批收到 414 项 = P1 14 项完整默认 Meta.ppExpr + P2 400 项 pp.all。当前合计 1005 项完整生产类型 = 986 pp.all + 19 默认完整；这是原始回执接收口径，不是本轮新集成类型导出执行结果。P5 S1LowerRosser 的 8 项依赖声明单列，不计入 37 或 1005。

## 模块清单

| Part | 模块 | 固定证明源 | 组件证据 / 新根门 | 完整生产类型 |
| --- | --- | --- | --- | ---: |
| P0 | `ImbalancedChen.CurrentPairedBuchstabBridge` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 2 |
| P1 | `ImbalancedChen.ActualHistoricalFifthCellIntegral` | `744316efd1887f21c91dd4b63c218fa27704c931` | 候选，未完全接收 | 0 |
| P1 | `ImbalancedChen.ActualSelectedPrefixLowerCellSum` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 9 |
| P1 | `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 8 |
| P1 | `ImbalancedChen.HistoricalPrefixCertificate` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 96 |
| P1 | `ImbalancedChen.HistoricalUpperFiveCellGeometry` | `744316efd1887f21c91dd4b63c218fa27704c931` | 候选，未完全接收 | 0 |
| P1 | `ImbalancedChen.OrdinaryLowerFourFrontier` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 27 |
| P1 | `ImbalancedChen.StoredHistoricalBoxPermit` | `744316efd1887f21c91dd4b63c218fa27704c931` | 新组件原始门已通过 / 新根待执行 | 14 |
| P2 | `ImbalancedChen.Certificates.AboveMuSecondCoarse` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 71 |
| P2 | `ImbalancedChen.Certificates.PairedCertificateChecker` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 58 |
| P2 | `ImbalancedChen.Certificates.PairedFibreIntegral` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 13 |
| P2 | `ImbalancedChen.Certificates.PairedV2` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 46 |
| P2 | `ImbalancedChen.Certificates.PairedV2Batch4To64` | `f0c00f9ccce98e04af439321a92eb9fd0dd26203` | 新组件原始门已通过 / 新根待执行 | 207 |
| P2 | `ImbalancedChen.Certificates.PairedV2Batch4To64Data` | `f0c00f9ccce98e04af439321a92eb9fd0dd26203` | 新组件原始门已通过 / 新根待执行 | 72 |
| P2 | `ImbalancedChen.Certificates.PairedV2Data` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 18 |
| P2 | `ImbalancedChen.Certificates.PairedV2Geometry` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 10 |
| P2 | `ImbalancedChen.Certificates.PairedV2Prefix4` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 35 |
| P2 | `ImbalancedChen.Certificates.PairedV2Prefix4Data` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 11 |
| P2 | `ImbalancedChen.Certificates.PairedV2Prefix64` | `f0c00f9ccce98e04af439321a92eb9fd0dd26203` | 新组件原始门已通过 / 新根待执行 | 121 |
| P2 | `ImbalancedChen.Certificates.RationalLogCertificate` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 47 |
| P3 | `ImbalancedChen.Part3CurrentLowerDistribution` | `64598da177adf861df3763d7c465ff941388b6d6` | 候选，未完全接收 | 0 |
| P3 | `ImbalancedChen.Part3DistributionTargets` | `64598da177adf861df3763d7c465ff941388b6d6` | 候选，未完全接收 | 0 |
| P3 | `ImbalancedChen.Part3LongSlotDistribution` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 35 |
| P3 | `ImbalancedChen.Part3LongSlotNormalization` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 2 |
| P3 | `ImbalancedChen.Part3PrimeAPDistribution` | `7d70a2545fd819706e473eb41e4d430ad19119d8` | 候选，未完全接收 | 0 |
| P3 | `ImbalancedChen.Part3RoughAuxiliarySW` | `7d70a2545fd819706e473eb41e4d430ad19119d8` | 候选，未完全接收 | 0 |
| P3 | `ImbalancedChen.Part3RoughAuxiliarySWNormalization` | `7d70a2545fd819706e473eb41e4d430ad19119d8` | 候选，未完全接收 | 0 |
| P4-A | `ImbalancedChen.ActualUpperDensityAssembly` | `262f69822a386a9d44efc059bceba11049668d68` | 候选，未完全接收 | 0 |
| P4-A | `ImbalancedChen.ActualUpperPolicyDensity` | `262f69822a386a9d44efc059bceba11049668d68` | 候选，未完全接收 | 0 |
| P4-A | `ImbalancedChen.UpperCoefficientPerturbation` | `262f69822a386a9d44efc059bceba11049668d68` | 候选，未完全接收 | 0 |
| P4-B | `ImbalancedChen.RealPhysicalUpperWeightBridge` | `262f69822a386a9d44efc059bceba11049668d68` | 候选，未完全接收 | 0 |
| P4-B | `ImbalancedChen.RealUpperCountingAssembly` | `262f69822a386a9d44efc059bceba11049668d68` | 候选，未完全接收 | 0 |
| P5 | `ImbalancedChen.CurrentChenBuchstabRefinement` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 5 |
| P5 | `ImbalancedChen.CurrentChenInitialMean` | `bf54caeb5e708474cacefac13a171d307b4c64f2` | 候选，未完全接收 | 0 |
| P5 | `ImbalancedChen.CurrentChenInitialSource` | `bf54caeb5e708474cacefac13a171d307b4c64f2` | 候选，未完全接收 | 0 |
| P5 | `ImbalancedChen.CurrentChenLowerScale` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 5 |
| P5 | `ImbalancedChen.CurrentChenMeanLedger` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 旧根已通过 / 新根待执行 | 93 |

## 本批来源

- P1 固定 `744316efd1887f21c91dd4b63c218fa27704c931`：许可模块 14；两历史叶仍未编译。
- P2 固定证明 `f0c00f9ccce98e04af439321a92eb9fd0dd26203`；最新交接 `101bb2291cd51f9717544ce477122fdd44eda44d`；同源码实际 CI `e6d6d57323cc358cef060fb243ec386c13cb662d`，run 38252572597。
- P5 固定交接 `7b1283e4a70874e4fb7004bafad0793069bdea71`：固定 goldbach 依赖 S1LowerRosser 8 项独立原始门已过，非新 ImbalancedChen 模块。

## 未闭合输入

P1 仍需采用的实际历史表、继承 old 身份、覆盖/支持/因式分解及完整历史积分和桥；P2 仅闭合 E0 原始 [4,64) 与 Prefix64，剩余 E0/E1、saved-floor、全域并和及实际父许可仍缺；P3 实际分布供应未齐；P4-A 同一实际 rho 的 K、P4-B hUpper、P5 完整 Chen 均值及解析 c/hLower 仍缺。Part5 只等 Part4-A，不等 Part4-B。

继承前层选择、仅过单模块编译的独立第五层候选身份继续 SOURCE_PENDING；744316… 的两份 joint-cell 源不能冒作该候选。

## 旧 CI 实际回执

| 原始阶段 | 结果 | 秒 |
| --- | --- | ---: |
| 完整 build | 9798 jobs，exit 0 | 35 |
| 原装根 leanchecker | 19 接收模块均被 replay，exit 0 | 365 |
| 根 axiom-audit v0.1.2 | 5458 声明，标准三公理，exit 0 | 25 |
| Round3 类型导出 | 新198 + 主条件桥1，exit 0 | 473 |

该结果仅适用于 28fd630…；恢复过程未启动 Lean / CI。完整旧 CI 身份核对为 `PREVIOUS_CI_VALIDATION.json`。

详尽逐模块未闭合输入、第一诊断和原始来源请读 JSON 及固定来源证据；源码类型与编译器类型分别保留。