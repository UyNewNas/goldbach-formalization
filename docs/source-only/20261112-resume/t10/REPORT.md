# 11 月 12 日独立核验

**建议给两条限定细叶登记绿色。现有概括性节点的整项升级清单为空。** 本次依据是三个已完成运行的实际 kernel 日志、类型与传递公理输出。精确作用域、每个存储块的源与对象 SHA-256、声明类型和允许登记的文字在 `SCOPE_ALLOWLIST.json`，SHA-256 为 `a1cc0e37c7fc5fce3485d5fc213b58fe59e6ed436c56dd61a353ffcc86bb45de`。

## 可以登记的绿叶

| 放置位置 | 建议文字 | 实际依据和边界 |
| --- | --- | --- |
| P1.4 中「第五层72块summary与entry2标量恒等式」之下 | Stored000–008 字面父表每块 4096 行，sourceIndex 等于块起点加块内下标 | 两个批次覆盖全局下标 [0,36864)。表含 sourceIndex、oldQ80、newQ80。已验证九份实际源中的完整字面数组与冻结原表逐字节相同。旧/新 Q80 的数值正确性、完整 72 块 summary/entry2、143 块 typed geometry 与 cells.npy 对应、完整第五层积分各有后续职责。 |
| P1.5「实际素数元组→cell积分→变量层均值」之下 | 通过 levelCheck 的历史五维 cell 素数修正及第四至第五策略差收敛到同一数据的积分 | Core 的三个实际定理为 `tendsto_fifthCellPrimeCorrection`、`tendsto_actualHistoricalFifthSaving`、`tendsto_upperFourthToFifthSaving`。它们对 HistoricalPrefixCapData 的明确前提是 0<a<b、old>0、levelCheck=true，正偶数 N 趋于无穷且 cap(N) 最终至少为 N^b。逐 cell 定理还要求 j∈cells5。整项原档案许可和其余变量层均值仍待验。 |

## 远端证据

| 运行，均为 attempt 1 | 源头与直接父提交 | 核验范围 |
| --- | --- | --- |
| [Core 43020290951](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43020290951) | `eedb1361edec9c28f2ec56166bd719250b7e7e05`，父 `82ced862cb5d0a2f49793a88e630fac86106e716` | 实际 leanchecker 重放 292 个不同模块。Round3/4/6 分别返回 198、414、136 条声明，跨轮按名去重共 709 条。全部返回显式和可读两种非空未截断类型及传递公理。Round6 五个定义模块的 136 个名称同时与序列化清单和环境清单一致。Round3 和 Round4 分别按固定选择范围核验。全部导出模块在 292 项重放日志中。 |
| [Stored000–004 43033551155](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43033551155) | `5db345d60c12ce03457a0a6174e0be7c8a65f1d6`，父为上面 Core 头 | 五个块和父类型模块逐名重放。1,327 条实际声明，包括父类型模块 27 条、每块 260 条。 |
| [Stored005–008 43080955096](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43080955096) | `4ba82a1b653fc2cb8ce73aa7c33d1d532265ea93`，父 `d056bd567a90185a848006f631f9f5e0def3ae21` | 四个块和同一个父类型模块逐名重放。1,067 条实际声明。两个批次合计有 2,367 个不同的块/父类型声明，父类型的 27 条只计一次。 |

Core 的三个类型收据记录的输入在导出前后一致。我将其 293 个不同输入路径及 SHA-256 逐项绑定到 eedb1361 的 Git blobs。全仓 umbrella 的重放与三个专门类型导出分别有日志。通向终结论的 `current_theorem_1_1_of_manuscript_bounds` 在三轮给出的实际类型均保留真实上下界输入。允许的传递公理为 propext、Classical.choice 和 Quot.sound。Core ZIP 的 SHA-256 为 `a91e3628c7abe86a4ef0e1577c439f4eb0e7e7f82a48d45bb4c3d74cff5eee2f`。

Stored 的冻结安装父头是 `124d09f9fc74e7b78261e2471a573f1657b5633e`，安装 manifest 为 `0aa3a96b57923c18febbc9da35d2cca88d2fec323df75dfd0ea5408a43f41963`。运行把逐行位置证明拆成每 64 个下标一段，再证明全块的原始公开命题。九个实际编译源分别匹配修复后 SHA，每份原始数组及 rows_size 与固定 Git 源字节一致。每块均核对归档 .olean、.olean.hash 和运行对象快照，核对了原 .olean 明细、实际 kernel replay 和每条展开类型。每个模块的导出名字集合等于序列化集合和环境集合，无 unsafe、partial 或新公理。两个批次观察到的传递公理并集都只有 propext 和 Quot.sound。原父类型在两批有相同源 SHA 与相同 .olean 快照 SHA，其 .olean 字节未随 ZIP 保存。两份 ZIP SHA-256 分别为 `576ceffeb454b127e7f8239fa0f7844e739d02c0f0e9f1eb6672f81719d00947` 和 `52c77dd6a2d48b235772b36c001f2695db88197ff3215aba79d8e5268a63b48a`。这些分片验收不建立全 T01 的 729 项编译或后续可恢复对象集。

三份实际运行使用 Lean v4.33.0-rc1（`62eed1db4d67327ec8120be05f1a1b0847d74561`），mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`，native `09b97db5764ade1246bfb77206baa1b124760958`，运行防护脚本 `837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877`。我重算了每份运行时审计所绑定的 state 和编译命令日志 SHA，核对了实际 `-t0 -j2 -M12288` 与各批的守护收据。两份 Stored ZIP 包含九块修复后的源码与 .olean。Core ZIP 保留证据及对象快照，不能据它恢复完整编译环境。

## 未获验收的运行

- P2 运行 43115954951，驱动 `f12fde61`，编译在五个具名依赖失败。compiler 日志含 Positive256LogRange32IntegerGuard、ThirdTailCertificateTruncation、StoredNodeQueryLookup、P4ASymmetricBranchPermutation 和 SymmetricMassCeil。kernel 和声明审计步骤跳过。结论针对该次精确源码。 [P2 运行](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43115954951)
- P4 运行 43108198136，驱动 `fb34e168`，完整 146 个目标模块编译和 kernel 重放成功。随后全声明审计在 `ImbalancedChen.FinitePiIntegral` 的序列化与定义模块环境清单不一致处退出，缺少完整的原目标类型与传递公理验收。 [P4 运行](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43108198136)
- 编写本记录时，Stored009–019 运行 43122130246（头 `356c3782e9428098a2fcbfb18c689bef264d84fa`、job 130864952699）仍在处理。该批不在本次绿色清单内。 [Stored009–019 运行](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43122130246)

## T08 水平边的两个实际因子

**两份源码通过限定数学核读，kernel credit 为零。** 我核对了作者注册的 37 项字节、原 reciprocalL 的主特征正则化、实际 uncompletionFactor 和 principalFactor，以及固定 mathlib 中 Möbius 卷积、Gamma 积分、递推和反射公式。四个公开结论的源码分别为 `Part3ActualEisensteinReciprocalGrowth.lean`（`2a1f67fd984db26a68b572564737002e3828523649f61b044fcb35f22e9d4652`）和 `Part3ActualEisensteinOrdinaryGrowth.lean`（`be2df9edebb1a49821cd6c6698795a6a1af6c04fa07075d90c008e03720824b1`）。作者报告 SHA-256 为 `ddab9afe56fce2087dc7ae93517fa27f633eb0acdcbef593d835360e68a74d95`，注册表为 `bf282119661890429253ff8a7e62ebab6a73e93c13179d220f30718afee1a4a6`。

当 1/2<σ≤3/2 时，χμ 的绝对收敛 Dirichlet 级数给出 |reciprocalL(χ,2s)|≤ζ(2σ)。主特征同样由实际正则化函数还原，因此 (σ−1/2) 倍的上界与导体和高度无关。当 |t|≥1 时，利用 2−s 处 Gamma 的 Euler 积分、|1−s|≥1 和反射公式，可将两个实际普通化因子的 (σ−1/2) 倍都控制为 Cχ exp(π|t|)，保留 χ²、Gauss 和与导体幂。Cχ 可依赖 χ。这两条估计单独仍有在左端不具有可积性的 1/(σ−1/2) 上界。实际散射条目的有界化、已完成级数与 Young 逆矩阵的控制，以及去除阻尼仍需证明。上一包的真实水平边全极限已经确定，在趋无穷的某列高度上让该差趋零就足以完成固定测试对的 Gram 恒等式。原全商 Plancherel、Kuznetsov 与 7/32 绝对估计保持开放。本次只作原始字节与已有远端证据读取，未本地运行任何证明或门禁。
