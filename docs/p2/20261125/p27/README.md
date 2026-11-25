# P2.7 same-mask-v2 配对证书接收说明

**当前验收状态：pending。** 当前候选源码由 [81 文件源码清单](source-manifest.json) 的逐文件哈希绑定。最新实际任务 `572afb7f57df4246b428983dce6188fc` 运行于 `76f17bf5c6a1878ae057f97f6547522dde3f40ff`，数值/Fubini 闭包已有 **71/73** 成功：复用 68 个对象，并新编译通过完整证书、实际网格接口及支撑并集积分模块。全部 12 个条带块和装配仍沿用已成功对象。实际 Fubini 编译暴露具体坐标、集合重写和产品测度表达问题；本轮最小修复已完成[独立源码审查](support-fubini-review.json)，复编译仍待执行。

本任务在数值阶段失败后即停止，19 项数值审核、native 接入、完整分析链和 26 项最终审核均未启动；不把源码审查、参数化探针或历史接收凭据记作本轮完成。参见[实际任务回执](numeric-fubini-attempt2-job.json)及[完整原日志](numeric-fubini-attempt2.log)。

## 稿件范围

规格固定为 `chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e` 的 1106 发布稿。

| 稿件位置 | 本轮对应内容 |
| --- | --- |
| `paper/release-20261106/en/argument.tex`，837–910 行 | `lem:current-omega-refinement` 的实际 Buchstab `7/3 → 11/20` 下界；`eq:current-Z` 的内纤维截断；`eq:current-extra-fibre` 的 `K/80` 归一化；`eq:current-extra-gross` 的严格有理下界。 |
| `paper/release-20261106/en/numerical-appendix.tex`，774–832 行 | same-mask-v2 的两族配对矩形及其并集，`num:paired-extra`、`num:gross-bound`。两族分别为 6,091、11,481 行，并集共 17,572 行。 |

本轮沿用 186 条带编码的全部 17,572 行、实际网格坐标与原截断 `min(u_l, 3(1-t_r-u_r)/13)`。进入保留算术父项的 P5 计数许可仍在既有计数范围内；本接口不以该许可或某个目标积分下界作为假设。

## 接收接口与积分边界

入口为 [P2PairedCertificateCompletion.lean](../../../../ImbalancedChen/P2PairedCertificateCompletion.lean)，声明命名空间为：

```text
ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedCertificateCompletion
```

以下表格描述当前源码中的声明；其本轮运行验收仍为 pending。

| 声明 | 接口内容 |
| --- | --- |
| `endpoint_strict_margin` | 原精确下端点严格大于稿件采用的 `558583 / 10^9`。 |
| `integral_strict_lower` | 全部行的 constant-gain 积分**总和**严格大于该值。 |
| `actual_grid_strict_lower` | 同一结论按实际采用的网格坐标求和。 |
| `support_union_strict_lower` | 同一结论写成实际支撑并集上的乘积体积积分。 |
| `actual_buchstab_gain_strict_lower` | 实际 Buchstab 额外增益积分严格大于该值。 |
| `actual_buchstab_difference_strict_lower` | 实际 Buchstab 积分减去同域、同权重的半基线积分，严格大于该值。 |
| `complete_analytic_certificate` | 合取网格基数 17,572、原精确上下端点及 constant-gain、实际 Buchstab 增益的严格下界。 |

记 `I = PairedV2.FullMask.integral`，`J = P2SemanticGainSetIntegral.unionSemanticIntegral`。源码组合的边界为：

```text
L = 55858378943374979 / 100000000000000000000
U = 55858409959907296 / 100000000000000000000
g = 558583 / 1000000000

L ≤ I ≤ U，g < I ≤ J
J = unionBuchstabIntegral - unionHalfBaselineIntegral
```

`I` 是原 `K/80` 常数增益核的真实积分总和。`J` 在同一实际支撑并集上积分
`((K/4)/(t*u*z^2*w)) * (LiLiuPrereqBuchstab.buchstab ((1-t-u-z-w)/z) - 1/2)`。
Chen 因子 `1/4` 与已证明的增量 `1/20` 合成 `1/80`，各计一次。**上端点 `U` 只约束 `I`，不作为 `J` 的上界。** 对应积分定义、可积性与比较见 [P2SemanticGainSetIntegral.lean](../../../../ImbalancedChen/Certificates/P2SemanticGainSetIntegral.lean)。

## 复用、定义归属与审核范围

原 witness、行选择器、checker、分块数据及自然数端点和均沿用既有实现。原数据入口为 [corpus-renewal-paired-certificate-v2-20261010.json](../../../../verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json)。[reuse-audit.md](reuse-audit.md) 与 [reuse-audit.json](reuse-audit.json) 记录历史接收凭据及当前源码哈希匹配；历史接收、前置对象重建和本轮完整依赖验收须分别判断。

`pairedChenQuarterWeight`、`pairedSemanticBuchstabGain` 的全名仍位于 `ImbalancedChen.Certificates.P2HistoricalFibreBinding`，定义体保持原样；其 **defining-module owner 已移至** [CurrentPairedBuchstabBridge.lean](../../../../ImbalancedChen/CurrentPairedBuchstabBridge.lean)。声明审核应按实际模块归属计入这两个定义，不能仅凭命名空间判断 owner。`P2HistoricalFibreBinding` 通过导入继续提供原名字；P2.7 分析入口不再导入其历史下筛链。

[audit-targets.txt](audit-targets.txt) 列出本轮 **26 个待审核 defining modules**，包括 12 个条带检查块、装配、完整证书及网格/Buchstab/积分接口。[project-closure.json](project-closure.json) 列出入口的 **81 个仓库内模块依赖闭包**；该数字不包括外部 Mathlib、goldbach 依赖，也不表示 81 个模块已经逐项审核。当前入口只选择 `ImbalancedChen.P2AdoptedRowsActualEnclosure` 作为实际网格声明 owner，不同时导入 `Certificates/` 下的同名副本。

## 复现入口

在依赖已准备好的仓库根目录，使用 [lean-toolchain](../../../../lean-toolchain)、[lakefile.toml](../../../../lakefile.toml) 固定的环境：Lean `4.33.0-rc1`；Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`；goldbach `09b97db5764ade1246bfb77206baa1b124760958`。

目标模块的编译与对象回放入口为：

```sh
lake build ImbalancedChen.P2PairedCertificateCompletion
lake env lean -DwarningAsError=true ImbalancedChen/P2PairedCertificateCompletion.lean
lake env leanchecker --verbose ImbalancedChen.P2PairedCertificateCompletion
```

上列命令是接收入口，不是已执行通过的记录。正式验收还须对应 `audit-targets.txt` 的声明类型、模块归属、独立回放和传递公理记录，并绑定实际源码、对象及依赖版本。禁用 `sorry`、`admit`、新增公理、`native_decide` 和 unsafe 证明供应；传递公理审核仅允许既定的 `propext`、`Classical.choice`、`Quot.sound`。

## 现有证据与待填验收结果

| 文件 | 当前可支持的结论 |
| --- | --- |
| [progress.json](progress.json) | 任务 ID、源码版本与 `complete: false`；任务状态须与本节及各任务最新回执一同核对。 |
| [prerequisite-job.json](prerequisite-job.json)、[prerequisite-compile.log](prerequisite-compile.log) | 前置任务 `86ef184c8d8b4f9e932af057554988dd` 退出码 0，53 个模块编译成功；独立审核仍待补。 |
| [strip00-job.json](strip00-job.json) | Strip00 任务 `96d6a29e696b4bfa97d85b22f90822ac` 退出码 0，外层耗时 14.758264 秒，峰值内存 3,938,062,336 字节；尚未独立回放。 |
| [source-review.json](source-review.json) | 源码评审范围及注释修正记录；不构成编译或接收凭据。 |
| [reuse-audit.md](reuse-audit.md)、[reuse-audit.json](reuse-audit.json) | 原证明复用、历史源码匹配与证据边界。 |
| [audit-targets.txt](audit-targets.txt)、[project-closure.json](project-closure.json) | 26 个审核目标及 81 个仓库内依赖节点。 |

Strip00 本轮闭包包含 24 个模块，其中 23 个复用既有对象；目标 Lean 编译耗时 11.078 秒。以上是编译与对象复用记录，不包含独立 replay。73 个无需 native 根的数值/Fubini 模块的任务 `e0cdaba244874eecbfb9bf787ac90367` 已结束：68 个成功（54 个复用、14 个新编译），另 5 个失败或依赖阻断，独立审核尚未启动。详见 [任务回执](numeric-fubini-attempt1-job.json)和[完整日志](numeric-fubini-attempt1.log)。全部 12 个条带块均已通过，原 witness、checker 和数据未改；两处表达修复仍须复编译。

当前运行及验收状态：

| 验收项 | 状态 |
| --- | --- |
| 53 个前置模块严格编译 | 编译成功；独立回放/审核 pending。 |
| Strip00，任务 `96d6a29e696b4bfa97d85b22f90822ac` | 编译成功；独立 replay / 声明审核 pending。 |
| 分析链，任务 `0ecd373efb4d4b44957f05f3416631f8` | 前置验证失败：旧 external snapshot 缺少 TailPropagation，未启动 Lean；任务记录绑定 `77db7b4…`。 |
| 73 个无 native 数值/Fubini 模块的继续验证 | 最新 71/73 成功；SupportFubini 表达错误，ContinuousFibreFubini 被阻断；最小修复后复编译 pending。 |
| 12 个条带检查块及完整证书 | 全部条带块、装配和完整证书已编译；独立审核 pending。 |
| 补充 native 资格及 P1 物理 payload | 准备中；资格审查与实际接收结果 pending。 |
| 26 模块声明类型、owner、传递公理审核及独立回放 | pending。 |
| 最终源码/对象/依赖哈希绑定与正式接收凭据 | pending，待实际记录补入。 |

**最终验收结果：pending；本快照不标记 accepted。** 后续更新本节时应引用实际运行记录及其绑定的提交，不以源码评审或历史叶模块凭据替代本轮结果。

## 现有 Buchstab 对象的接入校验

[p27_qualify_native_inputs.py](../../../../verification/part2/p27_qualify_native_inputs.py) 为本入口创建独立输入快照，复用旧环境和原 P6 来源，不改外部数学源码或旧快照。其[独立源码审查](native-adapter-review.json)与 22 项无编译检查已通过；真实对象包已取回并逐项核对；完整 checkpoint 已实际确认不含这三个模块的 eligible provider。两个前置模块改由各自已有的 P6 生产记录校验，TailPropagation 保持其原完整固定回执；最终 P2 `ExternalSnapshot.verify` 仍待实际执行。输入资格不等于 P2.7 编译、内核重放或数学验收。

原 P6 portable 输入已按哈希接收并打包为 [native-inputs.tar.xz](native-inputs.tar.xz)，其 [转运核对](native-transport-verification.json)、[Git 对象核对](native-blob-receipt.json)与[真实包字段审查](native-bundle-review.json)均保留。包内原数学源码和对象未改；两项 credit 明确为 false。P2 环境中的 provider、实际导入与运行时重绑仍须通过独立快照门禁。

## 后续任务与单模块对象复用

现场任务 `572afb7f57df4246b428983dce6188fc` 已在数值阶段停止，最新结果为 71/73；[实际入队命令](queued-resume-command.sh)先复用数值/Fubini 编译记录并执行 19 项审核，再串行完成 native 输入资格、CurrentChen 历史对象接入、81 模块闭包编译及全部 26 项审核。后续实际复编译与分析阶段仍为 pending。

[CurrentChen 原对象包](currentchen-inputs.tar.xz)保留其原 P6 源码、对象及生产上下文；[转运核对](currentchen-transport-verification.json)、[Git 对象核对](currentchen-blob-receipt.json)与[接收器独立审查](currentchen-adapter-review.json)分别记录字节运输与源码检查。接收器 [adopt_p27_currentchen_cache.py](../../../../verification/part2/adopt_p27_currentchen_cache.py)只接入这一未改源码模块，必须逐项重绑实际运行时和 16,623 项原导入 facets，并保留既有 registry 条目。记录明确 `new_strict_compile=false`，仍须执行该模块本轮独立审核。

[两处 Lean 表达修复的独立审查](lean-compatibility-review.json)不增加编译信用。现场接受成功后，使用下述增量证据命令保留单模块接入回执及完整导入映射；早先的 `supplemental-export-command.sh` 已被替代，不再生成第二份全量导出。

Function/Bounds 的显式 P6 来源扩展另有[独立审查](native-prerequisites-review.json)：29 项针对性测试和真实历史包字段检查通过；原 checkpoint、Tail provider 和 descriptor 门禁保持不变，原 `selected={}` 的结果未被改写。这一审查仍不代表 P2 实际环境接收或数学验收。

## 排序壁的具体坐标归约

P3 参数化表达探针 `67f828f5c16f4dd58ebdeca4c891aa00` 实际以退出码 1 结束，唯一诊断是在 `orderingWallForm_ne_zero` 中仍有 `![0, 0, 0, 1] 3 = 0`。在原简化后增加 `change (1 : ℝ) = 0 at hh` 和 `norm_num at hh`，仅补齐该具体坐标的定义归约。参见 [原始错误日志](p3-expression-probe-before.compile.log)、[探针原源码](p3-expression-probe-before.lean)及[两行修正的独立审查](ordering-wall-review.json)。修复探针 `cdaef8c04ada491abd231363ac6788dc` 实际通过，退出码 0，外层约 3.464 秒、Lean 约 3.376 秒，日志为空且无警告。参见[前后原件字节核对与边界说明](p3-expression-probe-verification.json)。探针使用显式参数化的已有供应结论，不是 P2.7 模块接收；本轮完整模块编译仍为 pending。

最终证据将引用固定旧归档中逐字节相同的依赖记录，并完整保留本轮新审核材料及 CurrentChen 接入补充；不再运行一次会重复写出全部旧上下文的补充全量导出。该打包安排不改变任何接收计数或证明信用。

## 增量证据交付入口

[专用打包和接收脚本](../../../../verification/part2/p27_delta_evidence.py)已通过[独立审查](delta-evidence-review.json)：17 项针对性测试及 5 个额外拒绝用例通过。它只复用原始 exporter 的有效接收清单，要求精确的 26 个目标和 81 个项目上下文；旧字节引用必须在接收端从固定 Git 文件流式重读并核对。所有新增审核、完整类型、日志与 CurrentChen 补充保持原字节。打包本身不增加任何数学信用，实际运行仍为 pending。

从首次 exporter 的实际输出取得 `manifest_sha256` 后，在 P2 工作目录执行：

```sh
bash docs/p2/20261125/p27/prepare-delta-evidence.sh ORIGINAL_MANIFEST_SHA256
```

[该准备命令](prepare-delta-evidence.sh)仅从首次全量导出派生增量包，并保留 CurrentChen 接入材料。传输页数以实际输出为准。接收端再执行：

```sh
python3 -B verification/part2/p27_delta_evidence.py verify P27_COMPLETE.delta.tar.xz \
  --repo . --git-tree FIXED_PUBLICATION_COMMIT \
  --manifest-sha256 ORIGINAL_MANIFEST_SHA256 \
  --output p27-delta-verification.json
```

`ORIGINAL_MANIFEST_SHA256` 必须独立取自原导出任务回执，不能只相信传输包自己的声明。接收成功后仍应核对最终发布的全部 81 个源文件与原接收清单的字节身份。

## 当前 Fubini 表达修复

候选改动仅位于 `P2PairedSupportFubini.lean`：移除两项确实未使用的 simp 参数，展开 `Fin.cons` 的具体数值坐标和原 `tInterval/uInterval` 定义，使用 `Measure.volume_eq_prod` 统一同一乘积 Lebesgue 测度的记号，并在区间重写前进行 β 归约。原定理陈述、假设、同 mask 积分域、核及 `K/80` 均保持不变。稿件对应段落已核对，本轮诊断属于 Lean 表达适配；实际编译仍待执行。
