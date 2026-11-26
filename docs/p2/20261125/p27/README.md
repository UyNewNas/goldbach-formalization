# P2.7 same-mask-v2 配对证书接收说明

**P2.7 已完成稿内分析证书验收：完整编译闭包 81/81，目标审计 26/26，共 679 个唯一所属声明；四页证据已完整接收，固定归档字节核验、全部声明重建、七个闭合完成定理及 81 份源码身份均已通过。** 本次接续没有新增 Lean 编译、内核回放或证明源码改动；复用已有真实通过记录。完整凭据见 [最终验收](acceptance-20261126/acceptance.json)、[接收端冻结核验](acceptance-20261126/delta-verification.json)、[原声明类型](acceptance-20261126/types.txt)及[逐节点稿内范围核对](acceptance-20261126/completion-manuscript-review.json)。 实际任务 `5ad392f1b0954a89a052ab7aaad82e6f` 运行于 `549ea2164c17a8a3f66edbbd88262ea9d5ef05f0`，先验证全部 77 个既有缓存，再复用这 77 个对象并新编译四个剩余模块；审计复用 19 项、新完成 7 项。参见[编译阶段原输出](full81-compile-stage-observed.log)和[26 项审计汇总观测](full81-audit26-observed.json)。

历史任务 `d734023ac6d243279c3f73e3308f111f` 运行于 `9c5a20ab9e13bc9393db8c9f5b0b0e4212006970`，已完成数值/Fubini **73/73 编译、19/19 审计及 551 个所属声明**，并通过三个外部 Buchstab 输入资格与 CurrentChen 原对象接收。当时完整闭包复用 74 个对象，新编译 `PairedV2`、`CurrentPairedBuchstabBridge`、`PairedV2FullBuchstab`，达到 77/81。参见[历史原始日志](analytic-attempt1.log)、[任务回执](analytic-attempt1-job.json)及[数值审计汇总](numeric-audit-summary-observed.json)。这些成功对象和审计在本次继续验证中已实际复用。

原候选 `9b60d129` 对 VariableLower 的两个实际错误作最小修正：显式将原有理截止不等式 cast 到实数并正规化，以及在既有权重/增益重写前消除函数应用。文件 SHA256 为 `a1980a59ccb4095411a4a01faefd9dcf528248f33d2e2eadf1d76f0b62a735d6`，其[独立源码复核](variable-lower-expression-review.json)之后，已在实际任务 `5ad392…` 编译通过，29 个所属声明也通过独立审计；三个下游模块一并通过。全部 81 文件由[源码清单](source-manifest.json)绑定。

native snapshot 绑定全部 81 份项目源码，因此本次源码修正使用了新的调用方绑定。窄迁移工具已核验三个上游分析对象的原 strict 编译来源：`PairedV2` 没有 native 祖先，其 schema 2 原记录保留；`CurrentPairedBuchstabBridge`、`PairedV2FullBuchstab` 两条 schema 3 记录已在实际输入等价性核对后完成重绑。该工具此前通过 30 项本地 fixture 测试及 2 项独立拒绝检查，并完成[独立源码审查](native-record-rebind-review.json)；[本地验证记录](local-resumption-verification.json)与[测试原输出](native-record-rebind-tests.log)保留原件。原 d734 registry、旧 snapshot 和三个原成功日志均先封存，再进行重绑，见[封存观测](original-capture-observed.json)、[capture 实际日志](resume-20261126-capture.log)及[实际重绑回执观测](binding003-observed.json)。重绑没有重新编译对象或增加新的内核信用。

P2 于北京时间 **2026-11-26 00:14:36** 恢复正常响应，见[环境观测](resume-20261126-system-info.json)。恢复时原工作目录仍为 `9c5a20ab…`；任务 `9892636962dd40fab7c809ad2ff31ac7` 在任何 fetch/checkout 前完成封存，exit 0，用时 114.613 秒。原 registry SHA 为 `f91d99533ee30ec2ced9b25d9c980804930787e7741f51b56a3668ac11631b48`，原 CAPTURE 清单的外部观测 SHA 为 `d078c02618aa11821055ad4cebeeb815474f41a64a252c6a3abf4c20fce978e7`。原 `Integrals.Basic` 对象也在旧 snapshot 中明确绑定。此前的[会话错误记录](p2-connection-observation.json)保留为历史证据，已不是当前阻塞。

封存完成后才切换到固定候选 `549ea216…`，全部 81 个源码 SHA 实际匹配。fresh002 在进入 Lean 前因稀疏检出缺少旧 `checkpoint_original_protocol.py` 而停止，见[历史原日志](resume-20261126-binding002.log)。任务 `0e75fdae4cbf4a0c853856c1c5eb2704` 已按 Git 固定原字节恢复协议，实际完成 fresh003、CurrentChen adoption003 和两条记录重绑，exit 0，用时 344.062 秒，源码编译与对象 loader 调用均为 0。见[原始输出](resume-20261126-binding003.log)和[三个阶段的观测回执](binding003-observed.json)。失败的 002 证据保留；该回执中全闭包与审计的 pending 是当时的阶段状态，后续实际结果已为 81/81、26/26。[恢复步骤](resume-from-d734.md)、[历史流程审查](resume-command-review.json)及[003差异审查](resume-command-review-003.json)仅为流程材料，不能代替真实运行结果。

任务 `5ad392…` 整体已 succeeded、exit 0，用时 648.181818293 秒，峰值内存 5,064,331,264 字节；见[完整原始日志](full81-audit26-export.log)、[最终任务回执](full81-audit26-export-job.json)及[首份导出观测](first-full-export-observed.json)。首次完整 export 已成功，原始结果为：

| 导出产物 | 字节数 | SHA256 |
| --- | --- | --- |
| `manifest.json` | 10,772,982 | `73179a250532882aa5a945ba149fb734ee776dd3fdcef5d386af69b6303eca08` |
| `all.tar.gz` | 584,685,232 | `8e524bf8c5dd8727c344ba98e456ea0bd57c09bc15ac0ec9d128be965c7fbee2` |

归档未压缩总量为 4,308,648,372 字节。原 exporter 的 Winner9 全 P2 覆盖标志仍为 false、`numeric_rows` 为 0，均保留其原定义；这些旧范围字段不表示 P2.7 失败，也不能为本节点完成而改写为 true。**原 delta 的等字节流重编码已接收并验收。压缩传输包为 5,909,172 字节，SHA256 `67750c831b532c3f763ff7d113400af0556a11024822e52fa195cc5a376b1b4b`；完整解压 tar 流为 119,715,840 字节，与原包重编码收据匹配。**

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

Completion 模块的七个所属声明已通过本轮独立审计；以下表格保持其源码接口边界，完整类型与证据的接收端字节核验已通过，见 [七个原始完整类型](acceptance-20261126/types.txt)。

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

[audit-targets.txt](audit-targets.txt) 列出本轮 **26 个已完成审核的 defining modules**，包括 12 个条带检查块、装配、完整证书及网格/Buchstab/积分接口。[project-closure.json](project-closure.json) 列出入口的 **81 个仓库内模块依赖闭包**；该数字不包括外部 Mathlib、goldbach 依赖，也不表示 81 个模块已经逐项审核。当前入口只选择 `ImbalancedChen.P2AdoptedRowsActualEnclosure` 作为实际网格声明 owner，不同时导入 `Certificates/` 下的同名副本。

## 复现入口

在依赖已准备好的仓库根目录，使用 [lean-toolchain](../../../../lean-toolchain)、[lakefile.toml](../../../../lakefile.toml) 固定的环境：Lean `4.33.0-rc1`；Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`；goldbach `09b97db5764ade1246bfb77206baa1b124760958`。

目标模块的编译与对象回放入口为：

```sh
lake build ImbalancedChen.P2PairedCertificateCompletion
lake env lean -DwarningAsError=true ImbalancedChen/P2PairedCertificateCompletion.lean
lake env leanchecker --verbose ImbalancedChen.P2PairedCertificateCompletion
```

上列命令是接收入口，不是已执行通过的记录。正式验收还须对应 `audit-targets.txt` 的声明类型、模块归属、独立回放和传递公理记录，并绑定实际源码、对象及依赖版本。禁用 `sorry`、`admit`、新增公理、`native_decide` 和 unsafe 证明供应；传递公理审核仅允许既定的 `propext`、`Classical.choice`、`Quot.sound`。

## 现有证据与最终验收结果

| 文件 | 当前可支持的结论 |
| --- | --- |
| [progress.json](progress.json) | 任务 ID、源码版本与当前 `complete: true`（仅 P2.7 范围）；任务状态须与本节及各任务最新回执一同核对。 |
| [prerequisite-job.json](prerequisite-job.json)、[prerequisite-compile.log](prerequisite-compile.log) | 历史前置任务 `86ef184c8d8b4f9e932af057554988dd` 退出码 0，53 个模块编译成功；该任务自身只提供编译记录，本轮独立审核范围以 26 项汇总为准。 |
| [strip00-job.json](strip00-job.json) | 历史 Strip00 任务 `96d6a29e696b4bfa97d85b22f90822ac` 退出码 0，外层耗时 14.758264 秒，峰值内存 3,938,062,336 字节；该任务自身不含独立回放，后续本轮数值审计已完成。 |
| [source-review.json](source-review.json) | 源码评审范围及注释修正记录；不构成编译或接收凭据。 |
| [reuse-audit.md](reuse-audit.md)、[reuse-audit.json](reuse-audit.json) | 原证明复用、历史源码匹配与证据边界。 |
| [audit-targets.txt](audit-targets.txt)、[project-closure.json](project-closure.json) | 26 个审核目标及 81 个仓库内依赖节点。 |
| [analytic-attempt1.log](analytic-attempt1.log)、[analytic-attempt1-job.json](analytic-attempt1-job.json)、[numeric-audit-summary-observed.json](numeric-audit-summary-observed.json) | d734 实际任务：数值/Fubini 73/73 编译、19/19 审计及 551 个所属声明；三个 native 输入资格和 CurrentChen 原对象接收成功；完整闭包 77/81。 |
| [variable-lower-expression-review.json](variable-lower-expression-review.json) | VariableLower 两处最小表达修复的独立源码审查；后续实际编译与 29 声明审计均通过，运行信用见 full81 记录。 |
| [binding003-observed.json](binding003-observed.json)、[resume-20261126-binding003.log](resume-20261126-binding003.log) | fresh003、CurrentChen adoption003 及两条 native 记录重绑均实际通过；PairedV2 原记录保留，无新编译或 loader 调用。 |
| [full81-compile-stage-observed.log](full81-compile-stage-observed.log)、[full81-audit26-observed.json](full81-audit26-observed.json) | 全部 77 个既有缓存通过前置门禁；完整闭包 81/81，77 复用、4 新编译；26/26 审计，19 复用、7 新审计，共 679 个所属声明。观测文件保留阶段当时的导出状态，不能替代最终接收核验。 |

历史 Strip00 单独任务的闭包包含 24 个模块，其中 23 个复用既有对象；目标 Lean 编译耗时 11.078 秒。该次记录只证明编译与对象复用。后续数值/Fubini 首轮任务 `e0cdaba244874eecbfb9bf787ac90367` 曾取得 68 个成功（54 个复用、14 个新编译），另 5 个失败或依赖阻断；[任务回执](numeric-fubini-attempt1-job.json)和[完整日志](numeric-fubini-attempt1.log)保留这段历史诊断。此后逐项修正表达并继续复用成功对象，d734 已达到 73/73 编译、19/19 审计；早期失败不再是当前阻塞。全部 12 个条带块沿用原 witness、checker 和数据。

当前运行及验收状态：

| 验收项 | 状态 |
| --- | --- |
| 53 个前置模块严格编译 | 已成功，后续数值/Fubini 闭包复用其记录。 |
| Strip00，任务 `96d6a29e696b4bfa97d85b22f90822ac` | 历史单独编译已成功；本轮数值审核已完成，见 19 项汇总。 |
| 分析链，任务 `0ecd373efb4d4b44957f05f3416631f8` | 历史阻塞：旧 external snapshot 缺少 TailPropagation，未启动 Lean；记录绑定 `77db7b4…`。d734 已通过独立 native 快照门禁。 |
| 73 个无 native 数值/Fubini 模块 | **73/73 编译通过；19/19 审计通过，共 551 个所属声明。SupportFubini 和 ContinuousFibreFubini 均已实际通过。** |
| 12 个条带检查块及完整证书 | 全部条带块、装配和完整证书已编译；本轮数值审计结果见 19 项汇总。 |
| 补充 native 资格及 P1 物理 payload | 三个 native provider 的 fresh003 资格和快照门禁已通过；未重新编译外部数学。 |
| CurrentChen 历史单模块对象 | adoption003 已实际接收，`new_strict_compile=false`；本轮独立回放与审计也已通过，共 5 个所属声明。 |
| 完整 81 模块闭包 | **81/81**，全部 77 个既有缓存先通过门禁并复用，VariableLower、Enclosure、SetIntegral、Completion 四个模块新编译通过。 |
| VariableLower 表达修复 | 固定候选 `549ea216…` 中已实际编译通过，29 个所属声明审计通过。 |
| 三个上游分析对象的复用 | 三个原 strict 来源已核验；PairedV2 的 schema 2 原记录保留，Bridge 与 FullBuchstab 两条 schema 3 记录实际重绑成功。 |
| 26 模块声明类型、owner、传递公理审核及独立回放 | **26/26 通过，共 679 个所属声明；19 项复用，7 项新完成。** |
| 首次完整证据导出 | 已成功，原 manifest SHA 为 `73179a25…`；完整任务 succeeded / exit 0。 |
| 原 delta 打包 | 已成功，12,157,720 字节，SHA256 `684f34c3…`；见[任务回执](delta-original-pack-job.json)及[打包观测](delta-original-pack-observed.json)。 |
| 无损编码、传回与接收端字节验证、最终交付凭据 | 四页原数据已接收，页及整包 SHA、完整 tar 流、冻结 delta 核验、679 声明及 81 源码身份均已通过；见 acceptance-20261126/acceptance.json。 |
| P2 服务连接与原记录封存 | 已恢复；原 registry、snapshot 和编译日志先封存并独立保存双 SHA，之后才执行固定 checkout。 |

七项新完成审计分别为：

| 模块 | 所属声明数 |
| --- | --- |
| `ImbalancedChen.CurrentChenBuchstabRefinement` | 5 |
| `ImbalancedChen.CurrentPairedBuchstabBridge` | 6 |
| `ImbalancedChen.Certificates.PairedV2FullBuchstab` | 4 |
| `ImbalancedChen.P2PairedFibreBuchstabVariableLower` | 29 |
| `ImbalancedChen.P2PairedSemanticGainEnclosure` | 33 |
| `ImbalancedChen.Certificates.P2SemanticGainSetIntegral` | 44 |
| `ImbalancedChen.P2PairedCertificateCompletion` | 7 |

新审计共 128 个声明，加上 19 项复用审计的 551 个声明，总数为 679。**现场编译、独立审计、首次导出及最终交付验收均已通过。** 本次接收记录绑定完整实际字节及固定提交；本结论不扩展至 P5 算术计数许可或整个 1+1.7482 工程。

## 现有 Buchstab 对象的接入校验

[p27_qualify_native_inputs.py](../../../../verification/part2/p27_qualify_native_inputs.py) 为本入口创建独立输入快照，复用旧环境和原 P6 来源，不改外部数学源码或旧快照。其[独立源码审查](native-adapter-review.json)与 22 项无编译检查已通过；真实对象包已取回并逐项核对；完整 checkpoint 已实际确认不含这三个模块的 eligible provider。两个前置模块改由各自已有的 P6 生产记录校验，TailPropagation 保持其原完整固定回执；d734 已实际通过三个 provider 的资格校验与最终 P2 `ExternalSnapshot.verify`。输入资格本身不授予新的 P2.7 编译、内核重放或数学验收信用。

原 P6 portable 输入已按哈希接收并打包为 [native-inputs.tar.xz](native-inputs.tar.xz)，其 [转运核对](native-transport-verification.json)、[Git 对象核对](native-blob-receipt.json)与[真实包字段审查](native-bundle-review.json)均保留。包内原数学源码和对象未改；运输包的两项 credit 明确为 false。d734 已核对 P2 环境中的 provider、实际导入与运行时；当前 `549ea216…` 的调用方源码已由 fresh003 重新严格绑定，未把旧快照直接当作新源码的验收凭据。

## 已执行流程与单模块对象复用

历史任务 `572afb7f57df4246b428983dce6188fc` 曾在数值阶段以 71/73 停止；其[实际入队命令](queued-resume-command.sh)保留当时安排，不追改为后续未执行的参数。后续 d734 达到 73/73 数值/Fubini、19 项审核及完整闭包 77/81；binding003 完成新的严格复用绑定，任务 `5ad392…` 完成剩余四个模块、26 目标审计及首次完整导出。原 delta 随后已生成，无损重编码、传回和接收端逐字节核验已在本次接续完成。

[CurrentChen 原对象包](currentchen-inputs.tar.xz)保留其原 P6 源码、对象及生产上下文；[转运核对](currentchen-transport-verification.json)、[Git 对象核对](currentchen-blob-receipt.json)与[接收器独立审查](currentchen-adapter-review.json)分别记录字节运输与源码检查。接收器 [adopt_p27_currentchen_cache.py](../../../../verification/part2/adopt_p27_currentchen_cache.py)只接入这一未改源码模块，已逐项重绑实际运行时和 16,623 项原导入 facets，并在 adoption003 保留其他 registry 条目。接收记录明确 `new_strict_compile=false`；该模块随后实际通过独立回放与 5 声明审计，信用来自该审计记录，不以历史对象接收替代审核。

[两处 Lean 表达修复的独立审查](lean-compatibility-review.json)不增加编译信用，相关模块已在后续真实任务中通过。首次完整导出与原 delta 打包均已成功，下述增量交付流程的无损编码、传回与接收核验均已完成；早先的 `supplemental-export-command.sh` 已被替代，不再生成第二份全量导出。

Function/Bounds 的显式 P6 来源扩展另有[独立审查](native-prerequisites-review.json)：29 项针对性测试和真实历史包字段检查通过；原 checkpoint、Tail provider 和 descriptor 门禁保持不变，原 `selected={}` 的结果未被改写。源码审查与 d734 的实际环境资格校验是两类证据，均不单独替代 P2.7 最终数学验收。

## 排序壁的具体坐标归约

P3 参数化表达探针 `67f828f5c16f4dd58ebdeca4c891aa00` 实际以退出码 1 结束，唯一诊断是在 `orderingWallForm_ne_zero` 中仍有 `![0, 0, 0, 1] 3 = 0`。在原简化后增加 `change (1 : ℝ) = 0 at hh` 和 `norm_num at hh`，仅补齐该具体坐标的定义归约。参见 [原始错误日志](p3-expression-probe-before.compile.log)、[探针原源码](p3-expression-probe-before.lean)及[两行修正的独立审查](ordering-wall-review.json)。修复探针 `cdaef8c04ada491abd231363ac6788dc` 实际通过，退出码 0，外层约 3.464 秒、Lean 约 3.376 秒，日志为空且无警告。参见[前后原件字节核对与边界说明](p3-expression-probe-verification.json)。探针使用显式参数化的已有供应结论，不是 P2.7 模块接收；对应 FullCertificate 和 AdoptedUnion 后来已由真实 P2 模块编译通过，其信用来自模块记录。

最终证据将引用固定旧归档中逐字节相同的依赖记录，并完整保留本轮新审核材料及 CurrentChen 接入补充；不再运行一次会重复写出全部旧上下文的补充全量导出。该打包安排不改变任何接收计数或证明信用。

## 增量证据交付入口

[专用打包和接收脚本](../../../../verification/part2/p27_delta_evidence.py)已通过[独立审查](delta-evidence-review.json)：17 项针对性测试及 5 个额外拒绝用例通过。它只复用原始 exporter 的有效接收清单，要求精确的 26 个目标和 81 个项目上下文；旧字节引用必须在接收端从固定 Git 文件流式重读并核对。所有新增审核、完整类型、日志与 CurrentChen 补充保持原字节。首次完整 export、原 delta 打包与接收端核验均已完成；完整接收记录见 `acceptance-20261126/`。打包与接收没有新增编译或内核回放信用。

原 delta 任务 `f2d4f8f6b72547cab22177bc526d4900` 已 exit 0，用时 59.520586754 秒。P2 执行 checkout 为 `ca15b1035ac8fc9be746fe8108f532f73aaaff2d`，全部 81 份源码与冻结工具 SHA 均已匹配。原包为 **12,157,720 字节**，SHA256 为 **`684f34c3019c533b40fa45b960f478ba4ec2eadebfd843efbcc5a745ddf527f5`**，保留 13,463 项旧证据引用、81 项源码引用、3 个 CurrentChen 补充文件，略去 8 个已知 staging aliases。原 export manifest 的独立锚仍为 `73179a250532882aa5a945ba149fb734ee776dd3fdcef5d386af69b6303eca08`。见[原打包任务回执](delta-original-pack-job.json)、[stdout 前缀观测](delta-original-pack-prefix.log)与[打包结果观测](delta-original-pack-observed.json)；前缀文件明确不是整份任务 stdout。

仅改变 XZ 编码的任务 `1a3c03e2c1484ecfad518378837966c3` 及后续只读传页任务均已 succeeded。四个实际数据页按原页 SHA、整包 SHA 与独立 exporter manifest 锚核对，编码前后完整解压 tar 流身份已确认。没有新增 Lean 编译、完整导出或审计。

以下是已完成原 delta 打包的准备入口记录；本轮保留既有原包，不再执行一次：

```sh
bash docs/p2/20261125/p27/prepare-delta-evidence.sh ORIGINAL_MANIFEST_SHA256
```

[该准备命令](prepare-delta-evidence.sh)仅从首次全量导出派生增量包，并保留 CurrentChen 接入材料。原流程若按[恢复步骤](resume-from-d734.md)使用 `next-private-step.sh 0`，其内部完成同一步；本轮两者都不再重跑，以免重复创建同一打包目录。后续仅传输既有原包或通过等字节流核验的重编码结果，传输页数以实际输出为准。以下冻结接收命令已成功执行，结果保存在 `acceptance-20261126/delta-verification.json`：

```sh
python3 -B verification/part2/p27_delta_evidence.py verify P27_COMPLETE.delta.tar.xz \
  --repo . --git-tree FIXED_PUBLICATION_COMMIT \
  --manifest-sha256 ORIGINAL_MANIFEST_SHA256 \
  --output p27-delta-verification.json
```

`ORIGINAL_MANIFEST_SHA256` 必须独立取自原导出任务回执，不能只相信传输包自己的声明。全部 81 个源文件还已与原接收清单、实际编译提交和发布基线逐字节核对，见 `acceptance-20261126/source-identity-verification.json`。

## 已通过的 Fubini 表达修复与历史诊断

`P2PairedSupportFubini.lean` 的修复包括移除两项确实未使用的 simp 参数、以有类型的局部等式归约 `Fin.cons` 的具体坐标、展开原 `tInterval/uInterval` 定义、用 `Measure.volume_eq_prod` 统一同一乘积 Lebesgue 测度的记号，以及在区间重写前进行 β 归约。`P2ContinuousFibreFubini.lean` 随后补齐同类测度与 β 表达，并显式证明两个有类型的向量等式、规范化最后一层 indicator 的 `w ∈ Ioo` 条件。原定理陈述、假设、同 mask 积分域、核及 `K/80` 均保持不变。稿件对应段落已核对，这些诊断均属于 Lean 表达适配；**两个模块均已实际编译通过，且本轮 19 项数值审计已经完成**。

## 历史具体坐标续验与空间恢复

历史任务 `a0f83d2b83a540fdb58ac88d381c86cb` 复用了全部 71 个成功对象，曾在 SupportFubini 的具体坐标归约处停止。[原日志](numeric-fubini-attempt3.log)仅报告展开后的 `Fin.cases` 坐标；当时修正改为三个局部 `rfl` 等式，并在四处原 simp 中使用，详见[局部独立复审](support-fubini-coordinate-review.json)。后续真实诊断又指出两个等式的依赖 motive 未定；补齐三个函数类型注解后，任务 `c3dd9c996b7d4f1e85f1ac3e3d3a1d91` 实际通过 SupportFubini，原失败探针与修复探针也分别复现失败和通过。该历史修复不再 pending；ContinuousFibreFubini 的后续向量与 indicator 修复已在 d734 通过。

P2 曾在可用空间归零后，逐项确认本轮缓存中的 44 个未登记、且在 P2.7 闭包之外的 Winner9 对象具有完全相同的原件。只回收这些复制件，释放 2,063,167,312 字节；原件、当时 71 个成功对象及编译登记均按字节保留，当时可用空间恢复至 2,007,519,232 字节。[恢复回执](duplicate-copy-recovery.json)保留完整复制件/原件映射、SHA 与恢复方法，恢复不需要重新编译。这是历史空间恢复记录，不代表当前可用空间；后续连接恢复另有前述实际观测。

## 2026-11-26 最终接收与范围结论

冻结接收器实际重读 37 份旧归档分片，核对 13,859 个旧成员，解析 13,463 项引用及 81 项源码引用，覆盖 13,978 个原导出成员；3 份 CurrentChen 补充与 8 个已知 staging aliases 的边界保持不变。离线声明检查器重建全部 26 份审计，得到 679 个唯一所属声明，无重复 owner、无未选择模块。允许的传递公理仅为 `propext`、`Classical.choice`、`Quot.sound`。

P2.7 的分析义务至此闭合：原完整常数增益积分区间、实际网格及支撑并集积分、真实 Buchstab 增量与同域半基线差，以及稿件严格下界。此验收不授予 P1/P5 算术父项注入许可，不关闭其他 P2 节点或整篇主定理。旧 exporter 的 `full_p2_complete: false` 保留。
