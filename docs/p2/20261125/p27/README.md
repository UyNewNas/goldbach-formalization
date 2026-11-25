# P2.7 same-mask-v2 配对证书接收说明

**当前验收状态：pending。** 源码基线为已发布快照 `a00a0bc8093429b73c411ec4913d23adb829aeb8`；证明源码为 `77db7b4250077ba9bd2cafb14dfa51b5a2e6e549` 加 `997e16dcf07ac32eeb2804cfb5280b8d890e44e5` 的注释修正。目前 53 个前置模块及 Strip00 已编译成功；Strip00 尚未独立回放。分析任务因旧 external snapshot 缺少 `MathlibNt.SieveTheory.LiLiuBuchstabTailPropagation`，在 `mark_project_nodes` 前置验证阶段失败，未启动 Lean。本轮完整证书的编译、独立回放及声明/公理审核仍待验收。

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

Strip00 本轮闭包包含 24 个模块，其中 23 个复用既有对象；目标 Lean 编译耗时 11.078 秒。以上是编译与对象复用记录，不包含独立 replay。73 个无需 native 根的数值/Fubini 模块已入队继续验证（任务 `e0cdaba244874eecbfb9bf787ac90367`），目前不记为该 73 模块整体通过。

当前运行及验收状态：

| 验收项 | 状态 |
| --- | --- |
| 53 个前置模块严格编译 | 编译成功；独立回放/审核 pending。 |
| Strip00，任务 `96d6a29e696b4bfa97d85b22f90822ac` | 编译成功；独立 replay / 声明审核 pending。 |
| 分析链，任务 `0ecd373efb4d4b44957f05f3416631f8` | 前置验证失败：旧 external snapshot 缺少 TailPropagation，未启动 Lean；任务记录绑定 `77db7b4…`。 |
| 73 个无 native 数值/Fubini 模块的继续验证 | 已入队：`e0cdaba244874eecbfb9bf787ac90367`；整体通过状态 pending。 |
| 12 个条带检查块及完整证书 | 除上述 Strip00 编译记录外，完整验收仍 pending。 |
| 补充 native 资格及 P1 物理 payload | 准备中；资格审查与实际接收结果 pending。 |
| 26 模块声明类型、owner、传递公理审核及独立回放 | pending。 |
| 最终源码/对象/依赖哈希绑定与正式接收凭据 | pending，待实际记录补入。 |

**最终验收结果：pending；本快照不标记 accepted。** 后续更新本节时应引用实际运行记录及其绑定的提交，不以源码评审或历史叶模块凭据替代本轮结果。

## 现有 Buchstab 对象的接入校验

[p27_qualify_native_inputs.py](../../../../verification/part2/p27_qualify_native_inputs.py) 为本入口创建独立输入快照，复用旧环境和原 P6 来源，不改外部数学源码或旧快照。其[独立源码审查](native-adapter-review.json)与 22 项无编译检查已通过；真实对象包、完整 checkpoint provider 和最终 `ExternalSnapshot.verify` 仍待实际执行。输入资格不等于 P2.7 编译、内核重放或数学验收。

原 P6 portable 输入已按哈希接收并打包为 [native-inputs.tar.xz](native-inputs.tar.xz)，其 [转运核对](native-transport-verification.json)、[Git 对象核对](native-blob-receipt.json)与[真实包字段审查](native-bundle-review.json)均保留。包内原数学源码和对象未改；两项 credit 明确为 false。P2 环境中的 provider、实际导入与运行时重绑仍须通过独立快照门禁。
