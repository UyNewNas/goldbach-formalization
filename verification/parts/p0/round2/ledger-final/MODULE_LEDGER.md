# Part 0 逐模块验证台账（增量快照）

快照：`2026-10-12T05:48:47.078246+00:00`。

声明的集成 SHA：`278f949444748a30b5165ff47bfa283ab0bad0d8`；树：`9723353ffbda12028cdd9e64e36ccb3ac8fbd4b5`。当前本地集成 checkout 为 `278f949444748a30b5165ff47bfa283ab0bad0d8`，是否等于该声明：`True`。

本单共 **28 个生产模块**，按配置与匹配验证门实际接收 **11 个**。接收配置本身不使验证通过；必须匹配当前源码及完整通过回执。其余保留候选身份。

本次仅读取现存记录、源码和配置，没有运行 Lean、Lake、leanchecker 或 CI。完整项目构建、最终项目内核/公理门与无 hLower/hUpper 的最终入口仍未完成。输出目录名 ledger-final 不代表证明目标已经完成。

| 所属 | 模块 | 编译 | 生产重放 | 公理审计 | 接收 |
|---|---|---|---|---|---|
| P1 | `ImbalancedChen.ActualSelectedPrefixLowerCellSum` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P1 | `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P1 | `ImbalancedChen.HistoricalPrefixCertificate` | strict / trust 0 通过 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P1 | `ImbalancedChen.OrdinaryLowerFourFrontier` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P2 | `ImbalancedChen.Certificates.AboveMuSecondCoarse` | strict / trust 0 通过 | 原装内核重放通过 | 通过：71 个 defining-module 声明 | 已接收 5e31713690daba5ff926da61875a99171718fd1d |
| P2 | `ImbalancedChen.Certificates.PairedCertificateChecker` | strict / trust 0 通过 | 原装内核重放通过 | 通过：58 个 defining-module 声明 | 已接收 c9f407efe66240c08c2e8a678330ba7b98b74db5 |
| P2 | `ImbalancedChen.Certificates.PairedFibreIntegral` | strict / trust 0 通过 | 原装内核重放通过 | 通过：13 个 defining-module 声明 | 已接收 c9f407efe66240c08c2e8a678330ba7b98b74db5 |
| P2 | `ImbalancedChen.Certificates.PairedV2` | strict / trust 0 通过 | 原装内核重放通过 | 通过：46 个 defining-module 声明 | 已接收 c9f407efe66240c08c2e8a678330ba7b98b74db5 |
| P2 | `ImbalancedChen.Certificates.PairedV2Data` | strict / trust 0 通过 | 原装内核重放通过 | 通过：18 个 defining-module 声明 | 已接收 c9f407efe66240c08c2e8a678330ba7b98b74db5 |
| P2 | `ImbalancedChen.Certificates.RationalLogCertificate` | strict / trust 0 通过 | 原装内核重放通过 | 通过：47 个 defining-module 声明 | 已接收 c9f407efe66240c08c2e8a678330ba7b98b74db5 |
| P3 | `ImbalancedChen.Part3CurrentLowerDistribution` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P3 | `ImbalancedChen.Part3DistributionTargets` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P3 | `ImbalancedChen.Part3LongSlotDistribution` | strict / trust 0 通过 | 原装内核重放通过 | 通过：35 个 defining-module 声明 | 已接收 5e31713690daba5ff926da61875a99171718fd1d |
| P3 | `ImbalancedChen.Part3LongSlotNormalization` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P3 | `ImbalancedChen.Part3PrimeAPDistribution` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P3 | `ImbalancedChen.Part3RoughAuxiliarySW` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P3 | `ImbalancedChen.Part3RoughAuxiliarySWNormalization` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P4-A | `ImbalancedChen.ActualUpperDensityAssembly` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P4-A | `ImbalancedChen.ActualUpperPolicyDensity` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P4-B | `ImbalancedChen.RealPhysicalUpperWeightBridge` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P4-B | `ImbalancedChen.RealUpperCountingAssembly` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P4-A | `ImbalancedChen.UpperCoefficientPerturbation` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P5 | `ImbalancedChen.CurrentChenBuchstabRefinement` | strict / trust 0 通过 | 原装内核重放通过 | 通过：5 个 defining-module 声明 | 已接收 30fdb230428e91d7eb5deb8deb5cbe3fdc113ceb |
| P5 | `ImbalancedChen.CurrentChenLowerScale` | strict / trust 0 通过 | 原装内核重放通过 | 通过：5 个 defining-module 声明 | 已接收 278f949444748a30b5165ff47bfa283ab0bad0d8 |
| P5 | `ImbalancedChen.CurrentChenMeanLedger` | strict / trust 0 通过 | 原装内核重放通过 | 通过：93 个 defining-module 声明 | 已接收 278f949444748a30b5165ff47bfa283ab0bad0d8 |
| P0 | `ImbalancedChen.CurrentPairedBuchstabBridge` | strict / trust 0 通过 | 原装内核重放通过 | 通过：2 个 defining-module 声明 | 已接收 c9f407efe66240c08c2e8a678330ba7b98b74db5 |
| P5 | `ImbalancedChen.CurrentChenInitialSource` | 当前源失败 | 无当前源完成回执 | 无当前源完整审计 | 候选 |
| P5 | `ImbalancedChen.CurrentChenInitialMean` | 无当前源完成回执 | 无当前源完成回执 | 无当前源完整审计 | 候选 |

## 类型与审计证据等级

`source-theorem-types.json` / `SOURCE_THEOREM_TYPES.md` 收录 267 个当前源码 theorem/lemma 声明头。`compiler-declarations.json` / `COMPILER_TYPES.md` 收录 393 个有完成审计证据的编译器声明类型，包括 private/generated 声明。两种来源明确区分。

新审计只有完成 strict / trust 0、source/import 对象前后一致、DECL/MODULE/COUNT 全部吻合、实际审计源码包含 defining-module 枚举及 unsafe/axiom/传递公理检查，才可绑定生产模块。审计导入的主 .olean 必须与当前源码成功编译对象相同；存在的 .server/.private 也按记录比较前后哈希。历史已验证回执保留原证据等级，没有补造旧记录不具备的 import 捕获字段。

## 逐模块源码与未闭合输入

### P1 — `ImbalancedChen.ActualSelectedPrefixLowerCellSum`

文件：`ImbalancedChen/ActualSelectedPrefixLowerCellSum.lean`；接收 Part：P1, P2, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | 尚未固定，按真实本地候选哈希追踪 |
| 原始 blob | `64e73f036cd309512ea5513377cb0528e65ed524` |
| 原始 SHA256 | `48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714` |
| 当前 blob | `64e73f036cd309512ea5513377cb0528e65ed524` |
| 当前 SHA256 | `48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714` |
| 当前固定源码提交 | `70ad4d737a2ff4a77413a5975af2fb41bdfb7d66` |

实际选中前缀的有限下界 cell-sum 恒等式；不同于完整解析极限。

类型：源码 theorem/lemma 5 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T05:22:01+00:00`；其中早期验证待办以本节当前门状态为准）：

- 固定提交 70ad4d737a2ff4a77413a5975af2fb41bdfb7d66 已按真实源码接收；本目标的严格编译、生产内核重放和完整所属声明公理审计尚待完成。
- 采用的历史选择/共同网格及实际积分极限尚未闭合。

### P1 — `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`

文件：`ImbalancedChen/ActualSelectedPrefixLowerOwnCubeIntegral.lean`；接收 Part：P1, P2, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | 尚未固定，按真实本地候选哈希追踪 |
| 原始 blob | `6a535380f1bb4074e06ff8ce4180eaae63d2e9fe` |
| 原始 SHA256 | `c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1` |
| 当前 blob | `6a535380f1bb4074e06ff8ce4180eaae63d2e9fe` |
| 当前 SHA256 | `c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1` |
| 当前固定源码提交 | `70ad4d737a2ff4a77413a5975af2fb41bdfb7d66` |

实际选中前缀在自身 Ico 网格单元上的有限积分身份。

类型：源码 theorem/lemma 5 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T05:22:01+00:00`；其中早期验证待办以本节当前门状态为准）：

- 固定提交 70ad4d737a2ff4a77413a5975af2fb41bdfb7d66 已按真实源码接收；本目标的严格编译、生产内核重放和完整所属声明公理审计尚待完成。
- 不能据此替代另行报告、尚未取得源码的“继承前层第五层积分”候选。
- 完整历史第五层 Tendsto、后续阶段与 adopted 数值表实际适用性仍未闭合。

### P1 — `ImbalancedChen.HistoricalPrefixCertificate`

文件：`ImbalancedChen/HistoricalPrefixCertificate.lean`；接收 Part：P1, P2, P4-A, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | 尚未固定，按真实本地候选哈希追踪 |
| 原始 blob | `7507cc1734d4f8ef5c7653f4c7bf46d8e7fc668a` |
| 原始 SHA256 | `347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1` |
| 当前 blob | `7507cc1734d4f8ef5c7653f4c7bf46d8e7fc668a` |
| 当前 SHA256 | `347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1` |
| 当前固定源码提交 | `70ad4d737a2ff4a77413a5975af2fb41bdfb7d66` |

有理历史证书数据和第三至第五层共同网格有限构造；第四/第五层沿用实际祖先旧 cap；levelCheck 检查旧 cap ≤ 新 cap。

类型：源码 theorem/lemma 33 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：production_kernel_replay, owned_declaration_axiom_audit。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1` | 0 | `/workspace/scratch/127408f63891/lean-runtime/logs/closure/ImbalancedChen.HistoricalPrefixCertificate.log` |

接口审查及未闭合输入（审查时刻 `2026-10-12T05:22:01+00:00`；其中早期验证待办以本节当前门状态为准）：

- 固定提交 70ad4d737a2ff4a77413a5975af2fb41bdfb7d66 已按真实源码接收；本目标的严格编译、生产内核重放和完整所属声明公理审计尚待完成。
- 完整 adopted 策略、物理合法性/支持、compiler 扰动预算、真实渐近积分和完整 U 仍未闭合。

### P1 — `ImbalancedChen.OrdinaryLowerFourFrontier`

文件：`ImbalancedChen/OrdinaryLowerFourFrontier.lean`；接收 Part：P1, P2, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | 尚未固定，按真实本地候选哈希追踪 |
| 原始 blob | `05f0e3758e0b6fa0cfa6b3002e9c61ce164489ae` |
| 原始 SHA256 | `97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8` |
| 当前 blob | `05f0e3758e0b6fa0cfa6b3002e9c61ce164489ae` |
| 当前 SHA256 | `97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8` |
| 当前固定源码提交 | `70ad4d737a2ff4a77413a5975af2fb41bdfb7d66` |

普通第四层的真实有限前沿与积分辅助叶；保留原历史/网格对象。

类型：源码 theorem/lemma 9 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T05:22:01+00:00`；其中早期验证待办以本节当前门状态为准）：

- 固定提交 70ad4d737a2ff4a77413a5975af2fb41bdfb7d66 已按真实源码接收；本目标的严格编译、生产内核重放和完整所属声明公理审计尚待完成。
- 完整采用策略、合法性/支持、网格极限与实际下界积分对接仍由 P1 供给。

### P2 — `ImbalancedChen.Certificates.AboveMuSecondCoarse`

文件：`ImbalancedChen/Certificates/AboveMuSecondCoarse.lean`；接收 Part：P1, P2, P4-A。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` |
| 原始 blob | `ec2814fba4aa3ddc204847fc34a9f1f2f052a358` |
| 原始 SHA256 | `84d3d5cccd9043568523780a4f9f08a70f78ccae997b2748d74f7edf16c1b89f` |
| 当前 blob | `c2d0b52b285cbc584b64e07eebd7f8593459491d` |
| 当前 SHA256 | `85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2` |
| 当前固定源码提交 | `5e31713690daba5ff926da61875a99171718fd1d` |

第二上界积分的两个实际 chart 积分粗界候选；系数、积分定义保持原样。

类型：源码 theorem/lemma 28 个；编译器全部声明 71 个，其中匹配源码 theorem/lemma 28 个。

当前尚未完成的验证门：该生产模块的三个门均有匹配回执。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `84d3d5cccd9043568523780a4f9f08a70f78ccae997b2748d74f7edf16c1b89f` | 1 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T045324945943Z-compile-ImbalancedChen.Certificates.AboveMuSecondCoarse.log` |
| compile strict | `85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T045717067800Z-compile-ImbalancedChen.Certificates.AboveMuSecondCoarse.log` |
| replay  | `85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T050358252186Z-replay-ImbalancedChen.Certificates.AboveMuSecondCoarse.log` |

保留的第一处真实诊断：

```text
/workspace/scratch/535d89efd063/p0-round2/validation/ImbalancedChen/Certificates/AboveMuSecondCoarse.lean:299:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (x : ℝ) in 0..1, ?m.89 - id x ∂?m.103
in the target expression
  ∫ (v : ℝ) in 0..1, 1 - v = 1 / 2

C : ℝ
⊢ ∫ (v : ℝ) in 0..1, 1 - v = 1 / 2
```

公理回执：`/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T050100871749Z-compile-verification.parts.p0.CoarseAudit.log`；绑定方法：recorded audit import objects before/after; primary object matched to current-source strict compile。

接口审查及未闭合输入（审查时刻 `2026-10-12T05:10:40.928907+00:00`；其中早期验证待办以本节当前门状态为准）：

- Physical-domain integral change of variables, coverage and boundary treatment remain separate; the pullback identity alone is pointwise algebra.
- Identification with the actual ordinary-sieve density, actual old-tree construction and the same arithmetic rho is not supplied.
- Rough-cutoff tail, strict finite buffers and limit order remain inputs to P4-A/P4-B.
- The coarse and fine-grid bounds estimate the same quantity and must not be added. No full K or hUpper supplier is claimed.

### P2 — `ImbalancedChen.Certificates.PairedCertificateChecker`

文件：`ImbalancedChen/Certificates/PairedCertificateChecker.lean`；接收 Part：P2, P0。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` |
| 原始 blob | `c6756844009afff7c0064961ddb7c013e62e9751` |
| 原始 SHA256 | `e3bed1eea4482024542b8a64ef6436de350728f190944329d7c0a051895096a3` |
| 当前 blob | `825ee28f923e5ef5144a3cf0f7eb263d45016319` |
| 当前 SHA256 | `454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c` |
| 当前固定源码提交 | `c9f407efe66240c08c2e8a678330ba7b98b74db5` |

每行有限检查通过则给出上述真实积分的有理上下界；有限族总和接口仍需要每行接受。

类型：源码 theorem/lemma 2 个；编译器全部声明 58 个，其中匹配源码 theorem/lemma 2 个。

当前尚未完成的验证门：该生产模块的三个门均有匹配回执。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `e3bed1eea4482024542b8a64ef6436de350728f190944329d7c0a051895096a3` | 1 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T034110479360Z-compile-ImbalancedChen.Certificates.PairedCertificateChecker.log` |
| compile strict | `a46bcd3fcb6c1fac87f76485ebf8c8625e3150aa32ee008c37c6dd8a44a50cf7` | 1 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T034648067908Z-compile-ImbalancedChen.Certificates.PairedCertificateChecker.log` |
| compile strict | `454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T035626620753Z-compile-ImbalancedChen.Certificates.PairedCertificateChecker.log` |
| replay  | `454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T044030095478Z-replay-ImbalancedChen.Certificates.PairedCertificateChecker.log` |

保留的第一处真实诊断：

```text
/workspace/scratch/535d89efd063/p0-round2/validation/ImbalancedChen/Certificates/PairedCertificateChecker.lean:28:8: error(lean.inferBinderTypeFailed): Failed to infer type of binder `upper`
```

公理回执：`/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T042301965323Z-compile-verification.parts.p0.CertificatesFirstCellAudit.log`；绑定方法：recorded audit import objects before/after; primary object matched to current-source strict compile。

接口审查及未闭合输入（审查时刻 `2026-10-12T04:59:00.605345+00:00`；其中早期验证待办以本节当前门状态为准）：

- All 17572 adopted rows: this batch proves only the first row, with independently weaker bounds, not its stored Q160 interval.
- P1 actual parent/mask coverage, legality, support and identification with the full construction.
- P3 actual arithmetic distribution/error and P4-A same-rho density.
- Actual full K, c, hLower and hUpper suppliers.

### P2 — `ImbalancedChen.Certificates.PairedFibreIntegral`

文件：`ImbalancedChen/Certificates/PairedFibreIntegral.lean`；接收 Part：P2, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` |
| 原始 blob | `be638197eccf070b015e5c60af58cee386db40fc` |
| 原始 SHA256 | `aa2d5af80ff2b426c91b6ca0b4e7819cb2e63a0d0b74b6ebe122e713638c4266` |
| 当前 blob | `9c9243c22c6359a93169f43f1e2155b6e1a19ecd` |
| 当前 SHA256 | `d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4` |
| 当前固定源码提交 | `c9f407efe66240c08c2e8a678330ba7b98b74db5` |

真实四重迭代积分 K/80 * ∫ 1/(t*u*z^2*w) 的闭式：K/80*log(tr/tl)*log(ur/ul)*(1/a-(1+log(Z/a))/Z)。

类型：源码 theorem/lemma 7 个；编译器全部声明 13 个，其中匹配源码 theorem/lemma 7 个。

当前尚未完成的验证门：该生产模块的三个门均有匹配回执。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `aa2d5af80ff2b426c91b6ca0b4e7819cb2e63a0d0b74b6ebe122e713638c4266` | 1 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T031937057113Z-compile-ImbalancedChen.Certificates.PairedFibreIntegral.log` |
| compile strict | `d768d55606618d8f569ecdec2cff27e69eb63882937625d403a24fefcd03d7ba` | 1 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T033520984504Z-compile-ImbalancedChen.Certificates.PairedFibreIntegral.log` |
| compile strict | `638e887a08168e9d1339780c84ad6c8bc03cc36c8f972767cc291cb424572b44` | 1 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T033716349243Z-compile-ImbalancedChen.Certificates.PairedFibreIntegral.log` |
| compile strict | `d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T033912589093Z-compile-ImbalancedChen.Certificates.PairedFibreIntegral.log` |
| replay  | `d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T043818118144Z-replay-ImbalancedChen.Certificates.PairedFibreIntegral.log` |

保留的第一处真实诊断：

```text
/workspace/scratch/535d89efd063/p0-round2/validation/ImbalancedChen/Certificates/PairedFibreIntegral.lean:45:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Real.log (z / a)
in the target expression
  Real.instAddCommGroup = Real.normedAddCommGroup.toAddCommGroup

case e'_4
a z : ℝ
ha : 0 < a
hz : 0 < z
hd :
  HasDerivAt ((fun x => ((fun x => 1) + Real.log) x - Real.log a) / id)
    (((0 + z⁻¹) * id z - (((fun x => 1) + Real.log) z - Real.log a) * 1) / id z ^ 2) z
⊢ Real.instAddCommGroup = Real.normedAddCommGroup.toAddCommGroup
```

公理回执：`/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T042301965323Z-compile-verification.parts.p0.CertificatesFirstCellAudit.log`；绑定方法：recorded audit import objects before/after; primary object matched to current-source strict compile。

接口审查及未闭合输入（审查时刻 `2026-10-12T04:59:00.605345+00:00`；其中早期验证待办以本节当前门状态为准）：

- All 17572 adopted rows: this batch proves only the first row, with independently weaker bounds, not its stored Q160 interval.
- P1 actual parent/mask coverage, legality, support and identification with the full construction.
- P3 actual arithmetic distribution/error and P4-A same-rho density.
- Actual full K, c, hLower and hUpper suppliers.

### P2 — `ImbalancedChen.Certificates.PairedV2`

文件：`ImbalancedChen/Certificates/PairedV2.lean`；接收 Part：P2, P5, P4-A。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` |
| 原始 blob | `69ed77e5bb63b34c447d5da409660ad196b74559` |
| 原始 SHA256 | `e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7` |
| 当前 blob | `69ed77e5bb63b34c447d5da409660ad196b74559` |
| 当前 SHA256 | `e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7` |
| 当前固定源码提交 | `c9f407efe66240c08c2e8a678330ba7b98b74db5` |

实际首格检查、积分界和 residual ≥ 7/3 的支撑几何候选。

类型：源码 theorem/lemma 9 个；编译器全部声明 46 个，其中匹配源码 theorem/lemma 9 个。

当前尚未完成的验证门：该生产模块的三个门均有匹配回执。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T041755313931Z-compile-ImbalancedChen.Certificates.PairedV2.log` |
| replay  | `e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T044348207315Z-replay-ImbalancedChen.Certificates.PairedV2.log` |

公理回执：`/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T042301965323Z-compile-verification.parts.p0.CertificatesFirstCellAudit.log`；绑定方法：recorded audit import objects before/after; primary object matched to current-source strict compile。

接口审查及未闭合输入（审查时刻 `2026-10-12T04:59:00.605345+00:00`；其中早期验证待办以本节当前门状态为准）：

- All 17572 adopted rows: this batch proves only the first row, with independently weaker bounds, not its stored Q160 interval.
- P1 actual parent/mask coverage, legality, support and identification with the full construction.
- P3 actual arithmetic distribution/error and P4-A same-rho density.
- Actual full K, c, hLower and hUpper suppliers.

### P2 — `ImbalancedChen.Certificates.PairedV2Data`

文件：`ImbalancedChen/Certificates/PairedV2Data.lean`；接收 Part：P2, P0。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` |
| 原始 blob | `ce51d921db64a1d1d0b517c874733d04b7a54d1e` |
| 原始 SHA256 | `a9d46c8bbdbb8cea97d41f47476465912f6370bcf99452bfa7e3e9fc1f6cc17f` |
| 当前 blob | `d7a62f959d7c575a40b0ed623956c71fa865e2fd` |
| 当前 SHA256 | `a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82` |
| 当前固定源码提交 | `c9f407efe66240c08c2e8a678330ba7b98b74db5` |

same-mask-v2 实际首格 (422,510) 数据；不是 17,572 格完整已证数据集。

类型：源码 theorem/lemma 0 个；编译器全部声明 18 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：该生产模块的三个门均有匹配回执。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `a9d46c8bbdbb8cea97d41f47476465912f6370bcf99452bfa7e3e9fc1f6cc17f` | 1 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T040651498535Z-compile-ImbalancedChen.Certificates.PairedV2Data.log` |
| compile strict | `a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T041421185780Z-compile-ImbalancedChen.Certificates.PairedV2Data.log` |
| replay  | `a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T044149725484Z-replay-ImbalancedChen.Certificates.PairedV2Data.log` |

保留的第一处真实诊断：

```text
/workspace/scratch/535d89efd063/p0-round2/validation/ImbalancedChen/Certificates/PairedV2Data.lean:42:54: error: unexpected identifier; expected '}'
```

公理回执：`/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T042301965323Z-compile-verification.parts.p0.CertificatesFirstCellAudit.log`；绑定方法：recorded audit import objects before/after; primary object matched to current-source strict compile。

接口审查及未闭合输入（审查时刻 `2026-10-12T04:59:00.605345+00:00`；其中早期验证待办以本节当前门状态为准）：

- All 17572 adopted rows: this batch proves only the first row, with independently weaker bounds, not its stored Q160 interval.
- P1 actual parent/mask coverage, legality, support and identification with the full construction.
- P3 actual arithmetic distribution/error and P4-A same-rho density.
- Actual full K, c, hLower and hUpper suppliers.

### P2 — `ImbalancedChen.Certificates.RationalLogCertificate`

文件：`ImbalancedChen/Certificates/RationalLogCertificate.lean`；接收 Part：P2, P0。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` |
| 原始 blob | `24078c8167f5b4baff5e3af02a85aefd3cdb8284` |
| 原始 SHA256 | `525d4eb7e87932aef7c2ecee816c8f1eb3dee5fcfc679c275444e278b06094c2` |
| 当前 blob | `354507bee23c4f7a8f3e463b6d3fda0f52db77c6` |
| 当前 SHA256 | `4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22` |
| 当前固定源码提交 | `c9f407efe66240c08c2e8a678330ba7b98b74db5` |

有限有理对数检查器与实际 Real.log 上下界的 soundness。

类型：源码 theorem/lemma 3 个；编译器全部声明 47 个，其中匹配源码 theorem/lemma 3 个。

当前尚未完成的验证门：该生产模块的三个门均有匹配回执。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `525d4eb7e87932aef7c2ecee816c8f1eb3dee5fcfc679c275444e278b06094c2` | 1 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T031521114553Z-compile-ImbalancedChen.Certificates.RationalLogCertificate.log` |
| compile strict | `4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T031840791785Z-compile-ImbalancedChen.Certificates.RationalLogCertificate.log` |
| replay  | `4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T043714705523Z-replay-ImbalancedChen.Certificates.RationalLogCertificate.log` |

保留的第一处真实诊断：

```text
/workspace/scratch/535d89efd063/p0-round2/validation/ImbalancedChen/Certificates/RationalLogCertificate.lean:66:20: error: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

公理回执：`/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T042301965323Z-compile-verification.parts.p0.CertificatesFirstCellAudit.log`；绑定方法：recorded audit import objects before/after; primary object matched to current-source strict compile。

接口审查及未闭合输入（审查时刻 `2026-10-12T04:59:00.605345+00:00`；其中早期验证待办以本节当前门状态为准）：

- All 17572 adopted rows: this batch proves only the first row, with independently weaker bounds, not its stored Q160 interval.
- P1 actual parent/mask coverage, legality, support and identification with the full construction.
- P3 actual arithmetic distribution/error and P4-A same-rho density.
- Actual full K, c, hLower and hUpper suppliers.

### P3 — `ImbalancedChen.Part3CurrentLowerDistribution`

文件：`ImbalancedChen/Part3CurrentLowerDistribution.lean`；接收 Part：P1, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `64598da177adf861df3763d7c465ff941388b6d6` |
| 原始 blob | `bd89bc32f6657d03a727adb4dcfccb9feaf4a52a` |
| 原始 SHA256 | `a78bb4051c70e17d2b954d3c043af40754dfb1b37b0e42c60dd117c75a5c107d` |
| 当前 blob | `bd89bc32f6657d03a727adb4dcfccb9feaf4a52a` |
| 当前 SHA256 | `a78bb4051c70e17d2b954d3c043af40754dfb1b37b0e42c60dd117c75a5c107d` |
| 当前固定源码提交 | `64598da177adf861df3763d7c465ff941388b6d6` |

实际 Y3–Y6 的完整 quotient 模数 p*e 或 p1*p2*e 在 cap 内时的误差；B 在 epsilon 之前统一选择。

类型：源码 theorem/lemma 7 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T03:56:28.674321+00:00`；其中早期验证待办以本节当前门状态为准）：

- PrimeAPDistribution 及共享闭包后的本模块显式验证。
- P1 实际模数 cap、实际选盒系数和行统一约束；P5 真实均值误差对接。

### P3 — `ImbalancedChen.Part3DistributionTargets`

文件：`ImbalancedChen/Part3DistributionTargets.lean`；接收 Part：P1, P4-A, P4-B, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `64598da177adf861df3763d7c465ff941388b6d6` |
| 原始 blob | `30d4aa75c285fccae2f56562a26c6e2ecbf03fb4` |
| 原始 SHA256 | `b11099467fa40c9975e4f76afb29cbff95923c81c3938b1b250769c62c1cb490` |
| 当前 blob | `30d4aa75c285fccae2f56562a26c6e2ecbf03fb4` |
| 当前 SHA256 | `b11099467fa40c9975e4f76afb29cbff95923c81c3938b1b250769c62c1cb490` |
| 当前固定源码提交 | `64598da177adf861df3763d7c465ff941388b6d6` |

固定实际 medium/prime-product 分布目标与量词；定义目标不等于证明目标。

类型：源码 theorem/lemma 0 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T03:56:28.674321+00:00`；其中早期验证待办以本节当前门状态为准）：

- 显式验证依赖闭合。
- 实际完整模数范围的 medium/双长变量分布与所需 uniform rough/Möbius SW。

### P3 — `ImbalancedChen.Part3LongSlotDistribution`

文件：`ImbalancedChen/Part3LongSlotDistribution.lean`；接收 Part：P3, P4-B, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `64598da177adf861df3763d7c465ff941388b6d6` |
| 原始 blob | `a41dc28e862f2f74bfa8719bc8b41141812f0f1d` |
| 原始 SHA256 | `f8054e4b422c5a62bfc39021aa5e6ce978d6aca83bfbc81990d35a53bdd557b5` |
| 当前 blob | `13288c1122f26135644bbd2c04f731f993ffa058` |
| 当前 SHA256 | `67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e` |
| 当前固定源码提交 | `6d1e5c4710a66f68fd101d0b40b5514bbbba4919` |

未筛选、无相位整数长变量 AP 误差 ≤ 2*||alpha||_1*||rho||_1 的有限恒等/界。

类型：源码 theorem/lemma 12 个；编译器全部声明 35 个，其中匹配源码 theorem/lemma 12 个。

当前尚未完成的验证门：该生产模块的三个门均有匹配回执。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `f8054e4b422c5a62bfc39021aa5e6ce978d6aca83bfbc81990d35a53bdd557b5` | 1 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T032009180679Z-compile-ImbalancedChen.Part3LongSlotDistribution.log` |
| compile strict | `67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T050744682383Z-compile-ImbalancedChen.Part3LongSlotDistribution.log` |
| replay  | `67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T051224325996Z-replay-ImbalancedChen.Part3LongSlotDistribution.log` |

保留的第一处真实诊断：

```text
/workspace/scratch/535d89efd063/p0-round2/validation/ImbalancedChen/Part3LongSlotDistribution.lean:177:4: error: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
```

公理回执：`/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T050947421966Z-compile-verification.parts.p0.LongSlotAudit.log`；绑定方法：recorded audit import objects before/after; primary object matched to current-source strict compile。

接口审查及未闭合输入（审查时刻 `2026-10-12T05:15:39.013346+00:00`；其中早期验证待办以本节当前门状态为准）：

- Actual rough/prime coefficients, phases and medium/two-long-variable distribution are not supplied.
- Same-rho realPhysicalDistributionError and normalization adapters remain separate.

### P3 — `ImbalancedChen.Part3LongSlotNormalization`

文件：`ImbalancedChen/Part3LongSlotNormalization.lean`；接收 Part：P3, P4-B, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `64598da177adf861df3763d7c465ff941388b6d6` |
| 原始 blob | `3e9aa6a43744d43e38d705d754963dba53e657e6` |
| 原始 SHA256 | `ca4e4d237bb4a5d21f72af3223001621902d6763d0b7ef1f423f532fd94f69fc` |
| 当前 blob | `3e9aa6a43744d43e38d705d754963dba53e657e6` |
| 当前 SHA256 | `ca4e4d237bb4a5d21f72af3223001621902d6763d0b7ef1f423f532fd94f69fc` |
| 当前固定源码提交 | `64598da177adf861df3763d7c465ff941388b6d6` |

长变量有限误差在 M*D ≤ N^theta、theta<1 条件下的 uniform 归一化。

类型：源码 theorem/lemma 2 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T03:56:28.674321+00:00`；其中早期验证待办以本节当前门状态为准）：

- LongSlotDistribution 修复及共享 BoundaryArbitraryLog 依赖闭合后的显式验证。
- P1 实际系数/参数满足该界；实际筛选/相位分布输入仍需另行证明。

### P3 — `ImbalancedChen.Part3PrimeAPDistribution`

文件：`ImbalancedChen/Part3PrimeAPDistribution.lean`；接收 Part：P3, P4-B, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `64598da177adf861df3763d7c465ff941388b6d6` |
| 原始 blob | `8ade723b6d245a1e98bb2fa48096617702a6bbff` |
| 原始 SHA256 | `ac752383a4691d337ba1528078209efda182da5141d0f6a524eeddbfc081b6a3` |
| 当前 blob | `2d761133b313302ab3a89ae906eb6944037a093d` |
| 当前 SHA256 | `55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc` |
| 当前固定源码提交 | `7d70a2545fd819706e473eb41e4d430ad19119d8` |

实际素数 li 中心误差、共同区间、移动剩余类和有符号有界权的平方根 BV 接口。7d70 修复两项三角不等式。

类型：源码 theorem/lemma 13 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T03:56:28.674321+00:00`；其中早期验证待办以本节当前门状态为准）：

- 7d70 固定更新仍为未编译候选，不能沿用旧源验证状态。
- 完整实际大模数分布并不由普通平方根 BV 取代。

### P3 — `ImbalancedChen.Part3RoughAuxiliarySW`

文件：`ImbalancedChen/Part3RoughAuxiliarySW.lean`；接收 Part：P3, P4-B, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `7d70a2545fd819706e473eb41e4d430ad19119d8` |
| 原始 blob | `7ac03bfc01b00b228fb108bf1186ef45302b8344` |
| 原始 SHA256 | `d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8` |
| 当前 blob | `7ac03bfc01b00b228fb108bf1186ef45302b8344` |
| 当前 SHA256 | `d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8` |
| 当前固定源码提交 | `7d70a2545fd819706e473eb41e4d430ad19119d8` |

复粗数系数的辅助互素移除误差 ≤ 2*tau(k)*H/z，以及覆盖 q>H 的粗大模数 envelope；S⊆Ioc 0 H 中 H 是绝对上端点。

类型：源码 theorem/lemma 16 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T03:56:28.674321+00:00`；其中早期验证待办以本节当前门状态为准）：

- 7d70 新模块必须显式编译/重放/审计；29 个新证明体目前仅源码候选。
- 这给出 auxiliary-k 和大模数约化，尚非 k=1 的小模数实际 rough/Möbius SW，也不是 medium dispersion。

### P3 — `ImbalancedChen.Part3RoughAuxiliarySWNormalization`

文件：`ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean`；接收 Part：P3, P4-B, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `7d70a2545fd819706e473eb41e4d430ad19119d8` |
| 原始 blob | `60bd8f19aa6733851fbfc43b2afb269a97fa1ed3` |
| 原始 SHA256 | `1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c` |
| 当前 blob | `60bd8f19aa6733851fbfc43b2afb269a97fa1ed3` |
| 当前 SHA256 | `1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c` |
| 当前固定源码提交 | `7d70a2545fd819706e473eb41e4d430ad19119d8` |

z=x^(1/(loglog x)^3)、q≥log(x)^(A+2) 与 H≥x^xi 的 uniform 归一化；medium admissibility 保留正 alpha 尺度。

类型：源码 theorem/lemma 13 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T03:56:28.674321+00:00`；其中早期验证待办以本节当前门状态为准）：

- 7d70 新模块显式编译/重放/审计及前模块依赖。
- 实际 k=1 小模数 rough/Möbius uniform hSW 仍是明示未证输入，不能用封装宣称消除。
- 完整 medium (18)、碰撞范数 (23)、共同包 Kuznetsov/exceptional return (24) 与 theta=7/32 的真实解析证明仍缺。

### P4-A — `ImbalancedChen.ActualUpperDensityAssembly`

文件：`ImbalancedChen/ActualUpperDensityAssembly.lean`；接收 Part：P4-B, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `262f69822a386a9d44efc059bceba11049668d68` |
| 原始 blob | `80ec53545eeb91ccdc172d7072c6568c1dc01c5d` |
| 原始 SHA256 | `241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d` |
| 当前 blob | `80ec53545eeb91ccdc172d7072c6568c1dc01c5d` |
| 当前 SHA256 | `241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d` |
| 当前固定源码提交 | `262f69822a386a9d44efc059bceba11049668d68` |

保留 epsilon→N0 量词顺序的 raw policy 密度组装桥；仍条件于完整 limit、实际证书与 <K 的 gap。

类型：源码 theorem/lemma 7 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T03:56:28.674321+00:00`；其中早期验证待办以本节当前门状态为准）：

- 显式编译、重放、公理审查。
- P1 实际完整策略极限与 compiler 误差；P2 同一实际积分的全族数值证书。
- 最终同一实际 rho 的 K 密度真供应者仍缺；丢掉 saving 的 envelope 只能比较，不可假作相等的实际 limit。

### P4-A — `ImbalancedChen.ActualUpperPolicyDensity`

文件：`ImbalancedChen/ActualUpperPolicyDensity.lean`；接收 Part：P4-A, P4-B, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `262f69822a386a9d44efc059bceba11049668d68` |
| 原始 blob | `487f13707ee13159cd7f161879b5a2e44ffb8c19` |
| 原始 SHA256 | `16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6` |
| 当前 blob | `487f13707ee13159cd7f161879b5a2e44ffb8c19` |
| 当前 SHA256 | `16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6` |
| 当前固定源码提交 | `262f69822a386a9d44efc059bceba11049668d68` |

原始 odd policy 系数、密度恒等式及奇偶处理。

类型：源码 theorem/lemma 12 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T03:56:28.674321+00:00`；其中早期验证待办以本节当前门状态为准）：

- 本模块及共享依赖显式验证。
- P1 真实完整策略及支持/合法性；原始 odd policy 不自动是实际编译后的 physical 权。

### P4-B — `ImbalancedChen.RealPhysicalUpperWeightBridge`

文件：`ImbalancedChen/RealPhysicalUpperWeightBridge.lean`；接收 Part：P4-B。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `262f69822a386a9d44efc059bceba11049668d68` |
| 原始 blob | `9fcdf562291c27cb75c8a102e6dcafddf1200905` |
| 原始 SHA256 | `f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d` |
| 当前 blob | `9fcdf562291c27cb75c8a102e6dcafddf1200905` |
| 当前 SHA256 | `f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d` |
| 当前固定源码提交 | `262f69822a386a9d44efc059bceba11049668d68` |

实数 b 与同一 physical 权的有限 Fubini/RealB 桥，保留互素门和正外层比较。

类型：源码 theorem/lemma 25 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T03:56:28.674321+00:00`；其中早期验证待办以本节当前门状态为准）：

- 显式验证与 P1 真实支撑/合法 majorant。
- P3 同一实际 rho 的相应分布余项与统一误差，不能用整数 b 降低实数参数范围。

### P4-B — `ImbalancedChen.RealUpperCountingAssembly`

文件：`ImbalancedChen/RealUpperCountingAssembly.lean`；接收 Part：P0。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `262f69822a386a9d44efc059bceba11049668d68` |
| 原始 blob | `6e6843444cafa0e1d51a903981da0092983d2ac0` |
| 原始 SHA256 | `56bab762d3f765f5080a441910a8696e297bcd72801e13f4338b0ed7142a9a96` |
| 当前 blob | `6e6843444cafa0e1d51a903981da0092983d2ac0` |
| 当前 SHA256 | `56bab762d3f765f5080a441910a8696e297bcd72801e13f4338b0ed7142a9a96` |
| 当前固定源码提交 | `262f69822a386a9d44efc059bceba11049668d68` |

同一实际 rho 的四个真实输入导出 hUpper 的条件式计数桥；不是 hUpper 供应者。

类型：源码 theorem/lemma 1 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T03:56:28.674321+00:00`；其中早期验证待办以本节当前门状态为准）：

- 本模块显式验证。
- P1 实际构造/支持/点态界、P4-A K 密度、P3 实际分布误差各自真供应者。
- 不得把未证 hUpper 或等价条件藏进新结构/类型类。

### P4-A — `ImbalancedChen.UpperCoefficientPerturbation`

文件：`ImbalancedChen/UpperCoefficientPerturbation.lean`；接收 Part：P4-A, P4-B, P5。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `262f69822a386a9d44efc059bceba11049668d68` |
| 原始 blob | `498d09cf1bb960fc5cdd5d811e84f947a651bdc4` |
| 原始 SHA256 | `59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef` |
| 当前 blob | `498d09cf1bb960fc5cdd5d811e84f947a651bdc4` |
| 当前 SHA256 | `59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef` |
| 当前固定源码提交 | `262f69822a386a9d44efc059bceba11049668d68` |

有限绝对系数差控制 majorant 和密度扰动；可承载 compiler 预算。

类型：源码 theorem/lemma 7 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T03:56:28.674321+00:00`；其中早期验证待办以本节当前门状态为准）：

- 本模块及共享依赖显式验证。
- P1 实际 compiler 扰动预算及其消失/被支付证明。

### P5 — `ImbalancedChen.CurrentChenBuchstabRefinement`

文件：`ImbalancedChen/CurrentChenBuchstabRefinement.lean`；接收 Part：P2, P5, P0。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `3b8ab5eb2041af1906ecdb108f5edd2dd61f19aa` |
| 原始 blob | `b4a4135b39ef7cab2e7661aac98af4b1f66192b6` |
| 原始 SHA256 | `8a9352e999496160e3093b38cd1e6472468b27deac1315f85752c9133d3c3e0b` |
| 当前 blob | `303e0fe8ffbb46c53e4a53698a3662c9c207092f` |
| 当前 SHA256 | `02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5` |
| 当前固定源码提交 | `db97d0fe03250f4d9a8aea34b23e9c20f67010b8` |

实际 Buchstab 函数满足 s≥7/3 ⇒ buchstab(s)≥11/20；四个公开定理和一个私有辅助定理。

类型：源码 theorem/lemma 5 个；编译器全部声明 5 个，其中匹配源码 theorem/lemma 5 个。

当前尚未完成的验证门：该生产模块的三个门均有匹配回执。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `8a9352e999496160e3093b38cd1e6472468b27deac1315f85752c9133d3c3e0b` | 1 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T031812037811Z-compile-ImbalancedChen.CurrentChenBuchstabRefinement.log` |
| compile strict | `02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T031917418253Z-compile-ImbalancedChen.CurrentChenBuchstabRefinement.log` |
| replay  | `02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5` | 0 | `/workspace/scratch/cd30ec11ea1d/p5-round2/runtime/logs/20261012T032450416121Z-replay-ImbalancedChen.CurrentChenBuchstabRefinement.log` |

保留的第一处真实诊断：

```text
/workspace/scratch/535d89efd063/p0-round2/validation/ImbalancedChen/CurrentChenBuchstabRefinement.lean:45:25: error: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

公理回执沿用基线台账中已验证的同源历史回执；没有补造 import 前后捕获。

### P5 — `ImbalancedChen.CurrentChenLowerScale`

文件：`ImbalancedChen/CurrentChenLowerScale.lean`；接收 Part：P5, P0。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `3b8ab5eb2041af1906ecdb108f5edd2dd61f19aa` |
| 原始 blob | `7f13b7bc1d89bae22b5936aaedce1b39c2fefc30` |
| 原始 SHA256 | `cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13` |
| 当前 blob | `7f13b7bc1d89bae22b5936aaedce1b39c2fefc30` |
| 当前 SHA256 | `cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13` |
| 当前固定源码提交 | `bd83a110ee52626daf9e68535c007eb73a93daca` |

有限条件式 factor-4 预算桥，4c=49044063/6250000；未供给实际 hLower。

类型：源码 theorem/lemma 4 个；编译器全部声明 5 个，其中匹配源码 theorem/lemma 4 个。

当前尚未完成的验证门：该生产模块的三个门均有匹配回执。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13` | 0 | `/workspace/scratch/cd30ec11ea1d/p5-round2/runtime/logs/20261012T043109605634Z-compile-ImbalancedChen.CurrentChenLowerScale.log` |
| replay  | `cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13` | 0 | `/workspace/scratch/cd30ec11ea1d/p5-round2/runtime/logs/20261012T043625594734Z-replay-ImbalancedChen.CurrentChenLowerScale.log` |

公理回执：`/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T054019888426Z-compile-verification.parts.p0.ChenFiniteAudit.log`；绑定方法：recorded audit import objects before/after; primary object matched to current-source strict compile。

接口审查及未闭合输入（审查时刻 `2026-10-12T05:41:34.873039+00:00`；其中早期验证待办以本节当前门状态为准）：

- The same actual adopted selector, actual distribution errors, each of the eleven analytic mean estimates and adopted integral certificates remain inputs.
- P4-A must supply K density for the same actual arithmetic rho; P5 does not need to wait for P4-B.
- Rows six and eleven share one pair mask; the row-nine cutoff varies with the outer pair; rows ten/eleven retain their full labels and budgets.
- No complete current-c / Chen mean estimate or eventual hLower is supplied by the finite conditional conversion.
- InitialSource and InitialMean at bd83 are separate candidates; successful logs for later uncommitted source hashes do not verify those fixed files.

### P5 — `ImbalancedChen.CurrentChenMeanLedger`

文件：`ImbalancedChen/CurrentChenMeanLedger.lean`；接收 Part：P5, P0。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `3b8ab5eb2041af1906ecdb108f5edd2dd61f19aa` |
| 原始 blob | `e383e25ad0525fa4d492701fe5e56d49292229fb` |
| 原始 SHA256 | `ab659310c2dca5400a6ffedc3790e1435187dc98b29e861cf273d95395005183` |
| 当前 blob | `59e259fd376660af2a6209b00a68ed83794a3b87` |
| 当前 SHA256 | `30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8` |
| 当前固定源码提交 | `bd83a110ee52626daf9e68535c007eb73a93daca` |

十一项实际有限 Chen 来源与恒等式，权 (3,1,-1,-1,1,1,-2,-1,-1,-1,-1)，绝对和 14；均值界仍条件式。

类型：源码 theorem/lemma 34 个；编译器全部声明 93 个，其中匹配源码 theorem/lemma 34 个。

当前尚未完成的验证门：该生产模块的三个门均有匹配回执。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `dccf0a4fc0cb8fa3568487215035147852adbd753af70dbe7b6a7f5db705e748` | 1 | `/workspace/scratch/cd30ec11ea1d/p5-round2/runtime/logs/20261012T041319106553Z-compile-ImbalancedChen.CurrentChenMeanLedger.log` |
| compile strict | `d6743f88d2badb788cb6d1dbde8a1e68f147498fa179d805cb1f93652503b5c1` | 1 | `/workspace/scratch/cd30ec11ea1d/p5-round2/runtime/logs/20261012T041911234213Z-compile-ImbalancedChen.CurrentChenMeanLedger.log` |
| compile strict | `30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8` | 0 | `/workspace/scratch/cd30ec11ea1d/p5-round2/runtime/logs/20261012T042402897056Z-compile-ImbalancedChen.CurrentChenMeanLedger.log` |
| replay  | `30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8` | 0 | `/workspace/scratch/cd30ec11ea1d/p5-round2/runtime/logs/20261012T043511053990Z-replay-ImbalancedChen.CurrentChenMeanLedger.log` |

保留的第一处真实诊断：

```text
/workspace/scratch/cd30ec11ea1d/goldbach-formalization/ImbalancedChen/CurrentChenMeanLedger.lean:47:2: error: Type mismatch
  Finset.card_filter_add_card_filter_not E
has type
  (Finset.filter E (chenY6Tuples n A H D)).card + {a ∈ chenY6Tuples n A H D | ¬E a}.card = (chenY6Tuples n A H D).card
but is expected to have type
  (Finset.filter E (chenY6Tuples n A H D)).card + {t ∈ chenY6Tuples n A H D | ¬E t}.card = (chenY6Tuples n A H D).card
```

公理回执：`/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T054019888426Z-compile-verification.parts.p0.ChenFiniteAudit.log`；绑定方法：recorded audit import objects before/after; primary object matched to current-source strict compile。

接口审查及未闭合输入（审查时刻 `2026-10-12T05:41:34.873039+00:00`；其中早期验证待办以本节当前门状态为准）：

- The same actual adopted selector, actual distribution errors, each of the eleven analytic mean estimates and adopted integral certificates remain inputs.
- P4-A must supply K density for the same actual arithmetic rho; P5 does not need to wait for P4-B.
- Rows six and eleven share one pair mask; the row-nine cutoff varies with the outer pair; rows ten/eleven retain their full labels and budgets.
- No complete current-c / Chen mean estimate or eventual hLower is supplied by the finite conditional conversion.
- InitialSource and InitialMean at bd83 are separate candidates; successful logs for later uncommitted source hashes do not verify those fixed files.

### P0 — `ImbalancedChen.CurrentPairedBuchstabBridge`

文件：`ImbalancedChen/CurrentPairedBuchstabBridge.lean`；接收 Part：P2, P5, P0。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | 尚未固定，按真实本地候选哈希追踪 |
| 原始 blob | `6db112740c1a5ac1981dbe5d0e6705e718382296` |
| 原始 SHA256 | `280481d294ebd6c9fa73e74e19b5dbd2efcb2018af6c6a1953d746cee80a7550` |
| 当前 blob | `6db112740c1a5ac1981dbe5d0e6705e718382296` |
| 当前 SHA256 | `280481d294ebd6c9fa73e74e19b5dbd2efcb2018af6c6a1953d746cee80a7550` |
| 当前固定源码提交 | `c9f407efe66240c08c2e8a678330ba7b98b74db5` |

将 P2 实际首格的 whole-fibre residual ≥ 7/3 与 P5 已证 Buchstab ≥ 11/20 连接，导出实际 support 上 buchstab−1/2 ≥ 1/20；不重复乘入 K/80 已含的因子。

类型：源码 theorem/lemma 2 个；编译器全部声明 2 个，其中匹配源码 theorem/lemma 2 个。

当前尚未完成的验证门：该生产模块的三个门均有匹配回执。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `280481d294ebd6c9fa73e74e19b5dbd2efcb2018af6c6a1953d746cee80a7550` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T042042068511Z-compile-ImbalancedChen.CurrentPairedBuchstabBridge.log` |
| replay  | `280481d294ebd6c9fa73e74e19b5dbd2efcb2018af6c6a1953d746cee80a7550` | 0 | `/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T044608376465Z-replay-ImbalancedChen.CurrentPairedBuchstabBridge.log` |

公理回执：`/workspace/scratch/535d89efd063/p0-round2/runtime/logs/20261012T042731728340Z-compile-verification.parts.p0.PairedBuchstabAudit.log`；绑定方法：recorded audit import objects before/after; primary object matched to current-source strict compile。

接口审查及未闭合输入（审查时刻 `2026-10-12T04:59:00.605345+00:00`；其中早期验证待办以本节当前门状态为准）：

- The entire adopted mask and the real arithmetic parent remain separate inputs.
- The integral coefficient K/80 already contains the gain 1/20 times K/4; do not apply that gain twice.
- No full K/c/hLower/hUpper claim.

### P5 — `ImbalancedChen.CurrentChenInitialSource`

文件：`ImbalancedChen/CurrentChenInitialSource.lean`；接收 Part：P5, P0。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `bd83a110ee52626daf9e68535c007eb73a93daca` |
| 原始 blob | `75b04cb3982d24329f5f775c04c591cbfa505cf0` |
| 原始 SHA256 | `2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767` |
| 当前 blob | `75b04cb3982d24329f5f775c04c591cbfa505cf0` |
| 当前 SHA256 | `2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767` |
| 当前固定源码提交 | `bd83a110ee52626daf9e68535c007eb73a93daca` |

固定来源候选：实际 prime-difference S1 向 current sifted source 的有限转移、两个奇异级数一致性、固定比值四系数与 primeFactors 误差可忽略性；固定源码编译失败。

类型：源码 theorem/lemma 5 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

| 实际动作 | 源 SHA256 | exit | 原始日志 |
|---|---|---|---|
| compile strict | `2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767` | 1 | `/workspace/scratch/cd30ec11ea1d/p5-round2/runtime/logs/20261012T045632402531Z-compile-ImbalancedChen.CurrentChenInitialSource.log` |
| compile strict | `4b11a63cc976a0866068337c12d616578dace6c80736574311f4cca13f7d8956` | 0 | `/workspace/scratch/cd30ec11ea1d/p5-round2/runtime/logs/20261012T050523412338Z-compile-ImbalancedChen.CurrentChenInitialSource.log` |
| replay  | `4b11a63cc976a0866068337c12d616578dace6c80736574311f4cca13f7d8956` | 0 | `/workspace/scratch/cd30ec11ea1d/p5-round2/runtime/logs/20261012T050941835629Z-replay-ImbalancedChen.CurrentChenInitialSource.log` |

保留的第一处真实诊断：

```text
/workspace/scratch/cd30ec11ea1d/goldbach-formalization/ImbalancedChen/CurrentChenInitialSource.lean:41:14: error: unsolved goals
p : ℕ
h : p ∉ {p | Nat.Prime p ∧ 2 < p}
hp : 1 + MathlibNt.SieveTheory.SingularSeries.liuBaseDeviation p ≠ 1
⊢ Nat.Prime p → 2 < p → ↑p - 1 = 0
```

接口审查及未闭合输入（审查时刻 `2026-10-12T05:39:51.852925+00:00`；其中早期验证待办以本节当前门状态为准）：

- 固定 bd83 源 SHA256 2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767 有 strict/trustLevel0 编译失败；首诊断见 20261012T045632402531Z 日志 41:14 unsolved goals。
- 不同的 live 未提交源 4b11a63cc976a0866068337c12d616578dace6c80736574311f4cca13f7d8956 有 producer compile/replay 和随后 InitialSourceAudit 成功记录；不可用于本固定源的门状态。
- 本固定源尚无匹配成功的生产编译、原装重放及 P0 同对象完整公理审计；不得接收为已核验组件。
- 源码拟提供实际 S1 源转移、奇异级数归一化等式、固定比值四系数及 primeFactors 误差；本模块不供应完整十一项均值、真实 c/K 或 hLower。

### P5 — `ImbalancedChen.CurrentChenInitialMean`

文件：`ImbalancedChen/CurrentChenInitialMean.lean`；接收 Part：P5, P0。

| 身份 | 完整值 |
|---|---|
| 原始固定提交 | `bd83a110ee52626daf9e68535c007eb73a93daca` |
| 原始 blob | `eedc3b6b1c8fe97bd46f17ab5ecbbe89d593c408` |
| 原始 SHA256 | `adad5c2c0a98b49fed4ef832726e2fa20881b4fd8e31a270f93c32902e13e6c5` |
| 当前 blob | `eedc3b6b1c8fe97bd46f17ab5ecbbe89d593c408` |
| 当前 SHA256 | `adad5c2c0a98b49fed4ef832726e2fa20881b4fd8e31a270f93c32902e13e6c5` |
| 当前固定源码提交 | `bd83a110ee52626daf9e68535c007eb73a93daca` |

固定来源候选：拟由已 pin 的普通 BV 固定比值四下筛与实际源字典推导 current Upsilon1 的非平凡渐近下界；尚无匹配目标完成记录。

类型：源码 theorem/lemma 1 个；编译器全部声明 0 个，其中匹配源码 theorem/lemma 0 个。

当前尚未完成的验证门：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

接口审查及未闭合输入（审查时刻 `2026-10-12T05:39:51.852925+00:00`；其中早期验证待办以本节当前门状态为准）：

- 固定 bd83 源 SHA256 adad5c2c0a98b49fed4ef832726e2fa20881b4fd8e31a270f93c32902e13e6c5 尚无匹配目标的 compile/replay 完成记录或实际首诊断；保持未编译候选身份。
- 不同的 live 未提交源 5358e4dbbda436b335620de19884624df3260386d5ab5e478a85f70599da6137 与本固定源分开登记，不能共享未经绑定的门状态。
- 直接依赖 CurrentChenInitialSource 的固定 bd83 源已失败；其余依赖为 CurrentChenMeanLedger 和固定上游 LiLiuGoldbachS1BetaFixedNormalizedLower，尚需实际 supplier 闭包与三门验证。
- 源提取目标仅为 actual Upsilon1 的 (33/4) log 3 下界；不是 adopted L1 端点，不闭合另外十项、真实 c/K 或 hLower。

## 全局接口与验证边界

P5 只需要等待 P4-A 的同一实际 rho 的 K 密度界，不等待 P4-B hUpper。P1 实际权、支持/合法性、P2 实际积分和证书、P3 相应分布误差必须指向同一实际构造。完整 K/c 解析供应者和最终 hLower/hUpper 仍未闭合，不能移入结构或类型类后宣称消除。

P1 闭包快照 596 / 688；四个生产目标已有完成记录 1 个。远端交接状态以附带原始读取时刻为准，404 不代表没有成果。

本单附带 Actions 回执是否匹配声明的集成 SHA：`True`。没有运行器或 steps=[] 的运行不能视为 Lean 验证已执行；没有触发新 CI。

完整源/对象绑定、原始失败、日志快照、全部编译器声明与公理集合保存在 JSON。新的源码变化必须匹配自己的完成记录；部分日志和进行中任务不会被计作 PASS。
