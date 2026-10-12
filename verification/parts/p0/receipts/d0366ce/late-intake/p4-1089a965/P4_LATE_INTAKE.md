# P4 新固定交接 1089a965：独立源码与证据接收回执

## 接收结论

**登记为可追溯的修复源码候选；本次尚不能升级为已核验生产组件。** 新提交确实恢复了三个模块的证明体修复，并给出先前五次严格编译、五次逐模块 stock kernel replay 及 Audit 严格编译成功的生产者观察记录。原始 Lean stdout/stderr、目标编译对象和完整所属声明清单在交接前丢失，aggregate fresh replay 与最终封存没有完成。已保留的 39 项 Python 成功记录是验证器自检，不能填补这些证明证据。

新提交已经有正常执行中的专项 CI；本审查只复用约 18:50 UTC 保存的实际 API 快照，未轮询、重启、重复构建或中断任何运行。届时专项运行 `38288356713` 的完整验证步骤仍在执行。接收应等待该已有运行的最终原件，并逐项审核，不能把 `in_progress` 写为成功。

**数学结论没有改变：同一实际 rho 的 sharp K、hUpper、完整 Chen mean、c 和 hLower 仍未闭合。P5 只等待 P4-A，不等待 P4-B。** 本新交接没有进入集成 `d0366ce64272e81faf6166a8a90050f56b328d38`；该 SHA 的根验证不能覆盖本批 P4 修复源码。[固定交接](https://github.com/UyNewNas/goldbach-formalization/blob/1089a965e20664e63ffd51e0105c11befa406a1f/docs/PART4_UPPER_HANDOFF.md)与[round2 状态说明](https://github.com/UyNewNas/goldbach-formalization/blob/1089a965e20664e63ffd51e0105c11befa406a1f/verification/parts/p4a/round2/README.md)都明确保留这些开放输入。

## 1. 固定身份与本次实际操作

| 项目 | 固定值 |
|---|---|
| 新 P4 源 SHA | `1089a965e20664e63ffd51e0105c11befa406a1f` |
| 新源树 | `ebfb0ed3ddb58504b7e33344f2d39cc960aa32d5` |
| 直接父提交 | `3d5dd058cf6bef5fe90719ee277580baf8b5bf41` |
| 旧 P4 证明源码 | `262f69822a386a9d44efc059bceba11049668d68` |
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 集成分支当前 SHA | `d0366ce64272e81faf6166a8a90050f56b328d38` |
| 源分支 | `chatgpt/chen-p4-upper` |
| 手稿固定起点 | `ba6ec11d800eccc54406490631895e174de85766`，沿用既有冻结手稿；本次未修改手稿 |
| Lean pin | `leanprover/lean4:v4.33.0-rc1` |
| 本次核对 | 103 项固定源码/已有证据交叉核对，全部通过；不是 Lean 验证 |

本次执行 `review_fixed_intake.py`，只读取固定 Git 对象、已提取源码与既有 JSON/log，写本 intake 目录。实际 stdout/stderr 在 `review-source.stdout.log`、`review-source.stderr.log`；stderr 为空，exit 0。未执行 Lean、Lake、kernel replay、公理审计、CI、生产者 39 项 fixture 或环境恢复。检查前后集成 HEAD 均为 `d0366ce64272e81faf6166a8a90050f56b328d38`。

提取的 32 个固定文件均逐字节匹配新 Git 对象，同时验证 Git blob、SHA-256 和长度；清单为 `FIXED_EXTRACTION_MANIFEST.json`。`SOURCE_CHANGES.patch` 是父提交到新固定提交的原始 Git diff。本回执未新增 Git 提交，也未修改任何生产源分支。

### 工具链和依赖

`lean-toolchain`、`lakefile.toml`、`lake-manifest.json`、`CurrentMainTheorem.lean`、`CurrentNumericalTransfer.lean`、`CURRENT_MANUSCRIPT_MAP.md`、`EXTERNAL_REUSE.md` 全部与共同基线和 d036 原字节一致。十一依赖 pin 逐项来自固定 `lake-manifest.json`：

| 依赖 | 完整 revision |
|---|---|
| `goldbach` | `09b97db5764ade1246bfb77206baa1b124760958` |
| `mathlib` | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| `LeanArchitect` | `78dd66840d3efe8c824c699fc03381cec817c271` |
| `plausible` | `b1c4a69a7e247ab7df20460212001673d74f08c0` |
| `LeanSearchClient` | `0498c7c070c143a3bf7379f4d99a2c63bb9d9715` |
| `importGraph` | `18a90119a5d316358fde6c86e0ca24e59212e32c` |
| `proofwidgets` | `b1436dc749e722c9920036b52cdc43b3451d0b69` |
| `aesop` | `57d3325be72a842920813bcb40f96a6f7393c185` |
| `Qq` | `ee41917ae11d38479fb8fb24745f7ca4bf0a784d` |
| `batteries` | `41bd267b3f6b7252f6676af46d4ffc6783b64de9` |
| `Cli` | `da07ca808b6718cb2aed14dba154e5a08b8f8ecf` |

## 2. 五个旧候选与新源码的精确区别

3d5d 的五个生产模块均与原 262f 证明提交及 d036 的 `verification/parts/p0/round3/ledger/snapshot-sources/` 对应五文件逐字节相等。新 1089 的 **53 个公开定理完整声明头全部保持原样**。因此修复不能解释为更换数学接口或新增实际解析供应者。

| 模块（命名空间 `ImbalancedChen`） | 公开源码定理数 | 相对父提交 | 新 Git blob | 新 SHA-256 |
|---|---:|---|---|---|
| `ActualUpperPolicyDensity` | 13 | 字节不变 | `487f13707ee13159cd7f161879b5a2e44ffb8c19` | `16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6` |
| `UpperCoefficientPerturbation` | 6 | 证明体修复 | `7b024033e58e19c0dcf94de322d6cb7d6815d987` | `e4d1d84fa128f7f84fb4f7d4f0b03acf8401312de1ceaed045de3aaf3b5d6e86` |
| `ActualUpperDensityAssembly` | 7 | 证明体修复 | `e363dee459e99b2be6f83f2c70b15f8968fd4817` | `659aa3d8cfa50345f912ba070e30cd57a6caa1738e4146d1c051a7506f944cec` |
| `RealPhysicalUpperWeightBridge` | 26 | 证明体修复 | `c774859dab0bdcfc1266200d7437a62d0c69e5ea` | `8a86c2e7fd2383fcae243b5958f3447675a4f5b7a4c9078ba1ba832ea067878f` |
| `RealUpperCountingAssembly` | 1 | 字节不变 | `6e6843444cafa0e1d51a903981da0092983d2ac0` | `56bab762d3f765f5080a441910a8696e297bcd72801e13f4338b0ed7142a9a96` |

| 模块 | 旧 262f / 3d5d / d036 台账源码 SHA-256 | 新源码相对旧源码 |
|---|---|---|
| `ActualUpperPolicyDensity` | `16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6` | 不变 |
| `UpperCoefficientPerturbation` | `59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef` | 变化 |
| `ActualUpperDensityAssembly` | `241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d` | 变化 |
| `RealPhysicalUpperWeightBridge` | `f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d` | 变化 |
| `RealUpperCountingAssembly` | `56bab762d3f765f5080a441910a8696e297bcd72801e13f4338b0ed7142a9a96` | 不变 |

三个证明体修复的具体原因如下，均由原始 Git diff 确认：

- `UpperCoefficientPerturbation.lean`：给 totient 非负性中的实数强制转换补充明确类型，修复类型推断。
- `ActualUpperDensityAssembly.lean`：移除两个未使用的 `simp` 参数，满足严格 warning-as-error；把加法单调性步骤改为参数适配的 `add_le_add … (le_refl _)`。
- `RealPhysicalUpperWeightBridge.lean`：使用固定 Finset API 的命名参数；修复加法单调性、整除与模同余条件项的重写，以及源集合外为零的化简。

公开声明计数 `13 + 6 + 7 + 26 + 1 = 53` 只是源码定理数，**不是**包括私有、生成和结构声明的 compiler-owned 声明总数。后者目前未知，回执明确保存为 null。

### 全部 20 个改变路径

| Git 状态 | 路径 |
|---|---|
| `M` | `.github/workflows/part4-upper.yml` |
| `M` | `ImbalancedChen/ActualUpperDensityAssembly.lean` |
| `M` | `ImbalancedChen/RealPhysicalUpperWeightBridge.lean` |
| `M` | `ImbalancedChen/UpperCoefficientPerturbation.lean` |
| `M` | `docs/PART4_UPPER_HANDOFF.md` |
| `A` | `verification/parts/p4a/round2/COMMON_CARRIER_CANDIDATE.lean.txt` |
| `A` | `verification/parts/p4a/round2/OBSERVED_CHECKS.json` |
| `A` | `verification/parts/p4a/round2/README.md` |
| `A` | `verification/parts/p4a/round2/RECOVERY_SOURCE_COMPARISON.json` |
| `A` | `verification/parts/p4a/round2/SOURCE_TYPES.json` |
| `A` | `verification/parts/p4a/round2/SOURCE_TYPES.md` |
| `A` | `verification/parts/p4a/round2/attempt1-runner-recovery-fixtures.stderr.log` |
| `A` | `verification/parts/p4a/round2/attempt1-runner-recovery-fixtures.stdout.log` |
| `A` | `verification/parts/p4a/round2/attempt1-runner-recovery-python.json` |
| `A` | `verification/parts/p4a/round2/extract_source_types.py` |
| `A` | `verification/parts/p4a/round2/runner-recovery-fixtures.stderr.log` |
| `A` | `verification/parts/p4a/round2/runner-recovery-fixtures.stdout.log` |
| `A` | `verification/parts/p4a/round2/runner-recovery-python.json` |
| `A` | `verification/parts/p4a/round2/verify_runner_recovery.py` |
| `M` | `verification/verify_part4_upper.py` |

`verification/Part4UpperAudit.lean` 和核心 `.github/workflows/lean.yml` 相对直接父提交不变。接收数学组件时，P0 应按各自源 SHA 选择生产文件并保留证据；无须把 P4 分支的根 workflow 全量替换集成 workflow。

## 3. 已有证据的真实强度

### 3.1 生产者观察成功，原始 Lean 记录丢失

以下信息来自固定 `OBSERVED_CHECKS.json`，其类型明确为 `CONVERSATION_TRANSCRIPTION_AFTER_WORKSPACE_MAINTENANCE`。**这些不是本审查重新运行所得，也不是仍可读取的原始终端日志。**

| 模块 | 严格编译观察值 | 单模块 stock replay 观察值 |
|---|---|---|
| `ActualUpperPolicyDensity` | exit 0；97.813 s | exit 0；50.465 s |
| `UpperCoefficientPerturbation` | exit 0；4.618 s | exit 0；10.926 s |
| `ActualUpperDensityAssembly` | exit 0；67.865 s | exit 0；51.165 s |
| `RealPhysicalUpperWeightBridge` | exit 0；4.686 s | exit 0；12.412 s |
| `RealUpperCountingAssembly` | exit 0；76.012 s | exit 0；50.788 s |

生产者的严格驱动使用固定官方 `Lean.Elab.runFrontend`、trust level 0、warnings as errors；驱动源码记录 SHA-256 为 `ede18bb7c68c9950c2096ed79211c4c26948c21c28ba1985bf9f38d909024f50`。逐模块 replay 记录为原 `leanchecker --verbose MODULE`，`fresh=false`，各自精确 target replay marker 被观察到。

Audit 严格编译记录为 exit 0、383.887 s；但原始输出未在删除前读取逐声明类型、逐声明公理列表和声明总数，现不能重建。五个模块的恢复源码 SHA-256 与新固定 Git 对象一致，但这不能替代已丢失的 source/object/import 绑定原件。

一个更早的 `UpperCoefficientPerturbation` 单模块 `--fresh` 尝试被中断，记录 exit 130，不能计为成功。预定的 Audit aggregate fresh replay 和 finalizer 均未运行。**第一处原始 Lean 诊断也没有保留；本回执不以证明修复说明伪造错误行号或 Lean 报错内容。**

### 3.2 已保留的真实 Python 检查

`runner-recovery-python.json` 及 stdout/stderr 是实际保留记录。独立读取确认：39 个 PASS 名称、嵌入 JSON、exit 0 与回执一致；runner、owned workflow、fixture 三个输入的前后 SHA-256 均等于新固定提交的文件。

第一次 fixture exit 1 的原始 traceback 仍在 `attempt1-runner-recovery-fixtures.stderr.log`：fixture 错误地查找小写 outcome 名称，实际 workflow 使用大写 shell 环境变量。原始失败点是 Python fixture 第 161 行调用及第 36 行抛出的 `AssertionError: Fixture condition failed`。仅 fixture 修正后得到 39 PASS；这不是 Lean 诊断，也不是修改证明门来掩盖失败。

该 Python 记录中的 `ci_status=NOT_STARTED` 是 18:00 UTC 的历史恢复时点，不可覆盖下面已经启动的正常 CI 快照。

## 4. 正在运行的真实 CI 与其范围

以下为本 intake 已保存原始 REST JSON 的快照。`api/` 四份原件的 SHA-256、保存时间和完整 job steps 都在机器回执中。之后运行可能继续推进；此表只断言已读取的快照状态。

| Run / job | 快照中的实际步骤与状态 | 可以支持的结论 |
|---|---|---|
| [P4 专项 run 38288356713](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38288356713)，job `114942066124` | 精确源 checkout、pin provenance、安装、依赖解析与 Mathlib cache 都 success；从 `18:06:10Z` 起第 7 步仍 in_progress；required outcome 与 artifact 尚 pending | 这是正常运行中的已有验证，继续复用；不能推断大步骤内部五模块已完成到哪一处 |
| [P4 分支 core run 38288356709](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38288356709)，job `114942066217` | full project build `18:06:16Z–18:46:45Z` success；root replay in_progress；root axiom/outcome pending | 有真实核心构建成果；不能替代五个 P4 显式目标的专项验证，也不是 d036 核心运行 |
| [P4 分支 VE run 38288356754](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38288356754) | completed / success | VE 的既有目标范围不包含本批五个 P4 目标 |

在新 P4 固定 SHA 上，从 `ImbalancedChen` 根计算的仓库本地源码 import 图包含 253 个模块；五个 P4 目标均不在该图。此为本地源码依赖图核对，不是外部依赖重放或证明检查。用户要求的五个新增模块显式验证仍须由已有专项运行提供。

本审查没有下载并审核已完成的该专项 artifact，因此不声称存在完整 compiled types、owned axiom 清单或已封存最终 PASS。不会用 Actions 顶层结果或 P4 分支根构建扩大验证覆盖范围。

## 5. 验证器静态审查与未来原件接收门

新 owned runner 保留五个显式 strict source compile 和五个单模块 stock replay，把重复五遍 full-closure fresh replay 改为一次 `verification.Part4UpperAudit` 的 aggregate fresh replay；Audit 直接导入全部五目标。依赖构建限额调整为 5,400 秒，owned job 限额为 180 分钟，pin 与证明门没有删除。

| 门 | 固定源码实际实现 | 接收原件时还需核对 |
|---|---|---|
| 显式严格编译 | `lake build` 先准备依赖，随后逐文件 `lake env lean -DwarningAsError=true -o …` | 每次真实命令、exit、原始日志；不能只用旧聚合根 build |
| 对象绑定 | 每个 strict 输出后立即记录 `.olean`，以及存在的 `.olean.server` / `.olean.private`；重放前后、末尾比较已知部分集合与哈希 | 实际报告的路径、哈希和集合。此实现限定这三类 Lean object parts，不声称覆盖任意扩展名或所有导入对象的逐项对象哈希 |
| 逐模块重放 | bundled checker，精确 `replaying MODULE` marker 恰一次 | 五个目标必须各有 marker 与 exit 0 |
| 完整所属声明审计 | `env.constants` + defining-module metadata；含 private/generated/structural；`pp.all=true`、universe parameters、`pp.privateNames=true`，拒绝 `⋯` | 不用 53 替代实际总数；读取所有声明类型、axioms 和各 module count |
| 公理/unsafe 门 | 拒绝 own axiom 与 unsafe；transitive axioms 仅允许 `propext`、`Classical.choice`、`Quot.sound` | 每条实际 inventory 记录均核查；静态 guard 不是逐声明结果 |
| 聚合 fresh | 单次 stock `leanchecker --fresh --verbose verification.Part4UpperAudit` | 精确 fresh marker、exit 0 与 Audit object 前后匹配 |
| 源与工具链绑定 | 固定锁文件哈希、依赖 HEAD/cleanliness、源 import closure 哈希、源文件前后、final HEAD 和 Lean/Lake/checker 三二进制前后 | 还要独立把报告中的源哈希归属到固定 Git 对象；runner 记录 root working tree，没有仅靠 `PASSED` 免除源码身份检查 |
| CI required outcome | cache/verification 必须 success；report PASSED、五 module count、非空 declaration count、fresh module、对象/二进制重查标记、全部 stages PASSED | 必须检查实际 outcome 和 report 的一致性；失败、取消和跳过不能算成功 |
| 留档 | `always()` 上传整个 `.lake/part4-upper-verification/` | 原始日志、type inventory、report/provenance/outcome 一并收取；保留首次失败 |

这段是对源代码的静态审查，不是对尚在运行中的最终 receipt 的预先认证。报告记录的源码闭包跳过 Mathlib 逐源扫描，依靠固定 mathlib pin/cache 与后续 fresh replay；不能把它描述为所有导入对象逐一 hash 绑定。

## 6. 完整关键定理类型与未闭合输入

完整、无手工省略的关键声明在 [`KEY_TYPES.md`](KEY_TYPES.md) 中；全 53 个公开声明也以原始 `SOURCE_TYPES.md/json` 保留。类型口径是 **source extracted**，声明名称之外的标识符仍沿用原文件 namespace/import 环境，不能称为 compiler elaborated types。

关键公开接口均位于 `1089a965e20664e63ffd51e0105c11befa406a1f` 的如下固定文件：

| 接口 | 固定文件 | 尚需的真实供应者 |
|---|---|---|
| `actualSmallRoughRho_eq_firstExitAttachment` | `ImbalancedChen/ActualUpperPolicyDensity.lean` | 已给定完整实际政策后所需的 `heven`；P1 某一有限前缀的 parity 只能供此特定有限输入 |
| `exists_actualSmallRoughRho_density_le_of_full_policy_limits` | `ImbalancedChen/ActualUpperDensityAssembly.lean` | 实际 `retainOdd/cap/integral`、`hcap`、同一实际归一化 density 的 `hIntegral`、同一 integral 的 `hCertificate`，以及 `rawBound < densityCap` |
| `exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits` | 同上 | 前项条件加 `rawBound < currentK`；仍是条件界，不是实际 K 解析证书 |
| `compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget` | 同上 | 同一个 small/rough carrier、small/rough support、small 密度界、raw density、实际编译误差和总预算 |
| `RealB_cast_le_actualSmallRoughRho_main_add_errors` | `ImbalancedChen/RealPhysicalUpperWeightBridge.lean` | 保留同一 rho 的有限三项 main/coprime/distribution 与 `ceil z`、`T+1` 端点成本 |
| `eventually_RealB_le_currentK_log_of_same_rho_inputs` | `ImbalancedChen/RealUpperCountingAssembly.lean` | 同一 `Q delta N`、`rho delta N` 的 `hmajor`、`hdensity`、`hcoprime`、`hdistribution` |
| `current_theorem_1_1_of_manuscript_bounds` | `ImbalancedChen/CurrentMainTheorem.lean` | 完整 `hLower` 与 `hUpper` 仍为参数，范围仍为实数 `1/2 < b < 1` |

实际 K 的难点没有被包装消除。特别是：

- full-policy 限制在精确 even-positive filter 上，以 `physicalDensitySum` / reciprocal-totient density 及 `singularSeries N / log N` 为对象。若上游只给 limsup envelope，必须先证明与这里实际 density 的关系，不能改称已给精确 `Tendsto`。
- raw-to-compiled 的误差是文字类型中的 `M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|)`，必须由真实解析估计支付。`rawBound + compilerReserve ≤ currentK` 不能靠 raw 恰等于 K 支付正 reserve。
- support legality 不止 `RoughPrimeSupportedAt`：完整政策、平方自由、与 N 互素、范围和单位界等仍要由真实构造提供。同一 carrier 的零扩展不自动证明 compiled support 合法。
- P2 固定一格或一个 A5-saving 下界不能替代完整实际 upper-integral certificate。P3 已有归一化 slot 结果也不能自动成为本式 prime-product source 的 signed distribution estimate 或 smoothing licence。
- counting 的源质量尺度为 `N / log N`，density 尺度为 `singularSeries N / log N`，乘积恰是 `singularNormalization N`；`same_rho_normalized_mainTerm` 保留精确商恒等式，没有增加 factor 2。将别的 `log(N^nu)` 归一化结果接入时仍需其真实转换。
- hUpper 结论保留实数 b 与 `log(1/b)`、严格 sieve cutoff 的 `Nat.ceil`、`T+1` 端点，不能通过有理化 b 或隐去端点来供应。

## 7. 新 common-carrier 有限候选

新文件 `verification/parts/p4a/round2/COMMON_CARRIER_CANDIDATE.lean.txt` 的 Git blob 为 `bca6b9c7eb4377c0137d3afb478ad997352c4f72`，SHA-256 为 `e6b2a2166a3624112c1b1a6f45cdeecf4bd307a387a8ee98adbe8b4f17680e86`。

它提供四个完整声明头与两个使用例：`smallRoughRho_eq_of_rough_subset`、`sum_smallRoughRho_mul_eq_of_rough_subset`、`actualSmallRoughRho_eq_rough_union`、`supportedDivisorSum_eq_of_subset`。这些将 raw rough carrier 零扩展到更大 carrier/并集并保存相同 rho、density 总和和 divisor sum。

**该文件未编译，不在五个 production targets、不在 53 个公开生产定理清单，也不在专项 Audit 内。** 可以作为下一小批单独有限节点准备验证；即使通过，也只提供 carrier 适配，不支付编译误差、不证明实际完整政策或 sharp K。不得因五模块专项最终成功就顺带接收这个 `.lean.txt`。

## 8. 对 P5 与既有开放接口附页的影响

既有 `ANALYTIC_OPEN_INTERFACES.md` 明确以 d036 为版本范围，其中关于旧 262f/3d5d 台账源码尚无目标验证回执的陈述保持其历史作用。这个 late intake 仅更新“最新 P4 源码和观察证据”的身份：不能继续把最新 1089 描述为从未执行过任何模块编译，也不能把生产者观察记录描述为已保留的最终原件。

本次没有修改该既有附页。P4-A 尚未交出 actual same-rho K，P5 的完整 Chen mean、c 和 hLower 仍缺真实供应；P4-B 尚未交出 hUpper。故附页的数学开放结论与依赖次序不变。

推荐下一步是在已有 P4 专项 run 完成后接收其明确源 SHA 的完整原件，按上述门验证五个条件式组件。若通过，可以将这些已核验组件作为独立下一批接入；根导入与最终入口仍由 P0 统一修改。P5 得到的仍首先是固定的接口状态，只有实际 K 供应者闭合后才获得其所需的 P4-A 输入，不需要等待 P4-B。

## 文件索引

- `P4_LATE_INTAKE.json`：机器可读身份、103 项核对、20 文件变化、五模块哈希、API 原件摘要与开放输入。
- `KEY_TYPES.md`：8 个关键 P4 公开声明、4 个未编译有限候选声明、原最终条件式入口的完整源码类型。
- `fixed-source/verification/parts/p4a/round2/SOURCE_TYPES.md` / `.json`：原始 53 个公开源码定理类型。
- `FIXED_EXTRACTION_MANIFEST.json`、`SOURCE_CHANGES.patch`：32 个固定提取文件身份与 20 文件原始 diff。
- `api/`：只读取得的 commit、runs、P4 jobs、P4-branch core jobs 原始 JSON。
- `review_fixed_intake.py`、`review-source.stdout.log`、`review-source.stderr.log`：独立只读交叉核对的代码与本次真实执行输出。
