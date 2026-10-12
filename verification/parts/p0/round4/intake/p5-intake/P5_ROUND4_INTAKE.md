# Part 0 第四批：P5 固定依赖 S1LowerRosser 接收回执

## 接收结论

建议正式接收 `MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser` 的固定依赖验证证据：**8 项所属声明、2 个公开定理，严格编译、原装目标重放、完整所属声明传递公理审计均实际通过；P0 本次按原始证据复用，没有重跑 Lean/Lake/CI。** 这次不新增 `ImbalancedChen` 生产源码，不将它计为新增自有生产模块，也不推出完整 Chen 均值、解析 c 或 hLower。

| 身份 | 固定值 |
| --- | --- |
| P5 交接提交 | `7b1283e4a70874e4fb7004bafad0793069bdea71` |
| 直接父提交 | `bf54caeb5e708474cacefac13a171d307b4c64f2` |
| 提交树 | `2fffeb66584f83e3d7acd5cc3294770765a3e741` |
| 已核验 P0 集成基准 | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` |
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| Lean | `leanprover/lean4:v4.33.0-rc1`；githash `62eed1db4d67327ec8120be05f1a1b0847d74561` |
| goldbach pin | `09b97db5764ade1246bfb77206baa1b124760958` |
| mathlib pin | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| 实际生产源码 SHA256 | `c07c0704c975bef4d772090ce03d7536f28edd319c700c4d9feb27c9f111ef62` |
| 实际目标对象 SHA256 | `005d9ac78bbd5e65386511bd975758f4fa8ed955e327c794569ab4a538be4988` |
| 目标对象字节 | `145336` |
| 接收 Part | P5 首项均值供应链、P0 统筹验证 |

全部 11 项依赖 pin 与共同基线及 P0 已验集成相同；P5 原有根导入、主定理、数值转移及手稿地图未改。

## 实际验证与对象绑定

| 原始阶段 | 退出码 | 实际秒数 | 原始结果 |
| --- | ---: | ---: | --- |
| 固定目标严格 frontend | 0 | 259.896 | 官方 frontend，trustLevel=0、warningAsError=true |
| 原装 `leanchecker --verbose` 目标重放 | 0 | 95.498 | 日志实际列出目标；未使用 `--fresh` |
| 审计辅助脚本首次尝试 | 1 | 81.689 | 原始错误保留，不冒充成功 |
| 修复辅助脚本后的实际审计 | 0 | 358.243 | 完整 8 项 + 2 个指定公开类型确认 |

目标对象贯通 **严格编译输出→重放输入/输出→成功审计直接导入前/后**，哈希及目标路径一致。目标唯一直接导入为已验 `S1Carrier`，其源码 SHA256 `757bdcea11195c48ed5814f95a70737326853e68bfaa093711a4f6161e1a896a`、对象 SHA256 `6bd8d1615d37f2db31e57c57ed66672f5fd646a0dc7a73eaa0badcac24ac16bd` 与固定旧回执一致。审计同时记录 `Lean.Util.CollectAxioms` 的导入对象及附件前后身份。

P0 实际执行了 `verify_fixed_intake.py`，35 项检查全部通过：173 个新增归档文件逐字匹配固定 Git blob、原始日志哈希及命令头、目标编码/压缩/解码三层哈希、全部源码/对象关系、标准三公理、实际类型数据、冻结依赖与保护项。

另外 `verify_import_bindings.py` 核对 96 个旧本地导入模块的源码、对象及 **430 条历史直接导入哈希**；62 个恢复对象改了绝对存放目录，模块相对路径、所有对象及附件字节身份保持一致。该补充检查最终通过。两次仅属 P0 消费端格式比较的失败原件保留：先比较了跨恢复目录的绝对路径，随后错误要求所有附件均以 `.olean` 结尾；最终按模块相对文件名与完整字节身份比较，生产者证据和证明未修改。

preflight 的 8,776 个源码导入节点可用性、96 个本地历史对象见证及 8,679 个官方缓存节点均按原回执记录。**不宣称对全部导入闭包做了本批全新严格编译/重放/公理审计。** 原生产者只恢复所需历史闭包：37 个 trust-zero 补编、25 个同哈希复制，目标三门继续严格。

## 类型及语义范围

实际 defining-module 枚举为 7 个 theorem + 1 个 definition，含 4 个 private 名称及 generated 声明。没有 own axiom 或 unsafe 声明；传递公理并集只有 `propext, Classical.choice, Quot.sound`。枚举使用 `env.constants` 与实际模块归属，不是名称前缀或源码 grep。

[PUBLIC_TYPES_COMPLETE.md](PUBLIC_TYPES_COMPLETE.md) 列出两个公开定理的默认和 explicit 编译器完整类型；[COMPILER_TYPES_8.json](COMPILER_TYPES_8.json) 保存全 8 项与原始 Expr。格式为 explicit + universes + fullNames + proofs，**没有伪标成 pp.all**。一项 generated 默认类型省略了证明参数，其同时记录的 explicit 与原始 Expr 没有省略。

令 `m = Nat.ceil ((1-ε)*(N:ℝ))-1`，`P = goldbachS1ProdPrimes N z`，`λ⁻ = lowerRosserWeight P D`。已验有限下界为：

```text
trueLogarithmicIntegral(m) * ∑ d ∈ P.divisors, λ⁻ d / φ(d)
  - ∑ q ∈ Icc 1 Q0, standardPrimeAPPrefixMaxError N q
≤ (goldbachS1 (goldbachDifferenceCarrier N ε) N z : ℝ).
```

全部公开假设保持：`0 < ε < 1`、`Even N`、`2 ≤ m`、`2 ≤ z`、`∀ p ∈ P.primeFactors, p < D`、`D ≤ Q0+1`；不删除证明体未使用的 `_hε1` 或 `_hz`。右侧是实际 `ℤ` 有限筛计数转为 `ℝ`，不是换成新权/新计数；实际单位权、严格素数端点、严格筛门及 totient 主和均保留。误差前缀和仍需在归一化尺度上支付。

## 首处诊断与环境界限

已保留最早恢复期实际 Lean 诊断：`PrimeNumberTheoremAnd.Wiener.lean:1:0` 缺少 `PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.olean`。这是命名空间路径遮蔽造成的导入阶段失败，目标 S1LowerRosser 尚未启动。控制器退出 1，frontend 数字退出码当时未落盘，记录 `null`，不编造。

目标严格编译及目标重放一次通过。审计脚本首处实际错误在 `S1LowerRosserAudit.lean:47:23`：`MonadWithOptions CommandElabM` 实例不可合成；另有选项链式写法错误。生产者仅把 `withOptions` 移至 `liftTermElabM` 并逐项设置选项；修复前后源码与补丁均原样归档。P0 本批没有生产证明修复。

现存官方运行时二进制哈希与历史记录一致，但仅文件存在不代表正常可启动。Root 本批已另行执行官方 Lean `--version`，实际仍报 `failed to locate application`；本接收任务未进一步尝试启动。历史 Lake 驱动是原已验驱动，使用 `unsafe Lean.enableInitializersExecution` 启动初始化器，再调用官方 frontend 的 trustLevel=0；此 helper 不是证明声明，目标另经原装重放，未用它注入证明或跳过内核。原始机制如实保留。

P5 原对象路径已经消失；本提交提供的 `.olean.gz.b64` 已由 P0 解码并核对。使用它前仍须匹配锁定源码、工具链、导入身份；不直接把它装进正在运行的其他 Part 工作树。

## 分批接收文件与下一接口

固定提交新增 173 文件，仅属于：`docs/CHEN_P5_S1LOWERROSSER_HANDOFF.md`、`verification/parts/p5/S1LowerRosserAudit.lean`、`verification/parts/p5/round4/s1lowerrosser/**`。完整逐文件 blob、SHA256 与字节数见 [EXTRACTION_MANIFEST.json](EXTRACTION_MANIFEST.json)。没有 `ImbalancedChen/*.lean` 生产改动。P0 可按固定新增路径接收证据与辅助审计，公共根是否显式导入依赖由 P0 统一决定；不 cherry-pick P5 旧祖先中的未验候选。

已解除 `S1BetaPaidLower` 真实有限 Rosser 主项减 AP 前缀误差下界的供应边；固定源码确实调用了本批第二个定理。`S1BetaLowerDensity` 的直接 import 供应边也解除，但不因此接收其密度结论。

下一独立节点是固定依赖 `MathlibNt.SieveTheory.LiLiuGoldbachS1MainMass`，SHA256 `4fdcdd6001278a1c7636a40ba8f2e2e6c685a20331a4b0c803c0146f516a4533`，唯一直接导入 `MathlibNt.SieveTheory.BombieriVinogradov`。它的完整源码声明头在接口单中明确标记“源码提取、未编译候选”。本批不启动它。

`CurrentChenInitialSource` 的同对象补审计绑定仍未补齐；`CurrentChenInitialMean` 仍是源码候选。Beta 几何/误差支付/密度/主尺度和归一化下界各节点须独立验收；第一项候选 `(33/4) * Real.log 3` 不等于手稿采用 L1，完整十一项均值及解析 c/hLower 仍开。P5 依赖 P1/P2/P3/P4-A 的实际供应，不等 P4-B。

P5 交接单另记录旧父 SHA bf54cae… 的根 CI 失败：run 38229846294 中 build success，根重放 1513 秒与公理审计 613 秒失败。该观察不迁移为当前提交/目标模块结论；P0 本接收没有启动或重跑 Actions。新集成的 Actions 状态由 Root 对明确集成 SHA 单独记录。
