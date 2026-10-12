# Part 0：d0366ce 统一验证与分批接收总回执

**固定集成源码 d0366ce 的六个核心验证门已全部实际执行成功；本批新增四个生产模块、414 项所属声明得到整体验证。最终“1+1.75”无条件入口仍未完成：同一实际 rho 的解析 K、完整 Chen 均值与 c、hLower 和 hUpper 仍缺真实供应。** 原有正确的条件式桥保持原样，没有以新结构、类型类或等价假设包装冒充完整定理。

本回执区分原始 CI 证据、P0 离线消费结果和源码接口说明。证据文档归档在独立分支 `chatgpt/chen-p0-receipts-d0366ce`；本文件不预报尚未产生的文档提交 SHA，也不把文档提交当成重新验证过的代码提交。代码验证身份始终是下表中的完整 SHA。

## 1. 固定版本、所有权与改动

| 身份 | 完整 SHA |
|---|---|
| 共同证明基线；来源 `codex/variable-envelope-boxes` | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 手稿起点 | `ba6ec11d800eccc54406490631895e174de85766` |
| 本次已验证集成；分支 `chatgpt/chen-p0-integration` | `d0366ce64272e81faf6166a8a90050f56b328d38` |
| 集成 tree | `e2ab22b96f76c8969386296558c626c62a581700` |
| 已验集成直接父提交 | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` |
| P1 固定交接 | `744316efd1887f21c91dd4b63c218fa27704c931` |
| P2 实际证明 / 成功专项 CI 源码 | `f0c00f9ccce98e04af439321a92eb9fd0dd26203` / `e6d6d57323cc358cef060fb243ec386c13cb662d` |
| P2 固定交接 | `101bb2291cd51f9717544ce477122fdd44eda44d` |
| P3 集成采用交接 / 后续诊断交接 | `f37f341412eb239f7e7e8937921ee8d01c9c2922` / `f3ad8cbe43c61c903857c7411626ee8c56f4f2f9` |
| P4 集成保留候选交接 / 后续专项源码 | `3d5dd058cf6bef5fe90719ee277580baf8b5bf41` / `1089a965e20664e63ffd51e0105c11befa406a1f` |
| P5 固定交接 | `7b1283e4a70874e4fb7004bafad0793069bdea71` |

首轮文档提交 `9fe1d6b8b68a97cad3a122410ad7fde1701eed35` 没有改变共同证明基线。完整来源及文件所有权见 [PART0_ROUND4_VERIFICATION.md](../../../../../docs/PART0_ROUND4_VERIFICATION.md)，固定父链证据见 [source-lineage](source-lineage/)。没有从初始化 master 重建证明。

工具链保持 `leanprover/lean4:v4.33.0-rc1`，实际 Lean commit 为 `62eed1db4d67327ec8120be05f1a1b0847d74561`；goldbach pin 为 `09b97db5764ade1246bfb77206baa1b124760958`，mathlib pin 为 `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。全部 11 个依赖 pin 及其完整清单仍由原 [lake-manifest.json](../../../../../lake-manifest.json) 固定；工具链、lakefile、手稿地图、外部复用说明、`CurrentMainTheorem.lean`、`CurrentNumericalTransfer.lean` 保留原字节。

| 所有者 | 本次新增生产文件（相对仓库根） | 实际所属声明 |
|---|---|---:|
| P1 | `ImbalancedChen/StoredHistoricalBoxPermit.lean` | 14 |
| P2 | `ImbalancedChen/Certificates/PairedV2Batch4To64Data.lean` | 72 |
| P2 | `ImbalancedChen/Certificates/PairedV2Batch4To64.lean` | 207 |
| P2 | `ImbalancedChen/Certificates/PairedV2Prefix64.lean` | 121 |

四个源按固定 producer Git blob 原字节接收，没有 P0 生产证明补丁。P0 负责四个公共根 import、Round4 审计/类型导出、workflow 必需门、分批入口及台账。P2 生成器原样更新；旧 309 项 `CertificateAudit.lean` 保留，新的 709 项 owner audit 原字节复制到 P0 的 `CertificatesPrefix64Audit.lean`，仅改变辅助路径。旧分批入口及原 Round3 门保留。完整变更清单见 [SOURCE_CHANGE_FILES_444.json](SOURCE_CHANGE_FILES_444.json)，逐文件来源见 [installed-fixed-files.json](../../round4/installed-fixed-files.json)。

## 2. 实际执行的统一验证

核心 [run 38289734671](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38289734671)、job `114946653833`、attempt 1 为 `completed / success`。实际 artifact 为 `11767708658`：**543994 bytes、38 个成员**，SHA-256：

```text
4d7499fd526651d70f73fb7cbbf98769ffc51d8a406e1bc80f96ad5dc0d20df8
```

| 必需门 | 实际秒数 | 退出码 / 结果 |
|---|---:|---|
| 完整项目 `lake build` | 2640 | 0 / success；9802 个构建任务 |
| 四个新增生产目标显式检查 | 4 | 0 / success |
| bundled Lean 4.33.0-rc1 根 `leanchecker` | 457 | 0 / success |
| 根声明及传递公理审计 | 29 | 0 / success |
| 原 Round3 完整类型导出及主桥 | 186 | 0 / success；198 项 |
| 新 Round4 完整类型导出及主桥 | 187 | 0 / success；414 项 |

四个显式目标在完整构建后复用刚完成的对象；没有将这个 4 秒步骤说成再次强制编译四份源码。实际项目根有 **276 个唯一项目模块重放标记**，包含全部 23 个接收组件。根公理审计清点 **5872 个声明**，允许的传递公理只有 `propext`、`Classical.choice`、`Quot.sound`。原件见 [core/original](core/original/)，六门日志、timing/outcome 与源绑定见 [core/verified](core/verified/)；P0 离线消费得到 **3956 项检查通过、0 失败**，详见 [CORE_RECEIPT.json](core/verified/CORE_RECEIPT.json)。这个离线消费没有再运行 Lean 或内核。

类型总账为 **393 个继承记录 + 本次 198 + 本次 414 = 1005**，其中 **1000 个完整 `pp.all`、5 个既有 Buchstab 完整默认 `Meta.ppExpr`**。旧 393 条保留原编译器来源，没有假称本次新打印；主桥另列，不计入 1005。组件台账为 **23 个已接收、14 个待验，共 37 个组件**，不等于整个根的模块数或声明数。[完整类型](core/verified/COMPLETE_TYPES_1005.json)、[格式映射](core/verified/TYPE_FORMATS_1005.json)、[模块台账](core/verified/MODULE_LEDGER_VERIFIED.json) 保留这一口径。

同一源 SHA 的 VE [run 38289734726](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38289734726) 也实际成功。六个生产、两个边界模块的显式执行和八次 stock replay、审计共 **358 项声明 = 284 生产 + 74 边界**，单列于 [VE_RECEIPT.md](ve/review/VE_RECEIPT.md)。这些是默认编译器打印，不能改标成 `pp.all`；数学范围是 `0 ≤ z ≤ y ≤ x ≤ 25/128`，不能扩大到全证书或 `x ≥ mu` 的扩展表达式。

## 3. 源码、对象与消费修正的准确范围

两次类型导出各自的完整 before/after 快照相等；两次的 **267 个生产对象模块 map 相等**。每轮 274 个源码条目中，共同 272 个逐项相同，另各有本轮 Audit 和 exporter 两个路径，因此**两轮完整 source map 不相等**。规范解释见 [SNAPSHOT_SCOPE_CLARIFICATION.json](core/SNAPSHOT_SCOPE_CLARIFICATION.json) 与 [独立范围复核](consumer/scope-review/INDEPENDENT_SCOPE_REVIEW.md)。

23 个接收组件中 **20 个有本轮对象快照**。旧 `PairedCertificateChecker`、`PairedFibreIntegral`、`RationalLogCertificate` 三个既不在本轮对象采样，也不在本轮 source snapshot；它们的当前源码身份来自固定 d036 Git 源与旧供应源的比较。原 producer 编译/重放/审计、118 个完整旧类型及本轮实际根重放标记均保留，不能把旧对象散列填作新对象散列。另六个 VE 生产模块也不在该导出器对象范围，所以 267 个 map 不是全部 276 个项目模块，更不是全部外部依赖。

生产对象本体并未全部归档；类型导出捕获的散列也不是在先前 root replay 每个 marker 的同一时刻打印。P2 三个新生产 `.olean` 的新旧记录散列均不同，虽然源码逐字节相同、400 项类型及公理六字段逐项相同。回执严格保留这种区别，不推测散列变化原因。[P2 独立实际核对](core/p2-independent-review/ACTUAL_P2_CORE_REVIEW.md) 另有 1318 项检查及逐条原 stdout/job 字节位置。

首次实际消费使用 SHA-256 `925ebb6e12e1693635ca56dfbf58fc548e5ee350897079a95b0bf11b63b6ed63` 的脚本，错误要求 23 个历史组件全部被根**直接** import，172 项通过后以消费者 `EvidenceFailure` 停止。实际固定根经传递导入已包含旧三模块。修正版 `5d697e55919c1e8a35053fbfb662605839ddba9319266b3ed97bc9a497c20e18` 核对固定源图可达性，并继续硬性要求本批四模块直接 import、显式 target、当前对象采样及所有六门。原失败与补丁保存，独立审查确认其他证明门没有放宽；第二次消费使用**同一个原始 artifact**，没有重跑 CI。此消费者错误与真实 Lean 错误分开。

## 4. 本批可交付的数学接口

### P1：实际储存 cap 的有限许可

`ImbalancedChen.storedMeshCapCheck_actual_square_gates` 把有限表 `J/I/old/nu/cap` 的 checker 成功落实到同一实际元组的严格前缀平方门和所选子乘积平方门。完整可读声明及原 producer 类型见 [KEY_INTERFACES.md](../../round4/intake/p1-intake/KEY_INTERFACES.md)；本次 14 个新 `pp.all` 在 [实际 Round4 清单](core/verified/actual-round4/declarations.json)。P1/P2/P3/P4-A/P5 仍须提供实际采用表、checker 成功、`old j` 与继承历史的等式、覆盖和物理支持；这个有限许可没有关闭完整历史积分或 K。

### P2：same-mask-v2 前 64 格真实积分

采用证书仍是 **same-mask-v2，共 17572 行**。本批仅将原 E0 `[4,64)` 六十行追加到已验 `[0,4)`，旧四行只计一次。以下是在 `ImbalancedChen.Certificates.PairedV2.Prefix64` 中的**完整源码声明头**，不省略量词或参数；编译器原文另见 [本次五个完整 pp.all](core/p2-independent-review/ACTUAL_CORE_FIVE_PP_ALL.md)。

```lean
theorem integral_semantics :
    integral = ((K : ℝ) / 80) * ∑ i : Fin 64,
      ∫ t in (tLower (rowIndices i).1 : ℝ)..(tUpper (rowIndices i).1 : ℝ),
      ∫ u in (uLower (rowIndices i).2 : ℝ)..(uUpper (rowIndices i).2 : ℝ),
      ∫ z in (a : ℝ)..(rowZ i : ℝ), ∫ w in (a : ℝ)..z,
        1 / (t * u * z ^ 2 * w)

theorem integral_bounds :
    (lowerBound : ℝ) ≤ integral ∧ integral ≤ (upperBound : ℝ)

theorem integral_eq_parts :
    integral = Prefix4.integral + Batch4To64.integral

theorem source_ordinal_coverage (n : ℕ) :
    ((∃ i : Fin 4, Prefix4.rowOrdinal i = n) ∨
      (∃ i : Fin 60, Batch4To64.rowOrdinal i = n)) ↔ n < 64

theorem rowIndices_injective : Function.Injective rowIndices
```

`rowIndices : Fin 64 → ℕ × ℕ`、`rowZ : Fin 64 → ℚ` 由原四行与新六十行 `Fin.append` 构成，`integral` 是其真实 `pairedLocalIntegral` 有限和。共同有理常数为 `a=417/5000`、`h=19/125`、`d=59/250`、`mu=25/128`、`K=8452171/1250000`；网格保持 512 等分，`tLower i=mu+(d-mu)*i/512`、`tUpper i=mu+(d-mu)*(i+1)/512`、`uLower j=a+(h-a)*j/512`、`uUpper j=a+(h-a)*(j+1)/512`。所有行值与精确定义见 [完整可读接口](interfaces/p2-readable/READABLE_INTERFACES_ZH.md)；该早期文件的 producer 来源标签保持原样，本次实际确认由上面的新核心原文补充。

| 积分对象 | 下界分子（分母 `10^20`） | 上界分子（分母 `10^20`） |
|---|---:|---:|
| 原四行 | 12676565261567 | 12676572571081 |
| 新六十行 | 190579962282066 | 190580072663307 |
| 合计前 64 行 | **203256527543633** | **203256645234388** |

核心中的 400 项与固定 producer 在 name/module/kind/type/readable_type/axioms 上全部精确相等，未规范化或简化。积分系数只使用一次 `K/80`；有限格行号及坐标无重复不替代完整历史 mask、几何并域或误差证明。P4-A 的完整上界证书范围也没有因这批 E0 下界数据而扩大。

### P5：额外上游 Rosser 组件

固定依赖 `MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser` 的 **8 项**有匹配 producer 严格编译、同对象 stock replay、全所属声明公理审计，单列而不加入 23 模块或 1005 类型。它提供真实差集单位权、严格端点 `ceil((1-ε)N)-1`、Rosser/totient 主项减 AP 前缀误差；完整类型见 [PUBLIC_TYPES_COMPLETE.md](../../round4/intake/p5-intake/PUBLIC_TYPES_COMPLETE.md)。它的 explicit / 原始 Expr 输出不改称 `pp.all`，未进入根依赖闭包的目标也不由根 CI 自动覆盖。AP 支付、主质量、密度/尺度、InitialSource 同对象补审计、InitialMean、十一项完整均值与 c/hLower 继续开放。

## 5. 最终条件式主桥：完整类型与语义

下列是 [CurrentMainTheorem.lean](../../../../../ImbalancedChen/CurrentMainTheorem.lean) 的完整源码声明头，省略的只有证明体。**本次** Round3 和 Round4 实际导出的完整 `pp.all` 另附于 [ACTUAL_FINAL_BRIDGE_TYPE.txt](core/verified/ACTUAL_FINAL_BRIDGE_TYPE.txt)，原记录与标准三公理见 [ACTUAL_FINAL_BRIDGE.json](core/verified/ACTUAL_FINAL_BRIDGE.json)。

```lean
theorem current_theorem_1_1_of_manuscript_bounds
    {b : ℝ} (hbLower : (1 : ℝ) / 2 < b) (hbUpper : b < 1)
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (RealB b N : ℝ) ≤
          (currentK * Real.log (1 / b) + epsilon) *
            singularNormalization N) :
    ((currentC - currentK * Real.log (1 / b) : ℝ) : EReal) ≤
      Filter.liminf
        (fun N : ℕ =>
          (((RealDb b N : ℝ) / singularNormalization N : ℝ) : EReal))
        evenNatAtTop
```

常数仍为 `currentK=8452171/1250000`、`currentC=49044063/25000000`，归一化为 `singularSeries N * N / (log N)^2`，没有额外前置因子二。实数 `b` 先固定于 `1/2<b<1`，再对每个正 epsilon 控制全部充分大的偶数 N；不能改成三个有理实例或某条偶数子序列。`RealDb` 按加法素数 p 计数；`RealB` 是在 `D12` 中的精确补集，保留 `q^b<r≤q` 的严格有序区域与素数平方情形，不产生因子见证重数。现有 factor-four 桥、实际权、计数和尺度均未改写。

本次回执明确为 `hLower_hUpper_discharged=false`。真正应由 P5 和 P4-B 分别交出的无附加分析前提终端类型、共同 rho 的 K 供应及完整 Chen 均值规格见 [ANALYTIC_OPEN_INTERFACES.md](interfaces/ANALYTIC_OPEN_INTERFACES.md)。该附页保留编写时固定 d036 及旧候选身份；后续 P4 的新执行状态以下节为准。P0 将在 `CurrentMainComplete.lean` 的证明体内调用闭合供应，继续复用本条件式桥。

## 6. 后续分批交付：已读到成果，尚未收入生产根

**P3 新交接**没有改动生产源码。`Part3PrimeAPDistribution.lean` 的真实前端于 `1:0` 因 `ChenQuotientSieveRemainders.olean` 不存在而失败，exit 1、3.326 秒；缺失导入对象 **185 = 184 个 goldbach 模块 + 1 个项目前置模块**，另加目标尚无对象。13 theorem / 2 def 目前仍是完整源码声明头，新增编译器确认类型为 0。源码审查保留真 li 中心、统一阈值、公共 `L<p≤U`、移动互素余数、`|w d|≤1` 和前缀相减的系数 2；高模数、phase、实际 rho 接口未闭合。[回执与首诊断](late-intake/p3-f3ad8cbe/INTAKE_REPORT.md) 保存原始日志，未将“检索不到”作为没有成果的证据。

**P4 新专项** [run 38288356713](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38288356713)、job `114942066124` 的最终状态为 failure，但已有真实部分成功：五目标构建、五次强制 strict、五次 individual stock replay、Audit 均通过；前 17 个阶段成功。实际审计清点 **73 项 = 68 theorem + 5 def**，五模块依次为 13/7/11/38/4；包括 53 个公开源码 theorem、1 个 private 和 14 个生成 theorem。73 个实际完整 `pp.all` 与逐项公理由原始 Audit stdout 派生保存，不能再称为仅源码。

第 18 阶段 `leanchecker --fresh --verbose verification.Part4UpperAudit` 在 1800.037 秒超时，实际首失败是 `TimeoutExpired`；没有 Lean 源码错误位置。fresh 日志只有 161 bytes 命令头，完成 marker 为 0，不推断已经重放哪些模块。末尾 HEAD、source/dependency/object/binary 复核和四个正式 producer export 未达，五模块**尚未整体验收或收入 d036**。完整部分成功、失败原件和派生类型见 [P4 实际回执](late-intake/p4-1089a965/receipt-prep/actual-consumed/ACTUAL_P4_RECEIPT.md)。这些派生文件没有伪造缺失 export 或把失败改成成功。

P1 两个第五层候选已取得真实固定源码：`HistoricalUpperFiveCellGeometry.lean` 的 SHA-256 为 `0d54b930393ef01dbc9c44fbec5f356bf6be9a645a1a537064179fc12799424b`，`ActualHistoricalFifthCellIntegral.lean` 为 `550602f634e27641bf1f0b811e5e201130f48587bd0760192d032b75c0c405de`。这两份及 probe/audit 未到 frontend，仅保存候选身份。另一个“继承前层选择、仅过单模块编译”的独立报告仍缺可一一对应的固定源码与原始回执，不能与这两份合并身份，也不能宣称其已在基线整体验证。

## 7. 未闭合输入与接收顺序

| 接收方 | 仍需真实提供的输入 |
|---|---|
| P2 / P4-A / P5 | P1 完整历史选盒、合法性、支持、实际表及几何并域/积分身份；不能用有限表 checker 代替全构造 |
| P2 / P5 | same-mask-v2 剩余 E0 `[64,6091)`、E1 `[6091,17572)` 共 17508 行，saved-floor 语义、Y6/Y11 全配对和误差总账 |
| P4-A → P5 / P4-B | 同一次实际 rho 的 majorant、非零支持、参数许可、全政策积分与 reserve、编译系数误差、真实解析 K |
| P3 → P4 / P5 | 对该实际权/源/完整物理模数的分布、互素修正、质量与归一化误差；保留真实区间和量词 |
| P5 → P0 | 完整当前十一项 Chen 均值、真实解析 c、已支付误差后的 hLower；**只依赖 P4-A，不等待 P4-B** |
| P4-B → P0 | 同 rho 的真实 RealB 上界，消去 majorant/density/coprime/distribution 的未证供应前提 |

后续仍按固定提交或补丁分批接收；已成功同源码记录先复用，新增模块必须显式验证。既有入口 `bash verification/parts/p0/check_batch.sh p1-permit`、`p2-prefix64`、原 Round3 与新增 Round4 类型脚本及 workflow 根三门全部保留。失败、超时、未运行或缺末尾绑定仍按实际状态记录，不重跑没有必要的同版本 CI，也不降低 P4 所要求的 fresh 门。

本轮没有启动 Codex CLI/任务，没有新增 `sorry`、`admit`、自定义公理、`native_decide` 或 `unsafe` 证明绕过方式；没有干扰 P1 的健康构建。本机无法正常启动 Lean 的既有阻塞与真正运行的托管 CI 分开记载。当前交付完成的是**固定集成 SHA 的规定验证和可追溯组件接收**；数学上的最终上下界保持公开待供状态。
