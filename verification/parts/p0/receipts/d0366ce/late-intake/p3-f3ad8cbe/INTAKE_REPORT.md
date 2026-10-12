# P0：P3 固定后续交接接收回执

## 接收决定

**接收这批诊断证据；新增可接收证明为 0，新增编译器确认类型为 0。** 固定交接 `f3ad8cbe43c61c903857c7411626ee8c56f4f2f9` 没有改变任何生产 Lean 文件。`Part3PrimeAPDistribution` 的源码与当前集成台账中的固定候选逐字相同；新证据把该候选的状态从“当前源码尚无编译记录”补充为“一次真实严格前端启动后，因缺失导入对象而失败”。没有目标对象、内核重放或完整所属声明公理审计，不能因此升级为已验模块。

本接收仅写外部 `late-intake/p3-f3ad8cbe/`。它是**没有进入集成 `d0366ce64272e81faf6166a8a90050f56b328d38` 的后续交接**，没有修改该提交、公共根导入、其他 Part 分支或源代码。当前核心 Actions 运行由 P0 root 统一监控；这份回执不报告该运行的结果。

## 固定版本与字节身份

| 项目 | 完整身份 |
| --- | --- |
| 共同证明起点 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 手稿起点 | `ba6ec11d800eccc54406490631895e174de85766` |
| 新 P3 固定交接 | `f3ad8cbe43c61c903857c7411626ee8c56f4f2f9` |
| 新 P3 tree | `58475622f4fede39ae9fe9749b51da2255578133` |
| 新交接父提交，也是实际诊断起点 | `f37f341412eb239f7e7e8937921ee8d01c9c2922` |
| 父 tree | `b6bcbedaf527e8894fd4d05a1df1d68463b47ac5` |
| 既有候选证明源码起点 | `7d70a2545fd819706e473eb41e4d430ad19119d8` |
| 对照集成提交 | `d0366ce64272e81faf6166a8a90050f56b328d38` |
| 对照集成 tree | `e2ab22b96f76c8969386296558c626c62a581700` |
| 原固定 goldbach 依赖 | `09b97db5764ade1246bfb77206baa1b124760958` |
| 原固定 mathlib 依赖 | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| 原工具链 | `leanprover/lean4:v4.33.0-rc1` |
| 目标文件 | `ImbalancedChen/Part3PrimeAPDistribution.lean`，9873 字节 |
| 目标 Git blob | `2d761133b313302ab3a89ae906eb6944037a093d` |
| 目标 SHA-256 | `55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc` |

本地固定 Git 对象核对了父子关系、完整父树清单和所有 348 个起始 blob。新提交保留其中 347 个原字节，只更新 `docs/part3-distribution/README.md`；另新增 `verification/parts/p3/prime-ap-distribution/` 下 18 个证据文件。19 项改动没有 `.lean` 生产文件。适用固定 P3 树内没有 `AGENTS.md`。

原 `lean-toolchain`、`lakefile.toml`、`lake-manifest.json` 以及 P3 原有完整验证脚本、审计源和 workflow 与父提交保持一致。11 个依赖 pin 记录和实际 manifest 已逐项比较；其中 Cli 在这份静态导入图内有 0 个源模块，因此该行只提供固定 HEAD 信息，没有非空导入闭包的 tree-read 字段。

## 第一处真实 Lean 诊断

实际日志来自固定交接中的 `strict-compile.log`，共 669 字节，SHA-256：

```text
0ee68f39f130d11d396a96e0e66655a39d3380879b0751d45c027f33c8d5400e
```

原日志第 5 行是第一处、也是唯一一处 Lean error：

```text
/workspace/scratch/e8f85e58ac36/goldbach-formalization/ImbalancedChen/Part3PrimeAPDistribution.lean:1:0: error: object file '/workspace/scratch/127408f63891/goldbach-formalization/.lake/build/lib/lean/ImbalancedChen/ChenQuotientSieveRemainders.olean' of module ImbalancedChen.ChenQuotientSieveRemainders does not exist
```

这次调用确实出现了 `FRONTEND_START ... trustLevel=0 strict=strict` 与 `Lean.githash=62eed1db4d67327ec8120be05f1a1b0847d74561` 标记。详细回执记录 **exit 1、3.326 秒、没有超时**。失败位于源码第一个 import 的 1:0，没有到达目标声明的 elaboration；因此它不构成该模块某个证明体有误的诊断。

原始合并 stdout/stderr 里 `FRONTEND_FAILED` 行出现在 `FRONTEND_START` 行之前。这里保留原字节与行号，不把缓冲后的行序改写为执行时间顺序。

| 实际生产者门 | 固定记录及接收状态 |
| --- | --- |
| 严格前端 | 已执行，`trustLevel=0`、`warningAsError=true`，exit 1，3.326 秒，缺失首个导入对象 |
| 目标源前后身份 | 相同，均为 `55319b7e…b8c7fc` |
| 目标对象前／后 | `{}`／`{}`，没有生成目标 `.olean` 或旁文件 |
| 两个直接导入对象前／后 | 各为 `{}`／`{}` |
| stock kernel replay | 未执行：没有目标对象、导入闭包不完整 |
| 完整所属声明传递公理审计 | 未执行：所属 private/generated 声明清单尚不存在 |
| 编译器确认完整类型 | 0 |
| 生产者前置模块构建／全库构建 | 均未启动 |

实际调用和 cwd 原样保存在 `INTAKE_RECEIPT.json`；详细生产者回执 SHA-256 为 **`694bf9e6692bc6416327ddd4b2557321a7d7c338cc6e21635a3f534d2d72e3d6`**。

生产者配置与工具／驱动 before-after 记录一致；归档中的真实驱动源与其记录哈希也一致。本消费者没有那些运行时二进制的完整载荷，没有重新 hash 或运行它们，因而只确认回执绑定，不补造本地运行时验证。驱动源含既有 `unsafe Lean.enableInitializersExecution` 运行时初始化调用；本交接没有新生产证明源码或绕过式证明接收。

## 原始归档与静态导入清单

| 证据载荷 | 字节／SHA-256 |
| --- | --- |
| `inventory-evidence.tar.xz.b64` | 642659；`efc8e9b091ef4af3ceb8137dc80a3ca2516f62820758b1ed9ebb2130a3113e79` |
| 解码的 `inventory-evidence.tar.xz` | 475732；`f640715b4891d7f32c937223a437b1c7eb804d49a743145ee4d889c35b037984` |
| `source-import-inventory.json` | 5015925；`3c0a56f910d0cee5af6ef11e465c85817a3f1c22dbe5ac111b8b332f3fe63227` |
| `source-restoration.json` | 120442；`af0365a1ffec5b8074d16faa3958484750825a274be36b67d0de5981da511f8a` |

17 项外层 manifest 与全部 6 个归档成员的实际大小和 SHA-256 均重新核对。六个成员都是普通文件，没有生产 `.olean`：目标源码、父 commit 元数据、父递归 tree、原前端驱动源、静态导入 inventory、原源码恢复清单。

静态 inventory 的 6472 个唯一模块都能在其记录的源导入图中从目标到达；逐行重算得到：

| 记录分组 | 模块数 | 记录缺失对象数 |
| --- | ---: | ---: |
| Lean 原运行时 | 2323 | 0 |
| mathlib | 3580 | 0 |
| goldbach | 270 | 184 |
| 项目 | 25，含目标 | 2，含目标 |
| 其他包 | 274 | 0 |
| 合计 | 6472 | 186，含目标 |

所以**缺失导入对象为 185 = 184 个 goldbach 模块 + 1 个项目直接前置模块**；加上尚未产生的目标，缺对象总数为 186。两个直接 import 的源 SHA 和实际源码已独立核对，其中 goldbach 的 `Bombieri1965Richert418Unconditional` 同样缺对象。

这些数值属于生产者当时的**静态源图与文件存在性记录**。它们不是实际已导入的 Lean 环境清单，也不证明某个已有对象由同一源码产生，更不能推出 P0 当前环境或全局缓存里也没有对象。原归档搜索只覆盖生产者列出的 11 个具体归档，不作全局无缓存结论。

25 个项目源已逐项对照父提交、新交接和 `d036`；其中 24 个在 `d036` 为同字节生产源，目标只在候选快照中。11 包完整 source closure 的证明者记录一致性已审阅，但本消费者没有独立读取全部上游数千个 blob；独立取得并 hash 对照了本次接口所需的 6 份固定 goldbach 文件。

### 可复用的既有直接前置模块回执

旧集成 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` 的实际 core artifact 记录了相同源 SHA 的 `ChenQuotientSieveRemainders`，并且原 root replay 日志确有该模块标记。其 `.olean` 摘要为：

```text
c62597fdb4936de3059195a9f2490f4e55f63915141a685ff5f14603d75f0aaf
```

这份证据载荷与 `d036` 已保存的旧 artifact 字节一致；`PRIOR_DIRECT_IMPORT_EVIDENCE_REUSE.json` 记录完整归档、成员和源／对象绑定。旧 artifact 没有运输这个 `.olean` 二进制，所以不能声称它已恢复到 P3 当时的运行环境；它也不供应缺失的 184 个 goldbach BV 导入对象。

## 声明类型身份与实际供应范围

`SOURCE_TYPES_15_SOURCE_ONLY.json` 与同名 Markdown 包含全部 **13 个 theorem、2 个 def 的完整源码声明头**，保留 namespace、open 范围、量词和常数。两个独立的源码提取结果逐项相同。每项均标为 **SOURCE_HEADERS_ONLY_NOT_COMPILER_TYPES**；这不是 `#print`／`pp.all` 输出，15 也不是未来完整所属声明数的上限。

| 类型载荷 | SHA-256 |
| --- | --- |
| 原交接 `SOURCE_TYPES.md` | `2605907758c72ead1da9d6539f87fc170cba62301c734909cc9ada931a1ad0db` |
| 原交接 `source-declarations.json` | `ed2dc933daa5c86b7a5b9780dfa00d55c55d8b375d016b7636b0c0636b68c3cf` |
| P0 完整 15 项 `SOURCE_TYPES_15_SOURCE_ONLY.json` | `c3e36d4a78cfff552336f90dba28773caed8b87c26c368320ffbf2019ba53d19` |
| P0 完整 15 项 Markdown | `36c23ea7e6ffef3a61562401752d1cedc129ac9f7611842f8b35ec0f681d4441` |
| 独立供应范围审查 | `supplier-scope-review/SUPPLIER_SCOPE_REVIEW.md`，`532a46357f39c622331e448f8e6edaf8d6f2f410bf04fcbe2fdcc7f34c3466b1` |

实际定义已经阅读并固定：

```lean
noncomputable def panModulusCutoff (N : ℕ) (B : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B)

noncomputable def liuLogarithmicIntegral (κ x : ℝ) : ℝ :=
  κ + ∫ t in (2 : ℝ)..x, 1 / Real.log t

noncomputable def trueLogarithmicIntegral (x : ℝ) : ℝ :=
  LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) x
```

因此这里是完整物理模数的普通平方根／对数 BV 截断，真实素数计数中心保留 `2 / log 2` 的固定加法项。计数为 `p ≤ Y`，不在实际计数定义中增加互素掩码。BV 接口的互素条件施加在移动余数上；`w : ℕ → ℝ` 是有限模数集合上的权，要求 `|w d| ≤ 1`。区间是公共端点 `L < p ≤ U`，保留两个前缀相减产生的系数 2。

固定上游的 `standardBombieriVinogradov` 是类型为 `StandardBombieriVinogradov` 的 theorem；后者是展开为 ∀ A 的 Prop 定义。P3 源码按 `A hA` 使用这个已写出的证明项，在源码接口层没有把 Prop 定义直接当成证明，也没有新增 `hBV` 参数。这个源级观察仍不能替代目标及上游闭包的实际内核、公理检查。

关键完整源码类型另见下方自动摘录附录；均未经编译器确认。

## 与冻结集成台账的对齐

7 个既有 P3 模块源摘要全部与新交接一致。`Part3LongSlotDistribution` 和 `Part3LongSlotNormalization` 延续原固定源验证范围，分别有 35 和 2 个已收到完整类型；本次未重复运行这两个同版本构建。其他 5 个 P3 组件仍为候选。

完整台账仍是 **37 个组件、23 个有生产者通过证据、14 个待验**；这份后续交接不改变它们，也不增加 `d036` 的根验证状态。`D036_LEDGER_ALIGNMENT.json` 只提供外部覆盖建议，保留 `d036` 原计数和原验证范围。类型格式继承也不变，不能把原来的默认完整输出改标成 `pp.all`。

| 接收 Part | 本批可接收内容 | 未闭合输入 |
| --- | --- | --- |
| P0 | 固定证据、真实首诊断、候选状态与接口审查 | 不将目标导入生产根；实际 source/object/import 绑定后的三门验证仍缺 |
| P3 | 184 个 goldbach 缺对象清单、1 个同源项目前置对象缺项；旧项目对象回执可复用 | 完整固定 BV 对象闭包、目标显式严格编译、stock replay、全部所属 private/generated 传递公理审计、完整编译器类型 |
| P1 → P3/P4/P5 | 后续可实例化的 `S`、`a`、`w` 和公共端点范围 | 实际构造的完整物理模数 cap、互素余数、系数界、真实计数和因子化身份；不能用一个辅助因子的范围代替 `b*d` 范围 |
| P4-A／P4-B | 普通 BV 的候选 AP 误差接口 | 高物理模数／素数乘积／相位分布、同一实际 rho 的 K 解析密度和完整 hUpper |
| P5 | 真实 li 主项的 quotient 误差池候选 | 完整 Chen 均值、实际源／权／质量／归一化与中心修正、真实解析 c 和 hLower；仍只需等 P4-A，不需等 P4-B |

本候选没有移除真实筛余项中的中心素数修正，也没有闭合 rough/Möbius SW、medium/two-long、Brun–Mellin／共同谱包、实数参数和实际 rho 的完整分布供应。K、c、hLower、hUpper 的供应没有被藏入新结构或类型类。

## 本消费者实际执行的核对

执行 `python3 p0-round4/late-intake/p3-f3ad8cbe/verify_late_intake.py` 得到 **563 项离线证据一致性核对通过**；另有 **17 项独立供应范围审查的源／声明头交叉核对通过**。这些 PASS 只属于消费者证据检查，不是 Lean 编译、内核重放或公理门通过。

第一次运行消费者时，Cli 的零源闭包行缺少 `tree_read_returncode` 字段，触发一次消费者 `KeyError`。原消费者字节和错误记录保存在 `consumer-preparation/`；修正为对非空闭包核对 tree-read 状态、对零闭包只核对 HEAD 和数量后，得到上述 563 项结果。该消费者错误没有替代或覆盖生产者的真实 Lean 首诊断。

未执行 Lean、Lake、Elan、leanchecker、生产者脚本、CI 轮询或任务、环境重建和进程信号。只进行了固定 Git 对象读取、JSON／归档／哈希检查和必要的固定 GitHub 文件 API 读取。

### 文件入口

- `INTAKE_RECEIPT.json`：可机器接收的本批结论、实际门状态、SHA、未闭合输入和范围限制。
- `D036_LEDGER_ALIGNMENT.json`：冻结台账与后续诊断的外部覆盖建议，不改变旧提交。
- `FIRST_REAL_LEAN_DIAGNOSTIC.json`／`.txt`：第一处真实 Lean 诊断及原始日志身份。
- `SOURCE_TYPES_15_SOURCE_ONLY.json`／`.md`：全部 15 个完整源码头，编译器确认数为 0。
- `CHECKS.json`／`SUPPLIER_REVIEW_CHECKS.json`：563 + 17 个离线检查。
- `PRIOR_DIRECT_IMPORT_EVIDENCE_REUSE.json`：旧固定 core 中同源直接前置模块的可复用记录。
- `fixed-source/`、`archive-evidence/`、`upstream-api/`、`upstream-fixed-source/`：保持固定来源身份的实际原件。
- `OUTPUT_MANIFEST.json`：本接收目录全部交付文件的最终大小及 SHA-256，排除 manifest 自身。

## 附录：三个关键接口的完整源码类型

以下三个声明与完整 15 项源清单同源，均在原 ImbalancedChen namespace 和原 open 范围内；**未经编译器确认**。

### ImbalancedChen.part3_abs_sum_mul_primeAPError_log_saving

```lean
theorem part3_abs_sum_mul_primeAPError_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ Y : ℕ, Y ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            ∀ w : ℕ → ℝ, (∀ d ∈ S, |w d| ≤ 1) →
            |∑ d ∈ S, w d * part3PrimeAPError Y (a d) d| ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ A
```

### ImbalancedChen.part3_abs_sum_mul_primeAPIntervalError_log_saving

```lean
theorem part3_abs_sum_mul_primeAPIntervalError_log_saving
    (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ L U : ℕ, L ≤ U → U ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            ∀ w : ℕ → ℝ, (∀ d ∈ S, |w d| ≤ 1) →
            |∑ d ∈ S, w d * part3PrimeAPIntervalError L U (a d) d| ≤
              2 * (C * (N : ℝ) / Real.log (N : ℝ) ^ A)
```

### ImbalancedChen.part3_chenQuotientPrimeAPError_pool_log_saving

```lean
theorem part3_chenQuotientPrimeAPError_pool_log_saving
    (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ A
```
