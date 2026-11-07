# Part 0 第三批：P5 固定交付接收审查

## 结论

本次只读接收已找到 P5 的实际最新固定提交 **`bf54caeb5e708474cacefac13a171d307b4c64f2`**。
远端 branch ref、Git commit 和完整 recursive tree 已读取；远端 tree
`3401b11f5299cea2d7351f7d6d164c817d12da4b` 的 **533 个 blob** 与本地固定 Git 对象逐一相同。
已从固定提交提取 **176 份**源码、交接和原始验证文件，不依赖本地未提交文件解释证明状态。

可立即复用的一项独立成果是固定 goldbach 依赖中的
`MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier`：生产者已完成严格编译、原装内核重放和
36 个所属声明的完整传递公理审查，调用前后源码及对象身份记录齐全。
其额外完整类型查询覆盖 17 个公开定理。默认的 36 声明类型清单有两处生成类型省略，
因此本接收单不称这 36 项都已完整打印。

`ImbalancedChen.CurrentChenInitialSource` 的修复已在
`a03a57265a49d542e6fac8ba72094dd673e5ed7d` 固定，当前交接源码逐字相同；
生产者三门也都通过，8 个所属声明无类型省略。
但是它沿用旧记录 schema，没有审计导入对象前后身份。
若保持 P0 上批接收标准，应复用已有严格编译及生产重放，仅补同对象审计绑定，
不能补造历史字段。本次没有启动这项补审计。

`CurrentChenInitialMean` 仍是固定源码候选，不是已证采用 L1，也不提供完整十一项均值或 `hLower`。

## 版本、归属与来源

| 项目 | 固定身份 |
| --- | --- |
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 上轮 P0 接收 | `80aca6710c83b5160f4c5fdd05d180e507990e95` |
| P5 上轮固定交付 | `bd83a110ee52626daf9e68535c007eb73a93daca` |
| InitialSource 新固定证明 | `a03a57265a49d542e6fac8ba72094dd673e5ed7d` |
| 随后的用户 CI 超时提交 | `8980571613d4980830e237d1135109a3149e8982` |
| P5 最新固定交付 | `bf54caeb5e708474cacefac13a171d307b4c64f2` |
| 分支 | `chatgpt/chen-p5-lower` |
| 手稿 | `ba6ec11d800eccc54406490631895e174de85766` |
| Lean | `leanprover/lean4:v4.33.0-rc1` |
| Lean githash | `62eed1db4d67327ec8120be05f1a1b0847d74561` |
| goldbach | `09b97db5764ade1246bfb77206baa1b124760958` |
| mathlib | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |

P5 原有 Buchstab、CurrentChenMeanLedger、CurrentChenLowerScale 三份生产源码与 bd83 完全相同。
本轮没有重复验收它们的证明。
工具链、manifest、主定理、数值转移、手稿地图及 P5 自己的公共根均与共同基线逐字相同。
2026-10-12 12:01 UTC 的只读检查确认 P5 本地十一项依赖 checkout 全部 pin 相符且 tracked clean。

从 bd83 到最新 P5 的生产源码改动只有：

- `ImbalancedChen/CurrentChenInitialSource.lean`：真实诊断后的证明修复；5 个公开定理头不变。
- `ImbalancedChen/CurrentChenInitialMean.lean`：按已发现命名空间问题修复候选；1 个定理头不变，仍未编译。

用户的 `.github/workflows/lean.yml` 超时改动单独属于 898057；本接收单不指示合并整个 P5 分支。
公共根、共享状态和最终入口仍由 P0 负责。S1Carrier 是既有固定依赖源码，不能复制成新定义或更换依赖 pin。

## 三项门与对象身份

| 模块 | 严格编译 | 原装内核重放 | 所属声明公理审计 | 接收范围 |
| --- | --- | --- | --- | --- |
| S1Carrier | exit 0，118.928 秒 | exit 0，41.873 秒 | exit 0，366.102 秒；36 项 | 已有三门可复用；17 公共类型完整；2 个生成类型打印待补 |
| CurrentChenInitialSource | exit 0，258.283 秒 | exit 0，210.823 秒 | exit 0，680.789 秒；8 项 | 旧 schema 缺审计导入身份，按 P0 标准等待补绑定 |
| CurrentChenInitialMean | 无同源完成回执 | 未完成 | 未完成 | 源码候选 |

两项生产编译均使用原装 Lake 调用官方 `Lean.Elab.runFrontend`，`trustLevel=0`，
warnings as errors。重放命令都是原装 `leanchecker --verbose MODULE`。
生产者没有使用 `--fresh`，所以没有将导入缓存说成本批全部重新重放。
完整审计基于 `env.constants` 和 `getModuleIdxFor?` 枚举，覆盖 private/generated 声明，
逐项检查 unsafe、自定义 axiom 与传递公理。实际公理集合只含
`propext`、`Classical.choice`、`Quot.sound`。

| 模块 | 源码 SHA256 | Git blob SHA1 | `.olean` SHA256 |
| --- | --- | --- | --- |
| S1Carrier | `757bdcea11195c48ed5814f95a70737326853e68bfaa093711a4f6161e1a896a` | `28765e9a22a486a803cf2e87b1405184ad133574` | `6bd8d1615d37f2db31e57c57ed66672f5fd646a0dc7a73eaa0badcac24ac16bd` |
| InitialSource | `4b11a63cc976a0866068337c12d616578dace6c80736574311f4cca13f7d8956` | `147da5cdb46787f2befe7e21856fd4691190d0ac` | `8b9ee7b0e4f18ea06057a99f075e87065131e12873221e114b9c5d5c46a8ef39` |

S1Carrier 目标、审计和类型查询对象的现存字节已重新核对相同；InitialSource 现存目标对象亦相同。
S1Carrier 固定来源 snapshot 与本地 pinned goldbach Git 源逐字一致。
其历史三次门控记录的 direct imports before/after 完全一致，审计导入的 S1Carrier
对象哈希就是编译与重放的目标哈希。原始日志的哈希、审计 JSON 行和发布的类型清单也逐条吻合。

S1Carrier 的默认类型打印中，以下两项出现 `⋯`：

- `BoundingSieve.mk.congr_simp`
- `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve.eq_1`

两项仍已被安全及公理审计覆盖；区别在于完整类型输出。
后续的 17 公开定理查询输出 `pp.all` 与精确 `Expr`，没有 `⋯`，但不能覆盖这两个生成声明。
可补一次纯完整类型导出；不需要重编或重放 S1Carrier 生产证明。

## 真实首诊断与中断

InitialSource 原固定源 `2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767`
于 04:56 UTC 尝试，428.784 秒后 exit 1。首诊断保持为：

```text
CurrentChenInitialSource.lean:41:14: error: unsolved goals
p : ℕ
h : p ∉ {p | Nat.Prime p ∧ 2 < p}
hp : 1 + MathlibNt.SieveTheory.SingularSeries.liuBaseDeviation p ≠ 1
⊢ Nat.Prime p → 2 < p → ↑p - 1 = 0
```

原日志还包括 unused simp 与 `goldbachDifferenceCarrier` 未打开父命名空间的问题。
真实修复是把集合非成员假设转换成 `liuBaseDeviation` 的确切分支条件并显式重写，
以及打开既有 `LiLiuOnePlusOneNine` 父命名空间。
没有修改定理目标。修复后的 source/object 与 a03/bf54 固定源一致。

此前 S1Carrier 的 attempt 是 **INTERRUPTED_FOR_PRIORITY**：工具 session exit 130，
没有 frontend 最终返回码、没有成功目标对象。原始回执提到共享内存压力及用户授权的优先级处理。
本次新成功来自相同源码的后续正常运行，未把退出 130 改记为成功或 Lean 证明失败。

S1Carrier 的辅助 PublicTypes 脚本另有首次 68.676 秒 exit 1：使用 Lean 保留字 `prefix` 作为局部标识符。
改为 `declarationRoot` 后 71.024 秒 exit 0。这个脚本修复不改变生产模块或三门结果。

## 数学接口与尚未闭合的输入

完整关键类型位于 `KEY_THEOREM_TYPES.md`；其 8 项 InitialSource 编译器类型、17 项 S1Carrier
公开完整类型和精确 Expr 位于 `key-compiler-types.json`。
InitialMean 及直接供应者的类型另标为 SOURCE_EXTRACTED_NOT_COMPILER_CONFIRMED。

InitialSource 已证明：两个真实奇素数无穷乘积以及有限奇素数除子修正相等，没有额外 factor 2；
固定筛比 4 的实际下筛函数系数为 `(33/4) * log 3`；
实际 upstream S1 在较小 cutoff 的当前 sifted prime-difference source 上可由
`N.primeFactors.card` 支付删除成本；这项 distinct-prime-divisor 成本在
`singularNormalization` 下可忽略。这里使用 distinct prime factors 是删除例外素数的实际成本，
没有拿它代替半素数重数计数。

S1Carrier 已证明实际 support `goldbachDifferenceCarrier N ε`、常权 1、
严格终点 `Nat.ceil ((1-ε)*N)-1` 与真实筛素数乘积的有限载体关系；
筛素数保持 `(p:ℝ)<z` 且排除 `p ∣ N`。
其 sifted sum、totient main sum 以及 `standardPrimeAPError endpoint d (N % d)` 的精确对应已闭合。
`literalHPoint` 仍不等于差值与 N 互素，InitialSource 的 primeFactors 删除成本不能省去。

尚未验证的 InitialMean 完整候选目标是：

```lean
theorem eventually_currentChenUpsilon1_ge_initial_mean
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ((33 / 4 : ℝ) * Real.log 3 - epsilon) * singularNormalization N ≤
        currentChenUpsilon1 N
```

固定 SHA256 为 `5358e4dbbda436b335620de19884624df3260386d5ab5e478a85f70599da6137`。
它依赖 `S1BetaFixedNormalizedLower` 的实际供应闭包；虽然候选定理头没有新的分析假设，
不能据此称它已经通过编译，更不能称该系数是采用 L1。
完整十一项均值、相同采用 mask、真实 c 支持以及最终 `hLower` 仍未完成。
P5 的跨 Part 依赖保持 P1、P2、P3 与 P4-A；**不需要等待 P4-B 的 hUpper**。

按真实 imports，下一最小独立供应模块为：

```text
MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser
source SHA256 c07c0704c975bef4d772090ce03d7536f28edd319c700c4d9feb27c9f111ef62
sole import MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier
```

本次只提取了它的固定源码与完整定理头，未启动。
`S1MainMass`、`S1BetaPaidLower`、`S1BetaLowerDensity`、`S1BetaMainScale` 到
`S1BetaFixedNormalizedLower` 的真实 imports 和 source SHA 见 `p5-fixed-intake.json`。
其中 PaidLower 另需 `Bombieri1965Richert418Unconditional`，不能由 Carrier 的通过推断整条闭包已齐备。

## 当前可复现环境边界

本次工作全程没有启动 Lean、Lake、CI、Codex CLI 或 Codex 任务，没有发送进程信号。
12:00 UTC 左右的只读 `/proc` 快照未见 P5 同源码版本的活动验证。

维护清理后，旧回执中的 P1 package 源码路径与 Mathlib 编译对象路径有缺失。
P5 自己的十一项 pinned 源码 checkout 保留，目标对象也保留；
P5 的 Mathlib 对应对象同样未找到，旧 LEAN_PATH 不能直接当作现存正常环境。
这不撤销固定版本已经完成的历史三门，但限制当前补审计／补完整类型的立即执行。
原工具二进制路径存在；本子任务没有尝试启动。
`ps` 初始化自身库曾报 `fatal library error, lookup self`，随后用 `/proc` 只读快照代替；
该错误不是 Lean 诊断。

## 文件索引

- `p5-fixed-intake.json`：固定版本、历史门、当前身份、候选、未闭合接口和进程观察。
- `fixed-source-manifest.json`：176 文件的固定 commit、Git blob、SHA256 和本地冻结路径。
- `remote-fixed-read.json`：原始 branch ref、commit、recursive tree。
- `s1carrier-current-object-checks.json`：逐次调用的历史身份一致性与现存对象检查，明确记录缺失缓存。
- `initial-source-legacy-evidence-checks.json`：旧 schema 的真实范围，没有补造字段。
- `current-p5-source-pins.json`：当前十一项 pinned checkout 复核。
- `KEY_THEOREM_TYPES.md` / `key-compiler-types.json`：完整关键编译器类型与精确表达式。
- `source-theorem-types.json` / `next-lower-rosser-source-types.json`：明确标记的候选源码类型。
- `initial-source-and-mean-supplier-fix.patch`：bd83 到 a03 的两源真实修复。
- `historical-source/`：原失败／原候选源码。
- `fixed-source/` / `fixed-upstream/`：按固定 Git 身份提取的证据及后续供应者源码。

接收方：P0 集成验证、P5 首项均值供应链。是否把 InitialSource 升格为 P0 正式接收，
应在补齐本单列明的审计身份后记录在新的固定集成 SHA；不要把本只读接收单当作新执行的 Lean 回执。
