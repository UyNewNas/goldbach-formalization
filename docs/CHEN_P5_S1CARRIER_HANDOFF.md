# Part 5：S1Carrier 独立验证切片

## 验收结果与固定身份

本检查点只验收 `MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier`。
固定 goldbach 证明源码已完成严格编译、原装 `leanchecker` 内核重放和定义模块全部声明的传递公理审计。
没有修改该证明源码，没有补编依赖，也没有启动后续供应节点。
验收提交为包含本交接与回执的独立提交；发布时提供其完整 SHA。

| 身份 | 固定值 |
| --- | --- |
| 分支 | `chatgpt/chen-p5-lower` |
| 续接检查点 | `a03a57265a49d542e6fac8ba72094dd673e5ed7d` |
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| Lean | `leanprover/lean4:v4.33.0-rc1` |
| Lean githash | `62eed1db4d67327ec8120be05f1a1b0847d74561` |
| goldbach | `09b97db5764ade1246bfb77206baa1b124760958` |
| Mathlib | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| 原始及实际编译源码 SHA256 | `757bdcea11195c48ed5814f95a70737326853e68bfaa093711a4f6161e1a896a` |
| 目标 `.olean` SHA256 | `6bd8d1615d37f2db31e57c57ed66672f5fd646a0dc7a73eaa0badcac24ac16bd` |

发布前远端出现用户的 CI 超时提交 `8980571613d4980830e237d1135109a3149e8982`，仅改 `.github/workflows/lean.yml` 的超时为 150／90 分钟。该提交已完整保留为本验收提交的父提交；验证源码仍绑定上述 a03 检查点，Lean 源码、依赖和共同证明基线没有变化。范围证据见 [upstream-ci-advance.json](../verification/parts/p5/round3/s1carrier/context/upstream-ci-advance.json)。

其余九项依赖版本及原装工具二进制哈希见完整 [receipt.json](../verification/parts/p5/round3/s1carrier/receipt.json)。
全部十一项依赖保持固定版本且 tracked clean；工具链、根导入、手稿地图、主定理和数值转移文件均保持共同基线原始字节。
源码快照为 [upstream-LiLiuGoldbachS1Carrier.lean.txt](../verification/parts/p5/round3/s1carrier/source/upstream-LiLiuGoldbachS1Carrier.lean.txt)。

## 三项实际执行

| 检查 | 实际退出码 | 秒数 | 范围 |
| --- | ---: | ---: | --- |
| 官方 frontend 经原装 Lake；`trustLevel=0`、`warningAsError=true` | 0 | 118.928 | 当前固定源码、单模块、单线程 |
| 原装 `leanchecker --verbose MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier` | 0 | 41.873 | 重放目标模块全部数据部分中的声明，对照其导入环境 |
| 严格编译 `verification.parts.p5.S1CarrierAudit` | 0 | 366.102 | 实际定义模块全部 36 个声明的传递公理审计 |

审计从 `env.constants` 与 `getModuleIdxFor?` 枚举，包含 private 和 generated 声明。
实际共有 **36 个声明**，其中定义模块种类计数为 `{'theorem': 31, 'definition': 5}`，
带 private 名称的声明为 4 个；源文件显式公开定理 17 个全部在编译器清单中。
每个声明均通过 `isUnsafe`、`isAxiom` 检查，传递公理的并集恰为
`propext`、`Classical.choice`、`Quot.sound`；没有额外公理。
源码、目标对象及每次调用的直接导入对象前后哈希一致。

这是复用既有正常环境的官方 frontend API 编译，具体启动入口与 `lake build` 分开记录。
驱动中既有的官方 initializer API 只负责 frontend 启动；实际证明以 trust level 0 检查。
本批没有手动运行 CI 或重启旧供应队列。原装 checker 未使用 `--fresh`，因此不把导入缓存误称为本批全部重新重放。

- [实际命令、退出码、前后哈希与原始日志索引](../verification/parts/p5/round3/s1carrier/commands-and-results.json)
- [可阅读命令清单](../verification/parts/p5/round3/s1carrier/commands.sh)
- [全部编译器声明类型及逐项公理](../verification/parts/p5/round3/s1carrier/compiler-types.txt)
- [17 个公开定理的完整编译器类型](../verification/parts/p5/round3/s1carrier/public-theorem-types.lean.txt)

## 关键编译器确认类型

默认 pretty printer 会隐藏 `BoundingSieve.siftedSum` 等函数的隐式载体参数。
因此在三项验证完成后，另以严格编译的 `S1CarrierPublicTypes` 查询同一目标对象，
显式输出所有 17 项公开类型并保存完整 `Expr` 表示：退出 0，用时 71.024 秒。
该导出脚本首次因局部变量使用 Lean 保留字 `prefix` 而退出 1（68.676 秒），
仅改名为 `declarationRoot` 后重新执行。原始失败、修复补丁和源码身份均归档；目标 S1Carrier 的证明源码与三项通过结果不受影响。
该查询没有重跑证明或公理审计。以下为其编译器显式输出，所有实例和载体实参都保留；
完整 17 项见 `public-theorem-types.json`／`.lean.txt`，36 项声明的公理清单见 `compiler-types.json`。

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve_multSum_eq_primesInAP :
∀ {N : Nat} (hEven : @Even.{0} Nat instAddNat N) {ε z : Real} {d : Nat},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) →
      @Eq.{1} Real
        (@BoundingSieve.multSum
          (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve N hEven ε z) d)
        (@Nat.cast.{0} Real Real.instNatCast
          (MathlibNt.SieveTheory.BombieriVinogradov.primesInAP
            (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) d
            (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) N d)))

MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve_siftedSum_eq :
∀ {N : Nat} (hEven : @Even.{0} Nat instAddNat N) (ε z : Real),
  @Eq.{1} Real
    (@BoundingSieve.siftedSum
      (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve N hEven ε z))
    (@Int.cast.{0} Real Real.instIntCast
      (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1
        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachDifferenceCarrier N ε) N z))

MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve_mainSum_eq_totientSum :
∀ {N : Nat} (hEven : @Even.{0} Nat instAddNat N) (ε z : Real) (μ : Nat → Real),
  @Eq.{1} Real
    (@BoundingSieve.mainSum (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve N hEven ε z)
      μ)
    (∑ d ∈ (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z).divisors,
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (μ d) (@Nat.cast.{0} Real Real.instNatCast d.totient))

MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve_rem_eq_standardPrimeAPError :
∀ {N : Nat} (hEven : @Even.{0} Nat instAddNat N) {ε z : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) →
      ∀ {d : Nat},
        @Dvd.dvd.{0} Nat Nat.instDvd d
            (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z) →
          @Eq.{1} Real
            (@BoundingSieve.rem
              (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve N hEven ε z) d)
            (MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError
              (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) d
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) N d))
```

真实 `support` 保持 `goldbachDifferenceCarrier N ε`，权恒为 1；终点保持
`Nat.ceil ((1-ε)*N)-1`，筛素数保持严格 `(p:ℝ)<z` 并排除 `p∣N`。
差映射计数中的单射、偶数排除素数 2、`literalHPoint` 与真实筛素数乘积的对应均由原始证明保留。
主质量是 `trueLogarithmicIntegral endpoint`，余项中的模数和剩余类是实际的 `d`、`N % d`。
`literalHPoint` 仍不等于额外要求差值与 N 互素；`CurrentChenInitialSource` 的 primeFactors 删除成本仍需保留。

## 导入对象与缓存证据

| 直接模块 | 源码 SHA256 | `.olean` SHA256 |
| --- | --- | --- |
| `MathlibNt.SieveTheory.LiLiuGoldbachBasicToSieve` | `71990abce420705df93d5a253966db0f7e02092d16ac00535380cce6abcba29e` | `a8d52dae6c6e4bbc959fc21e34f65c7179effee83c26a3125cb1b6362aa9da67` |
| `MathlibNt.SieveTheory.LinearSieve` | `f7ce98fbbcf3d7baca1ef6a0a3829c0ee6de85c39e7d1a6935b8f013557c5d03` | `980be4eba7e02278ec8efb1a121ed4ed64be894d302e8c6978a482358667c551` |
| `MathlibNt.SieveTheory.BombieriVinogradov` | `17be57e0cc3542112ab4e558eb92c5e3a06e0839491a672205a01ebe3f554bc9` | `bcfdf76d4b503094d0040a0c3e99371b1b769014947f0a4cc0e16ad078243e02` |
| `Mathlib.Data.Nat.Cast.Order.Field` | `fc9a5b94982bffd9ecc57ed2362091e1ad67d21a0d6e7eac96656a50d191e6e6` | `06db2d666d564b2ff634197fcf1754af5299e40251cd1f1e4a6d7dfaa69a5597` |
| `Mathlib.Data.Nat.ModEq` | `678c7d5030c056efb633aaab3a1b44ceec599332b9f70f694b08f4cce27d1fea` | `d9fbc4f24ea4fc473eed6bb5f914d3eef3f1ef09bff39603c149ee0b60feacdc` |
| `Mathlib.Data.ZMod.Basic` | `c910cf5089e3f961c495763c0a6c9609bcb8033f500faa1e7e4f0666f7eb5f99` | `534773a6ba1d637d4c7ff382bc1b2b1c1af12cc7be4d2376fd1168675f3d0828` |

完整直接导入闭包中有 96 个本地已编译模块及 8679 个官方 Cache 源码模块。
96 个本地对象按固定源码、完成 frontend 记录、工具版本和对象哈希匹配，记录过的直接导入哈希也逐项匹配；原始完成日志已归档。
官方 Cache 复用有固定源码版本、官方内容哈希下载／解压成功回执，三个直接 Mathlib 导入另有既有成功编译的相同对象哈希见证。
目标所需缺失对象为零，所以本批没有补编依赖。
这 8775 是复用闭包的源码模块数，不是本批新重放或审计的模块数。
preflight 的 `source.git_blob` 字段存的是 `git show` 内容的 SHA256，非 Git 的 SHA1 对象标识。

详见 [preflight.json](../verification/parts/p5/round3/s1carrier/preflight.json) 与
[直接缓存见证检查](../verification/parts/p5/round3/s1carrier/cache-direct-witness-check.json)。

## 解除的阻塞与下一小批

`CurrentChenInitialMean` 直接导入 `S1BetaFixedNormalizedLower`，后者直接导入本模块。
本批解除该供应者的 **实际有限 S1 载体、筛和／主和及标准素数 AP 余项识别** 这一导入阻塞。
这不提供后续 beta 渐近误差支付、密度下界或主尺度估计。

根据固定源码的真实 imports，下一最小切片是：

```text
MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser
source SHA256: c07c0704c975bef4d772090ce03d7536f28edd319c700c4d9feb27c9f111ef62
sole import: MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier
```

该节点的唯一导入已由本批验收，适合下一批验证其精确 Rosser 主项减 AP 前缀误差的有限下界。
`S1MainMass` 的唯一导入为既有 `BombieriVinogradov`，是之后另一个小候选。
`S1BetaPaidLower` 另需 `S1BetaGeometry`、`S1LowerRosser`、`S1MainMass` 和
`MathlibNt.AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418Unconditional`；
不能在本批完成后直接假定其额外闭包齐备。
后续再依依赖顺序推进 `S1BetaLowerDensity`、`S1BetaMainScale`，最终才验收
`S1BetaFixedNormalizedLower` 和 `CurrentChenInitialMean`。
本批没有启动这些节点，原 319 项队列也没有展开。
完整的有限来源图与源码哈希见 [context.json](../verification/parts/p5/round3/s1carrier/context.json)。

## 历史中断及接收边界

原记录中的 S1Carrier 尝试仍按 `INTERRUPTED_FOR_PRIORITY` 保存：工具退出码 130，
没有 frontend 最终返回码或成功对象。该原始记录不是证明失败，也不被本次新成功回执改写。
本次从完全相同的源码恢复，正常完成三项验证；没有依赖版本更换或源码补丁。

**接收 Part：P5 首项均值供应链与 P0 集成验证。** 其他 Part 可按本回执哈希复用这一有限模块，
无需等待完整 InitialMean。

`CurrentChenInitialMean` 的 `(33/4) * Real.log 3` 仍是独立第一项候选下界，尚未编译验收；
它不等于手稿采用的 L1，也不闭合完整十一项均值或 `hLower`。
其源文件 SHA256 保持 `5358e4dbbda436b335620de19884624df3260386d5ab5e478a85f70599da6137`。
本批不改变 `W_N ≤ 4 D12(N) + error` 的计数尺度，完整均值仍需权尺度
`4c = 49044063/6250000 = 7.84705008`，其 P1/P2/P3/P4-A 输入依旧另行闭合。
