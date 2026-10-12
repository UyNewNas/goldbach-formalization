# Part 0 第三批：P1 固定交付接收回执

## 接收结论

**可以直接分批接收 P1 固定证明提交 `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` 的四个生产模块。** 本次从固定 GitHub 树正式读取源码，恢复原始证据归档并逐项核对实际三门结果，复用已有验证，没有启动 Lean、leanchecker、Codex、CI，也没有向其他进程发送信号。

四个生产模块共 **140 个所属声明**；另有 `LevelCheckProbe` 的 10 个声明。生产者对四模块、probe 和审计执行模块共六个目标严格编译及原装重放，并审计五个数学定义模块的 **150 个声明**。不能把 150 全部计为新增生产声明。

纯证据核对于 **2026-10-12 12:02:15 UTC（北京时间 20:02:15）** 完成。本次正式接收范围不包括后来出现的两份未提交历史第五层 joint-cell 候选；它们已真实取得并另行冻结，见第五节。

主要交付：

- `P1_RECEIPT_REUSE.json`：六目标源码、对象、原始编译/重放和审计绑定。
- `P1_ACCEPT_FILES.json`：13 个 P1 所有文件的完整路径、Git blob、SHA256、来源提交；供 P0 取入自己的集成树。
- `verify_intake.py`：可直接运行的纯证据核对程序，不启动 Lean。
- `SOURCE_HEADERS_BOUND.md` / `.json`：四个生产模块全部 **52 条源码 theorem 声明头**与实际编译审计类型逐条对应。
- `KEY_TYPES_BOUND.json`：生产者 14 条关键完整源码类型与原始审计输出的精确对应。
- `FIRST_DIAGNOSTICS.json`：原始两次失败及最终修复身份。
- `FIFTH_CANDIDATE_SCOPE.json`、`LIVE_FIFTH_CANDIDATES.json`：原先报告候选的检索边界，以及实际取得的新候选源码。

## 1. 固定身份、保护范围与文件归属

| 项目 | 完整身份 |
| --- | --- |
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 原 P1 源码检查点 | `70ad4d737a2ff4a77413a5975af2fb41bdfb7d66` |
| 本次接收的 P1 证明提交 | `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` |
| P1 证明树 | `21c604997d43ec4e9e82aed4d0fc55919cb49f48` |
| 读取到的 P1 最新分支头 | `7f894bfb57b7aa561360e335c6d610b7c30614e0` |
| 冻结手稿 | `ba6ec11d800eccc54406490631895e174de85766` |
| 手稿主体 blob | `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` |
| 工具链 | `leanprover/lean4:v4.33.0-rc1` |
| Lean githash | `62eed1db4d67327ec8120be05f1a1b0847d74561` |

已经读取 README、`docs/CURRENT_MANUSCRIPT_MAP.md`、`docs/EXTERNAL_REUSE.md`、P1 固定 HANDOFF/VERIFICATION/KEY_THEOREM_TYPES，并检查祖先及固定树；没有适用的 `AGENTS.md`。`b09d` 相对共同基线保留全部 **303 个原文件 blob**，只增加 13 个 P1 所有文件。工具链、11 项依赖 pin、公共定义、主定理、量词、常数和公共根都没有被该证明提交修改。

`7f894b` 相对 `b09d` 只修改 `.github/workflows/lean.yml`：总任务 150 分钟、build 步骤 90 分钟。它不改变四模块或任何该批验证文件。P0 当前远端也已有对应 workflow 调整；接收 P1 证明时只取 P1 所有文件，公共 workflow 的现有状态由 P0 保留。

| 生产文件 | 完整源码 SHA256 | 归属与用途 |
| --- | --- | --- |
| `ImbalancedChen/OrdinaryLowerFourFrontier.lean` | `97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8` | P1；普通 lower rank-three 父树的实际第四候选和仿射区域字典 |
| `ImbalancedChen/ActualSelectedPrefixLowerCellSum.lean` | `48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714` | P1；整个有限选择修正的实际 cell 分解、外部精确抵消 |
| `ImbalancedChen/ActualSelectedPrefixLowerOwnCubeIntegral.lean` | `c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1` | P1；真实 Lebesgue 积分、实际素数和极限、selected lower density 极限 |
| `ImbalancedChen/HistoricalPrefixCertificate.lean` | `b6ef2c6febc61e28ddf5bbeb5c02fd665e5266833df4cd1b5b2640481cb6e6f3` | P1；共同网格、真实祖先 fallback、有限 cap 检查及 actual upper telescope |

另外九个文件均在 `verification/parts/p1/`：`EVIDENCE.tar.gz`、`HANDOFF.md`、`INTEGRATION.patch`、`KEY_THEOREM_TYPES.md`、`LevelCheckProbe.lean`、`Part1HistoryAudit.lean`、`VERIFICATION.json`、`VERIFICATION.md`、`check.sh`。完整逐文件身份在 `P1_ACCEPT_FILES.json`。其中根导入补丁由 P0 应用，本 intake 没有修改公共根或 P1 源分支。

本地初次读取时 Git 元数据尚不可见，11:59:06 UTC 已观察到恢复，`HEAD = 7f894b...` 且当时工作树干净。两个时点分别保留；没有把维护清理错误解释成用户删除或没有成果。

## 2. 实际三门及原始证据绑定

| 目标 | 严格编译，秒 | 原装重放，秒 | 所属声明 |
| --- | ---: | ---: | ---: |
| OrdinaryLowerFourFrontier | 退出 0，200.131 | 退出 0，68.232 | 27 |
| ActualSelectedPrefixLowerCellSum | 退出 0，214.859 | 退出 0，28.921 | 9 |
| ActualSelectedPrefixLowerOwnCubeIntegral | 退出 0，94.948 | 退出 0，48.552 | 8 |
| HistoricalPrefixCertificate | 退出 0，93.780 | 退出 0，47.087 | 96 |
| LevelCheckProbe | 退出 0，91.282 | 退出 0，38.900 | 10 |
| Part1HistoryAudit | 退出 0，427.006 | 退出 0，45.307 | 审计执行模块，不另计生产声明 |

原始执行使用未修改的官方 Lake → `Lean.Elab.runFrontend`，`trustLevel = 0`，六目标 `warningAsError = true`。原装 Lean CLI 的历史启动错误是 `error: failed to locate application`，因此没有冒称生产者执行了标准 `lake build`。缓存引导中曾使用的 metadata adapter 与生产/依赖源编译、六目标重放分开记录；后者明确没有该 adapter。驱动中的官方初始化调用不在生产证明树中。

六次原装 `leanchecker --verbose <精确模块>` 顺序执行，均 `LEAN_NUM_THREADS=1`。每份原始日志恰有对应目标的 `replaying` 行，总重放 277.015 秒；源码、目标对象及 sidecar 的前后哈希一致。默认 checker 重放所选模块定义的声明，包括 private 数据，不能声称它重新重放了所有导入依赖。

独立核对程序实际完成：

- 固定源码字节与 GitHub 完整树的 blob 和字节数一致；六份归档源码与固定源码一致。
- 归档 **2,196 个成员**全部为安全普通文件；2,195 个 manifest 条目全部逐文件校验，解压 payload **11,850,281 字节**。
- **689 条**本地 source-closure compile 记录及原始日志成功标记一致；**1,350 条**内部导入对象连接一致。记录中的 8,679 个官方缓存模块保持为缓存证据，没有重新描述为本轮编译。
- 六个目标的编译记录、原始命令、源码 before/after、生产对象、重放 before/after 与发布 `VERIFICATION.json` 一致。
- 审计用 defining-module 元数据枚举 private/generated/structure 等声明；150 条唯一声明、各模块计数、原始日志和传递公理完全对应。审计载入的五个数学模块对象正是各自已编译并重放的对象。
- 实际公理并集只有 `propext`、`Classical.choice`、`Quot.sound`。审计源在 `info.isUnsafe`、`info.isAxiom` 或额外公理时失败。
- 本次读取时六个当前对象均实际存在，SHA256 也与已发布回执完全一致。

归档 SHA256：`c56fc707d40ad255fd2d9c8b6c94dc7442c9c62b7238d833188b18cdf10f601d`。原始完整 receipt SHA256：`2a23599ce539e7768a938e729b9beb7516210ff49221f6a8fd8a0938107765a1`。全部实际命令、首次失败、旧源码和 final current 日志仍在归档中，没有另造成功 stdout。

### 类型展示的边界

P1 原审计使用默认 `Meta.ppExpr`，不是 `pp.all`。已提取所有 150 条原始 pretty 类型，其中 **7 条**含证明参数省略符 `⋯`。本 intake 没有删除省略符后冒称完整输出。

四模块全部 **52 条源码 theorem 声明头**已经与编译审计声明逐一匹配（含 1 条 private theorem），保存在 `SOURCE_HEADERS_BOUND.md/.json`；14 条生产者关键类型也逐字匹配原始源码和实际审计日志。其他 generated/structure 声明的默认 pretty 输出仍如实保存。P0 另行在新精确集成 SHA 的 CI 中导出完整 `pp.all`，那是补充类型证据，不代替此处三门回执。

## 3. 完整接口与数学边界

下面使用各源文件原有命名空间、open 和 notation；每个声明头均来自已绑定固定源码，完整的四模块接口见 `SOURCE_HEADERS_BOUND.md`。

### 普通 lower 第四层的真实积分入口

```lean
theorem tendsto_actualSelectedPrefixLowerDensity_ceil_normalized
    (I : Finset (Fin 4)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hbo : 2 * b ≤ old)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true) :
    Tendsto (fun N : ℕ =>
      actualSelectedPrefixLowerDensity N (Nat.ceil ((N : ℝ) ^ (b : ℝ)))
        I old nu a b m J * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 ((2 * Real.exp (-Real.eulerMascheroniConstant) / (b : ℝ)) *
        suzukiContinuousLowerFactor ((old : ℝ) / (b : ℝ)) +
        selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

这里 `b` 是固定有理对数盒端点，不是最终主定理的实数 imbalance 参数。几何数据先于目标 `N` 固定；ceil 枚举 cap 的覆盖由已有定理供应，没有把趋近结论交给调用方。

`selectedPrefixLowerRestorationIntegral_eq_integrals` 将真实积分写成：

```lean
theorem selectedPrefixLowerRestorationIntegral_eq_integrals
    (I : Finset (Fin 4)) (old nu a b : ℚ) (ha : 0 < a) (hab : a < b)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) :
    selectedPrefixLowerRestorationIntegral I old nu a b m J =
      ∑ j ∈ J, ∫ t in logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
          primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old),
        (primeOwnCubeGatedProfile (selectedPrefixCellCap I old nu a b m j : ℝ) t -
          primeOwnCubeGatedProfile (old : ℝ) t) * ∏ i, 1 / t i
```

父区域严格为 `t0 > t1 > t2 > t3` 且 `t0 + 3*t1 < old`。第四 own-cube 不预先过滤候选；新旧两个 own-cube 指示函数分别保留。实际素数 `p ∤ N`、严格 cutoff、反向存储历史、半开唯一归属、`∏ 1/(p-1)` 权及 `log N / singularSeries N` 归一化均未更换。外部 cell 的贡献精确抵消，不丢离散边界或素数尾项；进入连续零测结论前使用实际素数边界 sandwich/reserve。

这一族使用固定 `I`、`nu`。采用数据若需要逐 cell 不同 mask/ceiling，仍须给出准确泛化及不重计字典。它不是 P2 same-mask-v2 的 `K/80` 配对修正，也不提供整篇 Chen 均值或 c。

### 有限历史 cap 与实际 upper telescope

在 `ImbalancedChen.HistoricalPrefixCapData` 内：

```lean
theorem levelCheck_sound (D : HistoricalPrefixCapData) (h : D.levelCheck = true) :
    (∀ j ∈ D.cells3, D.old ≤ D.cap3 j) ∧
      (∀ j ∈ D.cells4, D.old4 j ≤ D.cap4 j) ∧
      (∀ j ∈ D.cells5, D.old5 j ≤ D.cap5 j)

theorem upperThirdToFifthSaving_eq (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    firstExitRetainedPolynomial (D.upperThirdPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z +
        actualHistoricalFifthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z

theorem upperFifthPolicy_eq_oddFirstExitPolicy (D : HistoricalPrefixCapData) (N : ℝ) :
    D.upperFifthPolicy N = oddFirstExitPolicy (fun pre => D.upperFifthPolicy N false pre)
```

第四旧 cap 来自有效第三祖先 cell，第五旧 cap 来自有效第四祖先 cell；每层外部都继承真实上一层，包括第三层 fallback。`levelCheck` 只检查三组有限有理比较，未放入 K、c、积分收益或期待的渐近上/下界。

`levelCheck_of_selectedBoxCapChecks` 的完整类型保留每 cell 的 `I3/I4/I5`、`nu3/nu4/nu5`、存储 cap 等于检查出的 midpoint cap 的证明，以及按该真实 inherited old 值执行的整盒检查。不能只检查某个 midpoint，却把另一个 cap 值交给积分。

这已供应实际有限 telescope 的 h34/h45，但没有供应采用数据表、全域覆盖、平方/envelope/因子分解许可、support exponent、boxed compiler、分布误差、实际 K 密度。上式 raw policy 也尚未等同于手稿的 boxed physical rho。

## 4. 原始失败与修复身份

原五根依赖图在 687/688 时失败，第一处真实 Lean 诊断为 `Part1HistoryAudit.lean:1:0` 缺少 `LevelCheckProbe.olean`。其 graph 和错误保存在 `closure-attempt-01`，没有当作审计通过。

随后第一份 probe 在 `LevelCheckProbe.lean:26:2` 报 `Tactic decide failed`，同版第 32、38 行也失败。原始错误恢复输出含 `sorryAx`，它们属于被拒绝的失败版本，未进入任何成功回执。最终只将三处 proof tactic 改为 `decide +kernel`，让同一有限 Rat 命题在内核转换中求值；不使用 `native_decide`。最终 probe 连同生成的辅助声明经过严格编译和原装重放。

`HistoricalPrefixCertificate` 从 `70ad` 的 `347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1` 改为本次 `b6ef2c6f...`：显式使用三个 `Finset.decidableDforallFinset`，确保只遍历采用有限 cell 集。33 个源码 theorem 声明头逐字未变，三组比较语义和字段未改。旧成功对象 `cacdacdc...` 与新成功对象 `d0a2da75...` 分开保留；旧编译成功没有覆盖新源码。修复是生产者 P1 在 b09d 已提交的内容，本 intake 没有编辑证明。

## 5. 第五层候选：实际取得的内容与未对应的旧身份

本次实际固定树范围是共同基线 `1a80...`、P1 已证 `b09d...`、P1 最新 `7f894b...`；逐字读取固定的 `ActualSelectedPrefixOwnCubeIntegral`、`FirstExitHistoricalLevels`、`ActualOrdinaryUpperFiveCubeIntegral` 并保留其相关源码类型。基线第一份是普通常层父树的第五积分，第二份是历史有限恒等式；都没有冒充另行报告的独立候选。以前 P1 对 3 个可见 PR、PR3 的 9 个评论和 30 条 commit title 的检查仅作历史记录复用，本次未声称重新搜索那些范围。

12:07:42 UTC 的本地实际检查发现并冻结两份**新的未提交真实源码**：

| 本地候选 | 固定 SHA | 本次冻结源码 SHA256 | 当前验证身份 |
| --- | --- | --- | --- |
| `HistoricalUpperFiveCellGeometry.lean` | 无，HEAD 7f894b 下未跟踪文件 | `0d54b930393ef01dbc9c44fbec5f356bf6be9a645a1a537064179fc12799424b` | 源码候选，未取得同源三门回执 |
| `ActualHistoricalFifthCellIntegral.lean` | 无，HEAD 7f894b 下未跟踪文件 | `dd9afad8cae4c977b8c6916e12ac38d0c4edeb5f7b1e0d42768958bae30f031a` | 源码候选，未取得同源三门回执 |

两份源码在快照读取前后哈希稳定，合计 24 条源码 theorem 声明头已保存；当时对应 `.olean` 不存在。它们给出第三层实际历史父树上的共同 cell：第一门仍读根 old，第三门读有效第三祖先，旧第五残差读有效第四祖先，新残差读第五 cap，并分别保留两个 own-cube 指示函数。

新候选确实包含以下实际 prime correction 的目标，而不是仅有文件名：

```lean
theorem tendsto_fifthPrimeCorrection_ceil (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) :
    Tendsto (fun N : ℕ =>
      D.fifthPrimeCorrection N (Nat.ceil ((N : ℝ) ^ (D.b : ℝ))))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral)
```

**上面是源码提取，尚无编译器确认。** 它仍未给出与 `actualHistoricalFifthSaving` 的整个 retained-density 身份、完整采用实例及全局 K 界。源码注释和同时取得的 P1 `UPSTREAM_INTAKE.md` 明确把这两份 joint-cell 续作，与以前用户报告的“独立全局第五积分、仅单模块编译”候选区分开。原报告候选的来源 SHA/补丁、实际文件与原始回执仍未对应；不能说“没有第五层成果”，也不能说“找到的两个文件就是那份已编译候选”。

此次本地范围是已恢复 P1 工作树的固定源与非 ignored 未跟踪 Lean 文件，没有穷尽其他会话、ignored 路径或不可访问成果。新候选源和上下文为发现用途，等待其固定交付后再正式接收。不会因这两份仍在推进而延迟 b09d 四模块的接收。

## 6. 接收顺序、CI 与未闭合输入

推荐取入 `P1_ACCEPT_FILES.json` 的 13 文件；公共根由 P0 增加四生产导入。依赖顺序为 `OrdinaryLowerFourFrontier → ActualSelectedPrefixLowerCellSum → ActualSelectedPrefixLowerOwnCubeIntegral`；`HistoricalPrefixCertificate` 可独立接收，probe 随后导入它，审计最后。

P1 已发布 `check.sh` 显式构建四生产模块、严格 elaboration 六目标、顺序原装重放六目标；它是正常 pinned stock CLI 可启动时的复现入口，本 intake 没有执行。P0 的新精确集成 SHA 仍须完成整根构建、根内核重放和项目规定的根公理检查，新增模块也须显式覆盖。

只读 CI 结果：b09d 的 Core run `38220815879` 为 cancelled、Variable-envelope 成功；最新 7f894b 的 Core run `38227749843` 为 success，任务 API 中全构建、根 checker、根 axioms 三个要求步骤均 success，Variable-envelope 也成功。本次没有下载该 CI 的 raw logs，因此只表述 API 实际状态。P1 未应用根导入，四新增叶不在原根传递闭包中，不能用这个绿色结果替代四目标验证，也不能套到 P0 的新集成 SHA。

| 接收方 | 现在可用 | 仍需真实提供 |
| --- | --- | --- |
| P2 / P5 | 普通 lower-fourth 的实际有权素数和—真实积分及密度 restoration | 采用的 cell/cap/mask 字典、真实积分数值证书；不得把 P2 配对修正计入同一 restoration |
| P2 | 共网格、祖先所有权、有效 old4/old5、有限 levelCheck 接口 | 采用表与每 cell 整盒许可、完整覆盖、不重计及源 row 绑定 |
| P3 / P4-A | 具体 raw upper policy/parity 和实际有限 telescope | boxed physical rho 的一致身份、support/factorization、分布与 compiler 误差，以及实际 K |
| P1 | 已取得的新历史第五 joint-cell 候选 | 固定并验证该批、整树 saving 身份、完整采用历史第五/第六/第八积分和截断误差；另报告的旧候选继续待对应 |
| P5 | lower-fourth 局部组件 | 全十一项采用均值、c 与 hLower；继续只等待 P4-A，不必等待 P4-B |
| P0 | 四个已证生产模块与完整回执 | 新整根精确 SHA 的最终门、完整类型补证，以及以后真正消除 hLower/hUpper 的最终入口 |

本次没有得到实际 K/c/hLower/hUpper 的新供应者，也没有新建包装隐藏它们。
