# Part 0 第二轮：分批验证回执

本轮接收 **11 个生产模块、393 个 defining-module 声明**。首批为 P5 Buchstab、P2 检查器与采用证书的实际首格五模块，以及 P0 的首格 Buchstab 桥；随后接收 P2 Coarse、P3 LongSlot，以及 P5 的实际有限十一项台账和因子四转换。每个组件均有严格编译、对应生产对象的原版内核重放，以及包括私有和生成声明在内的完整公理审计。

十一模块的固定证明接收提交为 **`278f949444748a30b5165ff47bfa283ab0bad0d8`**，tree 为 `9723353ffbda12028cdd9e64e36ccb3ac8fbd4b5`，位于独立集成分支 `chatgpt/chen-p0-integration` 的历史中。后续回执文档提交不改变该证明版本。当前提交的 CI 结果必须按其自己的完整 SHA 读取；组件接收和整根验证分别登记。

这不是完整 Chen 定理的验证完成声明。实际 K 密度、完整 c / Chen 均值、`hLower` 和 `hUpper` 仍须真实供应者；原有条件式最终桥保留原样。本轮没有把这些输入藏进新结构或类型类。

## 固定来源

| 来源 | 完整 SHA | 本轮使用范围 |
|---|---|---|
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` | `codex/variable-envelope-boxes`，不是初始化 master |
| P0 首轮文档 | `9fe1d6b8b68a97cad3a122410ad7fde1701eed35` | 没有改变共同证明基线 |
| 手稿 | `ba6ec11d800eccc54406490631895e174de85766` | 定义、量词、常数和证书版本不变 |
| P2 | `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` | 原始源码实际读取；本批最小修复见补丁 |
| P3 首轮 → 更新 | `64598da177adf861df3763d7c465ff941388b6d6` → `7d70a2545fd819706e473eb41e4d430ad19119d8` | 后者新增 rough auxiliary SW 两模块，并修正 PrimeAP 的一行证明；尚未整体核验 |
| P4 首轮 → 更新 | `262f69822a386a9d44efc059bceba11049668d68` → `c942b4c51d9d0005f0bd566906a3f0c88eeb1dba` | 更新仅为文档；生产源码仍是首轮版本 |
| P5 首轮 → 更新 | `3b8ab5eb2041af1906ecdb108f5edd2dd61f19aa` → `db97d0fe03250f4d9a8aea34b23e9c20f67010b8` → `bd83a110ee52626daf9e68535c007eb73a93daca` | Buchstab 字节保持相同；bd83 另含有限十一项 ledger、factor-four scale 及两个独立候选 |
| P1 固定分批交付 | `70ad4d737a2ff4a77413a5975af2fb41bdfb7d66` | 四个真实生产源码及五个交接/验证文件；基线 303 个 blob 未改 |
| P0 已发布 Buchstab 接收 | `30fdb230428e91d7eb5deb8deb5cbe3fdc113ceb` | 已固定的首个证明组件；后续接收提交继续保留相同源码 |
| P0 首格与桥接收 | `c9f407efe66240c08c2e8a678330ba7b98b74db5` | 五个 P2 模块和 P0 桥，共 184 个新增声明 |
| P0 LongSlot 固定候选 | `6d1e5c4710a66f68fd101d0b40b5514bbbba4919` | 发布时为未编译候选；后来同一源码通过三门，原候选回执保留其历史身份 |
| P0 Coarse 与 LongSlot 接收 | `5e31713690daba5ff926da61875a99171718fd1d` | 两个新增生产模块，共 106 个声明；保留前七模块原源码 |
| P0 有限 Chen 台账与 scale 接收 | `278f949444748a30b5165ff47bfa283ab0bad0d8` | 两个新增生产模块，共 98 个声明；固定源码复用生产者编译/重放，P0 补对象绑定审计 |

P1 的固定提交 `70ad4d737a2ff4a77413a5975af2fb41bdfb7d66` 已从 GitHub 正式读取，tree 为 `d287e728ca8d5825455728065ef60122dc6cf56a`，唯一父提交是共同基线。四个生产文件为 `ActualSelectedPrefixLowerCellSum.lean`、`ActualSelectedPrefixLowerOwnCubeIntegral.lean`、`HistoricalPrefixCertificate.lean`、`OrdinaryLowerFourFrontier.lean`；其字节与先前候选相同。最终台账的 05:48:47 UTC 只读快照为依赖闭包 596/688 完成；`HistoricalPrefixCertificate` 已出现同一固定源码的 strict/trustLevel0 编译成功（171.838 秒，对象 SHA256 `cacdacdcd4a5b55c4797d59dd41ef7b0c3cc926fddee16eeb309b1ebea17ad0b`），其生产重放和完整公理审计仍未确认。其余三个生产目标没有同源完成记录。四项均保持候选身份，没有把单门通过升级为三门接收，也没有启动重复闭包构建。另行口述的“继承前层选择的第五层积分仅过单模块编译”仍未找到对应真实源码，没有把上述四模块或有限历史关系冒充该候选，也没有纳入当前基线或本批接收。

## 已核验生产文件与接收方

以下 `.lean` 文件均在 `ImbalancedChen/` 下；表中计数为声明数，不是仅公共 theorem 数。

| 文件 | 声明数 | 严格编译 | 原版内核重放 | 公理审计 | 接收 Part |
|---|---:|---|---|---|---|
| `CurrentChenBuchstabRefinement.lean` | 5 | PASS，P0 | PASS，复用 P5 同对象回执 | PASS，P5 | P2、P5、P0 |
| `Certificates/RationalLogCertificate.lean` | 47 | PASS | PASS | PASS | P2、P5、P0 |
| `Certificates/PairedFibreIntegral.lean` | 13 | PASS | PASS | PASS | P2、P5、P0 |
| `Certificates/PairedCertificateChecker.lean` | 58 | PASS | PASS | PASS | P2、P5、P0 |
| `Certificates/PairedV2Data.lean` | 18 | PASS | PASS | PASS | P2、P5、P0 |
| `Certificates/PairedV2.lean` | 46 | PASS | PASS | PASS | P2、P5、P0 |
| `CurrentPairedBuchstabBridge.lean` | 2 | PASS | PASS | PASS | P2、P5、P0 |
| `Certificates/AboveMuSecondCoarse.lean` | 71 | PASS | PASS | PASS | P1、P2、P4-A、P4-B、P0 |
| `Part3LongSlotDistribution.lean` | 35 | PASS | PASS | PASS | P3、P4-B、P5、P0 |
| `CurrentChenMeanLedger.lean` | 93 | PASS，复用 P5 | PASS，复用 P5 | PASS，P0 新补同对象审计 | P3、P4-A、P5、P0 |
| `CurrentChenLowerScale.lean` | 5 | PASS，复用 P5 | PASS，复用 P5 | PASS，P0 新补同对象审计 | P3、P4-A、P5、P0 |

严格编译使用 `warningAsError=true`、官方 frontend `trustLevel=0`。每个生产对象的重放与源码绑定；新回执还记录直接导入对象前后哈希。审计允许的传递公理仅为 `propext`、`Classical.choice`、`Quot.sound`，并拒绝 owned unsafe 或 axiom 声明。

完整、未截断的编译器类型与三门回执在：

- `verification/parts/p5/round2/buchstab/`：5 个声明与 P5 的同对象复用记录。
- `verification/parts/p0/round2/buchstab/`：P0 最初诊断、修复与接收。
- `verification/parts/p0/round2/p2-first/`：182 个声明、五模块三门、所有真实失败诊断、修复和再生成检查。
- `verification/parts/p0/round2/paired-buchstab/`：2 个桥声明与独立三门。
- `verification/parts/p0/round2/p2-coarse/`：71 个声明、采用的真实双图积分下界、原诊断和最小证明修复。
- `verification/parts/p0/round2/p3-long-slot/`：35 个声明、固定候选的三门完成回执和原诊断。
- `verification/parts/p0/round2/p5-finite/`：98 个声明、两个固定生产源、生产者原始编译/重放与新的同对象完整审计。
- `verification/parts/p0/round2/ledger-final/`：28 模块的源码版本—验证—未闭合输入台账；源码提取的 267 个定理头与实际编译器确认的 393 个声明类型分别列出。全部原始 JSON、源副本和日志按字节收在完整归档，可按 `PACKAGE_README.md` 校验还原。
- `verification/parts/p0/round2/context/`：固定来源、运行环境、P1/P3/P4 后续交接审查及历史 Actions 状态；这些上下文记录不是额外成功门。

## 关键编译器确认类型

下列以常规 Lean 记法转写完整实际类型；`compiler-types.json` 保存 `pp.all` 的原始输出，包括显式实例与宇宙参数，不以源码提取冒充编译器输出。

```lean
theorem ImbalancedChen.currentChen_buchstab_eleven_twentieths
    {s : ℝ} (hs : 7 / 3 ≤ s) :
    11 / 20 ≤ LiLiuPrereqBuchstab.buchstab s

theorem ImbalancedChen.Certificates.PairedIntegralCertificate.check_sound
    (c : ImbalancedChen.Certificates.PairedIntegralCertificate)
    (hc : c.check = true) :
    (c.lower : ℝ) ≤
      ImbalancedChen.Certificates.pairedLocalIntegral
        c.K c.a c.tl c.tr c.ul c.ur c.Z ∧
    ImbalancedChen.Certificates.pairedLocalIntegral
        c.K c.a c.tl c.tr c.ul c.ur c.Z ≤ (c.upper : ℝ)

theorem ImbalancedChen.Certificates.PairedV2.first_certificate_checked :
    ImbalancedChen.Certificates.PairedV2.firstCertificate.check = true

theorem ImbalancedChen.Certificates.PairedV2.firstIntegral_bounds :
    (31703 / 1000000000000 : ℝ) ≤
      ImbalancedChen.Certificates.PairedV2.firstIntegral ∧
    ImbalancedChen.Certificates.PairedV2.firstIntegral ≤
      (31704 / 1000000000000 : ℝ)

theorem ImbalancedChen.Certificates.PairedV2.first_fibre_buchstab_gain
    {t u z w : ℝ}
    (hs : ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w) :
    (1 : ℝ) / 20 ≤
      LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z) - (1 : ℝ) / 2

theorem ImbalancedChen.Certificates.AboveMuSecondCoarse.adopted_coarse_lower :
    (640339 / 15210735000 : ℝ) ≤
      ImbalancedChen.Certificates.AboveMuSecondCoarse.totalChartIntegral

theorem ImbalancedChen.part3LongSlotRemainder_abs_le_two
    (L U q a m : ℕ) (hq : 0 < q) (ha : a.Coprime q) :
    |ImbalancedChen.part3LongSlotRemainder L U q a m| ≤ 2

theorem ImbalancedChen.part3LongSlotSignedError_norm_le_box
    (M D L U a : ℕ) (α ρ : ℕ → ℂ)
    (hα : ∀ m ∈ Finset.Icc 1 M, ‖α m‖ ≤ 1)
    (hρ : ∀ q ∈ (Finset.Icc 1 D).filter (fun q => a.Coprime q), ‖ρ q‖ ≤ 1) :
    ‖ImbalancedChen.part3LongSlotSignedError (Finset.Icc 1 M)
      ((Finset.Icc 1 D).filter (fun q => a.Coprime q)) α ρ L U a‖ ≤
      2 * (M : ℝ) * (D : ℝ)
```

首格是 same-mask-v2 的 row 0：E0、t-index 422、u-index 510。其真实积分为

\[
\frac{8452171/1250000}{80}
\int_{937361/4096000}^{1875373/8192000}
\int_{194217/1280000}^{388777/2560000}
\int_{417/5000}^{76088109/532480000}
\int_{417/5000}^{z}\frac{dw\,dz\,du\,dt}{tuz^2w}.
\]

这是独立的较弱有理包围，不是原始 Q160 紧区间，也不是全 17,572 行积分证书。点态 Buchstab 桥只使用坐标支持和已证明的解析界，没有假设新的 K/c 结论；`K/80` 已含 `1/20 × K/4`，不能再次乘入同一增益。

冻结 JSON 的 SHA256 为 `f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7`。修复后的 importer 对完整 17,572 行进行了相同哈希、mask、解码检查，并以 `--check-generated` 与已编译的 `PairedV2Data.lean` 逐字匹配。改动仅为三处结构字面量的合法布局；所有有理数、行值和 mask 保留。

Coarse 采用固定手稿的 `above_mu_second_coarse_only` / `no_grid_coarse_lower`：负、正两图分别证明 `3/95000` 与 `32/3042147` 的真实积分下界，合计 `640339/15210735000`。密度因子 4 已包含在核中，没有 ordered-slot factorial；细网格证书估计的是同一节省量，不能与 coarse 下界相加。该模块的 `rho = 19/96` 是端点标量，不能冒充实际算术权函数。完整换元、覆盖和算术边界处理仍待供应；已有 pullback 恒等式只是逐点代数。

LongSlot 的任意复系数 `α`、`ρ` 位于短槽和模数上。实际证明尚未给长整数槽加上 rough/prime 限制或长槽相位；`2 M D` 的有限误差界还须接入正确的尺度与参数预算。它没有闭合 medium/two-long 分布，也没有提供实际权的 `realPhysicalDistributionError`。

P5 有限台账保留实际 prime carrier、自然数接收量 `N - P`、带标签 tuple 的重数、第 6 与第 11 项相同的 mask 补集，以及第 9 项随前两素数变化的 `sqrt (N / (p₁*p₂))` 截断。十一项系数仍为 `(3, 1, -1, -1, 1, 1, -2, -1, -1, -1, -1)`。第 1、2、5、6 项消费下界，其余消费上界；第 10、11 项可消费实际和的一个联合上界，不能由联合证书反推出各自端点。统一归一化下逐项 `delta` 的预算总成本是 `14 * delta`，最后两项的联合份额为 `2 * delta`。

以下完整类型由实际成功审计打印，并以常规 Lean 记法呈现；所有参数保持显式：

```lean
theorem ImbalancedChen.currentChenPairedPrimeSum_eq_upsilon
    (N : ℕ) (E : ℕ × ℕ → Prop) :
    currentChenPairedPrimeSum N E =
      3 * currentChenUpsilon1 N + currentChenUpsilon2 N -
      currentChenUpsilon3 N - currentChenUpsilon4 N +
      currentChenUpsilon5 N + currentChenUpsilon6 N E -
      2 * currentChenUpsilon7 N - currentChenUpsilon8 N -
      currentChenUpsilon9 N - currentChenUpsilon10 N - currentChenUpsilon11 N E

theorem ImbalancedChen.currentChen_lower_scale_of_finite_budgets
    {N : ℕ} (E : ℕ × ℕ → Prop) {epsilon etaMean etaCount : ℝ}
    (hbudget : etaMean + etaCount ≤ 4 * epsilon)
    (hweight : (4 * currentC - etaMean) * singularNormalization N ≤
      currentChenPairedPrimeSum N E)
    (hcount : currentChenPairedPrimeSum N E - etaCount * singularNormalization N ≤
      4 * (D12 N : ℝ)) :
    (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ)
```

`hweight` 与 `hcount` 在这里是有限预算桥的公开输入；该桥没有供应 adopted mask 的十一项渐近均值、真实 c/K 或最终 `hLower`。P5 原生产者审计的 103 个声明中有已接收 Buchstab 的 5 个，不能重复计入新组件；本批新增正是 98 个。

同一 `bd83...` 的两个 Initial 模块保持独立候选：固定 `CurrentChenInitialSource` 源 SHA256 为 `2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767`，有第 41:14 行 `unsolved goals` 的真实 strict 失败；固定 `CurrentChenInitialMean` 源 SHA256 为 `adad5c2c0a98b49fed4ef832726e2fa20881b4fd8e31a270f93c32902e13e6c5`，尚无匹配目标的完成记录。live 未提交修复的成功记录不覆盖这两份固定源。


## 真实诊断与修复边界

- Buchstab：保留首个 strict linter 诊断，将 `field_simp ... <;> ring` 分为顺序 tactic；未改定理。
- RationalLog：修正 strict sequence linter 和乘除表达式的规范形，使原实对数证明闭合。
- PairedFibreIntegral：修正导数 proof API、积分定理命名空间和 beta/ring 规范形；真实积分定义、界限和定理声明保留。
- PairedCertificateChecker：原分组 field 布局被 Lean 当成函数 binder，出现 `inferBinderTypeFailed upper`。改为每字段独立声明，保持原意的字段名、顺序和类型；另修两处加法次序证明。原版本尚不能 elaboration，未声称它已有可比较的编译后定义。
- PairedV2Data：首诊断为 42:54 `unexpected identifier; expected '}'`。仅修三处嵌套 record 布局，并同步生成器；原始数据逐值不变。
- PairedV2：原固定源码未修改即通过。
- Coarse：原第 299 行的积分 `rewrite` 模式不匹配；随后有不存在的 `intervalIntegral.integral_pow` 和冗余 tactic 聚焦。修复显式函数/测度、pinned Mathlib 引理名和严格 linter；28 个定理头及 16 个完整定义逐字不变。
- LongSlot：原第 177 行 strict linter 要求 `letI` 改为 `let`，第 189 行互素目标未解。补全互素等价的两个方向；12 个源码定理头和 6 个定义正文逐字不变。同一 `6d1e5c...` 源通过后没有再修改。

P0 修复只在自己的验证树及补丁中进行，没有更改其他 Part 的源分支。P5 有限两模块直接采用固定 `bd83...` 的字节；MeanLedger 相比 db97 的六处修复由供应者交付，其 34 个源码定理头和 16 个定义保持不变。

P5 补审计的首次真实诊断为 05:30:21 的对象导入失败：Lean 从部分填充的 P0 `ImbalancedChen` 对象目录寻找 MeanLedger，没有回退到 P5 缓存。P0 仅将本次显式选定的、已核实的只读生产者对象根放在查找路径首位，保留失败日志后补审计。49.685 秒的实际审计成功，外层锁等待及启动合计计入 155.311 秒；没有重复编译或重放两个生产模块。生产者旧回执缺少 replay-before 和 audit-import-before/after 字段，这些历史字段未被编造；精确固定记录、现有对象哈希及新的 P0 双端审计绑定分别保留。

## 未闭合输入与总体门槛

P1 须供应实际历史策略、许可/支持、采用实例及完整真实积分；P2 须完成全部实际数值证书；P3 的新的 finite rough-removal 推导仍保留同一家族 `k=1` small-modulus SW 输入，尚非实际全分布结论。P4-A 须证明同一实际 rho 的 K 密度，P4-B 须构造 hUpper，P5 须完成十一项真实均值、c 和 hLower。**P5 等待 P4-A，不必等待 P4-B。**

计数、实参数和归一化没有改变：先固定 `1/2 < b < 1`，使用 distinct additive prime count，ordered `r ≤ q` 并保留平方，不添 factor 2；计数/均值尺度为 `singularSeries N * N / log N ^ 2`，密度尺度为 `singularSeries N / log N`。

当前原装 `lean --version` 启动失败，原装 Lake/官方 Lean frontend API 和原装 `leanchecker` 的实际成功分别记录，未冒充原装 `lake build` 成功。完整公共根构建、公共根内核及全根传递公理审计尚未完成。两份旧最终入口源码、工具链和所有 dependency pins 与共同基线逐字不变。

本地明确阻塞是原装 Lean CLI 在进入证明前报 `error: failed to locate application`。成功的组件编译由原装 Lake 运行官方 `Lean.Elab.runFrontend`，`trustLevel=0` 且 `warningAsError=true`，未改 Lean 二进制、内核或依赖元数据。归档的 frontend driver 使用官方初始化器执行 API 恢复其正常生命周期；该运行器位于生产证明树之外，不是 Lean 数学声明中的 `unsafe` 或公理。源码与对象哈希、原始命令、环境和实际输出保留在回执中。

原最终桥 `current_theorem_1_1_of_manuscript_bounds` 的当前类型仍要求下列 `hLower` 和 `hUpper`。以下是**固定源码提取**，本轮没有用新编译器打印冒充它；其缺失依赖中有 P1 正在构建的同版本模块，未重复启动：

```lean
theorem ImbalancedChen.current_theorem_1_1_of_manuscript_bounds
    {b : ℝ} (hbLower : (1 : ℝ) / 2 < b) (hbUpper : b < 1)
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (RealB b N : ℝ) ≤
          (currentK * Real.log (1 / b) + epsilon) * singularNormalization N) :
    ((currentC - currentK * Real.log (1 / b) : ℝ) : EReal) ≤
      Filter.liminf
        (fun N : ℕ =>
          (((RealDb b N : ℝ) / singularNormalization N : ℝ) : EReal))
        evenNatAtTop
```

这里的 `currentK = 8452171/1250000`、`currentC = 49044063/25000000` 没有变化。真实 K 密度与完整 Chen 均值/c 未闭合，因此尚无可接收的、消除了两个解析假设的完整入口。

正常锁定工具链 checkout 的逐批入口为：

```bash
bash verification/parts/p0/check_batch.sh buchstab
bash verification/parts/p0/check_batch.sh p2-first
bash verification/parts/p0/check_batch.sh paired-buchstab
bash verification/parts/p0/check_batch.sh p2-coarse
bash verification/parts/p0/check_batch.sh p3-long-slot
bash verification/parts/p0/check_batch.sh p5-finite
```

每个入口显式构建新增目标，不借旧根 `lake build` 覆盖。它们不取代 `.github/workflows/lean.yml` 和 `verification/verify_variable_envelope_boxes.py` 规定的完整项目门槛。本环境没有把这些 shell 入口记为已端到端执行。

对 `30fdb230428e91d7eb5deb8deb5cbe3fdc113ceb` 的 Actions 读取显示两个工作流均无已分配 runner、执行步骤为空。未盲目重跑；它们不提供 Lean 成败证据，也不能覆盖后来 SHA。

后来 `c9f407efe66240c08c2e8a678330ba7b98b74db5` 已实际取得运行器：Variable envelope run `38205485520` 完成成功，实际日志确认其原定 358 声明审计和对应构建、回归与重放均通过。这是该工作流原定范围，不是本轮十一模块或完整根通过的替代证据。Core run `38205485501` 在 05:36:51 UTC 的实际终态为 `completed / cancelled`：完整构建最后完成到 `9643/9786`，根 `leanchecker` 与根公理审计均为 `skipped`，随后门槛结果检查失败。原始日志中没有真正 Lean `error:`；首个 CI error 是 `The operation was canceled.`。工作流固定 45 分钟时限已核实，取消时间与时限相符，但未取得超时 annotation，因此原因只记为推断。七个当时新增生产模块各有真实 CI `Built` 记录；这是额外的组件编译证据，不升级为完整根或 strict/内核/公理三门通过。

没有在该健康运行期间推进 integration 引用，也没有取消、盲目重跑或降低任何工作流门槛。最后证明提交 `278f949444748a30b5165ff47bfa283ab0bad0d8` 的 Actions 查询在 2026-10-12 05:44:17 UTC 尚为零条；本地完整根门没有运行成功。之后回执文档提交所触发的检查必须使用该文档提交自己的完整 SHA 单列记录，不能继承 C9 的部分成功或取消结论。终态日志与解释见 `verification/parts/p0/round2/closeout-context/c9f407-terminal-CI-receipt.md`。
