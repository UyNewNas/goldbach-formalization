# P2 最终陈述、真实依赖与稿内闭合路线审计

日期：2026-11-24。审计者：`/root/p2_ledger`。

本报告只读核对既有源码、看板、1106 手稿和已保存验收记录；未运行 Lean、未提交云任务、未改证明或看板。它不增加任何声明的编译或内核信用。已有源码中的 `SOURCE ONLY` 注释可能保留旧状态；是否已有信用以同源、同对象、同依赖的实际收据为准，不能只靠注释判定。

## 1. 首要结论

**Winner9 有限族是 P2 上界证书的一部分；完成它不会直接完成 P2。当前 17,572 行终端仍需要真实 `BankEndpointLicences`。但“对全部移动 Wu 盒统一的 seed”不是 1106 手稿唯一要求的命题：它是现有原生 H/h 接口带来的供应要求。**

当前存在三层必须分开报告的目标：

1. Winner9 的完整原积分下界：一个具体 Full87 cell 的积分，包含原 log floor 与第 21、22 个增量，不能当作全部 22 项的上界密度。
2. P2.9 的完整 ordinary-plus-defect 积分下界：17,572 个已存行数值需要真实 h-bank 许可，不能只证整数和或删去实际 Wu-h 缺陷项。
3. P2 的稿内总目标：四个上界项、22 个 saving、下界十一项及采用的改进项都绑定真实解析/算术对象，同一策略的两项 reserve 分别支付，最终进入实际密度与实际 Chen 计数。有限数字总账与条件装配接口不是这层结论。

**固定有限标记族路线已有大量源码，不能重做；目前也不能只宣布“令 P3 成立”就结束。** 真正剩余的是命名的 `ordinaryAP`、`switchedPPBalance`、前代反馈、各动作 `debt` 的实际支付，以及从历史数值表到原增强族实际计数的语义桥。该路线的一批最接近终端的源码仅覆盖 `Root.U3 | Root.U4`，不能据此覆盖其他原根。

## 2. 本次读到的版本与证据边界

- 本地工程：`/workspace/scratch/89135e928d3c/goldbach-p2`；本次快照 HEAD 为 `0f87651d2f27a6de1900b717b8703f2c6cbcb0ae`。文件 SHA 见末节，审计针对实际读取字节。
- 本地看板：`/workspace/scratch/89135e928d3c/goldbach-board/data/board.json`，`asOf=2026-11-23`，`baselineCommit=7f5330cace31383f5626da526b476dd4b0f43376`。它没有自动包含 11 月 24 日全部私有验收。
- 手稿：`UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `paper/release-20261106/en/`。本地为 `/workspace/scratch/89135e928d3c/chen-paper/` 下相同路径。
- P3/外部复用沿用已保存的 `docs/source-only/20261124-p2-wu-uniform/UPSTREAM_REUSE_REVIEW.json`，本次没有重新发起上游发现搜索。
- 私有有限证据沿用本目录 `slim-repository-verification.json` 与 `evidence-checkpoint-20261124.slim.tar.xz`。126 模块、5,447 个 owned 声明是该检查点的数目；本报告不把运行中的后续任务算入。

看板的 P2 根标题为“数值证书与真实解析积分绑定”；P2.9 明写“计算层已闭合，解析许可仍待供给”。其 “Final” 是描述标签，当前已核对的 board evidence 没有给出一个叫 `Final` 的 Lean 声明。本报告用下列确切符号确定依赖，不把描述标签当作一个已经验收的无条件定理。

## 3. 实际终端陈述

### 3.1 Winner9：原 Full87 cell 的真实积分

文件：`docs/source-only/20261124-p2-winner9/ImbalancedChen/P2Winner9CompleteSeedTerminal.lean`。

命名空间：`ImbalancedChen.P2Winner9CompleteSeedTerminal`。

最终候选声明为：

```lean
theorem complete_seed_ledger_le_original_full87_nine11 :
  (adoptedLogTotal : ℝ) + (savingLower slot21 : ℝ) +
    (savingLower slot22 : ℝ) ≤
  P4AOriginalFull87SourcePrimeTests.cellIntegral (.remaining (.nine 11))
```

它经 `complete_seed_ledger_le_terminal41` 和
`P2Winner9OriginalFull87Bridge.terminal41_integral_eq_original` 到达**原全限定** `cellIntegral`；不是新建的同名替身。

直接供应链为：

- `P2Winner9LedgerBridge.selected_real_sum_eq`：原选中 floor 的总账恒等式。
- `P2Winner9CompleteNumericalChecks.selected_checked`：全部原选中行的实际有限检查。
- `P2Winner9CompletePullingGeometry.complete_seed_actual_overlap_null`：完整族的实际重叠为零。
- `P2Winner9ArchiveIntegral.checked_family_floor`：检查到真实积分的不等式。
- `P2Winner9OriginalFull87Bridge.terminal41_integral_eq_original`：真实原对象身份。

这一陈述没有 PP、H247 或 Wu 移动 seed 前提。它仍需要全部数值行和整闭包的验收。该处“seed”指八维积分区域的采用 floor，和 `sv:finite-seed` 的真实计数改进不是同一个对象。

`P2OriginalSeedChronologicalMaxArithmetic.lean` 保留：

```text
adoptedLogTotal    = 475182339168330434688559 / 2^96
mixedSelectedTotal= 475741072397709744401965 / 2^96
mixedSelectedTotal - adoptedLogTotal = savingLower slot21 + savingLower slot22
```

手稿对应 `numerical-appendix.tex` 的 `num:upper-table`：第 21、22 行只是对前一个 floor 的增量；第 277–284 行要求比较 own bound 与完整 child sum、跨 rank 望远镜求和。不能把完整 mixed floor 再与已计入的原 floor 相加。

本检查点已有完整 93 几何模块与 11 原定义核心；数值页 `0000–0015` 及 block 00 覆盖 256/11,026 行。还有 10,770 行未被该检查点覆盖。完整 terminal 的源码存在不等于它已通过整族验收。原四个 owner 的定义拆分还必须联合安装并验证 native 边界；“独立 definition core 可编译”不等于原 owner 全闭包已验证。

### 3.2 P2.9：17,572 行 ordinary-plus-actual-Wu-h 积分

文件：`ImbalancedChen/P2HistoricalSavedFloorFullBinder.lean`。

确切终端为：

```lean
theorem checked_full_saved_total_actual_lower {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hbank : P2HistoricSavedOrdinaryDefectAssembly.BankEndpointLicences δ)
    (hc : ∀ r : Row, fullSourceRowCheck r = true)
    (hsum : storedTotalCheck = true) :
    decodeQ80 sourceSavedFloorTotal ≤ fullCompleteActualIntegral δ
```

此处：

```lean
rowCompleteActualIntegral δ r =
  rowActualOrdinaryIntegral r +
  guardedDefectIntegral δ (rowTL r) (rowTR r) (rowUL r) (rowUR r)
fullCompleteActualIntegral δ = ∑ r : Row, rowCompleteActualIntegral δ r
```

`checked_full_saved_total_quarter_units` 只再把两边各除以 4 一次。`actualSf` 已指定为原 `sf 16384 8`，`actualLog` 指向原 log interpreter；不是让调用者提供任意数值函数的正确性。看板历史绿色可复用的是相应实际 source checks、保存整数总和、Q80 与一次 `/4` 等计算层；更换 source graph 时仍须沿原收据核对身份。

**这里不能消掉 `hbank` 后仍使用同一结论，也不能删除 `guardedDefectIntegral` 来制造一个较易终端。** 此积分下界还需要与手稿指定的增强 marked-count 实例及最终下界计数连接；文件本身不是整个 Chen 下界。

### 3.3 `hbank` 到 H247 的精确路径

`ImbalancedChen/P2HistoricSavedOrdinaryDefectAssembly.lean` 定义：

```lean
def bankCellRight (k : ℤ) : ℚ := 1 + ((k : ℚ) + 1) / 50
def BankEndpointLicences (δ : ℝ) : Prop :=
  ∀ k : ℤ, 0 ≤ k → k ≤ 199 → 2 ≤ (bankCellRight k : ℝ) →
    decodeQ80 (bankLowerTable k) ≤
      P2TableActionSourceOnly.h δ (bankCellRight k : ℝ)
```

而 `ImbalancedChen/P2TableActionSoundness.lean` 中：

```lean
def H (δ s : ℝ) : ℝ := wuImprovementLimit true δ s
def h (δ s : ℝ) : ℝ := wuImprovementLimit false δ s
```

它们是原生 Wu 源函数，绝不是通过 recurrence 定义的数组。

现有桥的顺序如下：

| 桥 | 源码位置 | 实际提供什么 |
|---|---|---|
| `historical_248_lower_from_H247` | `docs/source-only/20261102-resume-30j/bank_endpoint/P2HistoricalLowerBankAncestry.lean` | 给定第 247 代真实 H 端点，由原最后一代 lower suffix 得到第 248 代 h 下界 |
| `designated_h248_eq_last_H247_suffix`、`bankEndpointLicences_from_H247` | `docs/source-only/20261102-resume-30m/h248_historical_authentication/P2Historical248Authentication.lean` | 绑定原分阶段 schedule、原档和指定 h248；没有供给 H247 分析许可 |
| `actual_bank_from_low_upper` | `docs/source-only/20261112-resume/t08/bank-next/P2HistoricalScheduledPointReads.lean` | 把所需 H247 上端输入缩至 low sector |
| `original_bank_from_edges` | `docs/source-only/20261112-resume/t08/bank-next/successor-low-frontier/P2HistoricalLowTargetEdges.lean` | 再缩为 29 个实际 H 比较 |

最后一个输入的原型完全明确：

```lean
he : ∀ i : Fin 200, i.val ∈ edges →
  readGain 247 i ≤ H δ (tableGrid (i.val + 1))
```

`edges` 是：

```text
[50,51,52,53,54,55,56,57,59,61,63,64,65,67,69,
 71,73,74,75,77,79,81,83,84,85,87,89,94,99]
```

原 bank 复用审计记载这些实际比较仍为 0/29；本次没有发现或新增供应它们的证据。这个“29”与看板黄色节点总数无关。`P2HBankSourceFloor50.lean`、`P2HBankEndpoint50Facts.lean` 还明确区分较弱的真 lower floor 与 copied bank 第 50 项：弱正种子不够许可采用表，不能偷偷换用较小表。

原档身份另有一处独立阻塞：`docs/source-only/20261123-yellow-node-owners/Y10_ARCHIVED_BANK_EVIDENCE.json` 已核对 7/8 原 JSON，指定 `certify_combined_finite_table.json` 字节仍缺。该文件在 authentication source closure 中有实际用途。它是归档/来源绑定问题，不是一个可以用新算一次整数来代替的解析证明。

### 3.4 P2 的总账接收器仍是有条件接口

`ImbalancedChen/P2OriginalCertificateBudgetAssembly.lean` 中：

- `P2OriginalCertificateBudget.endpoint_sum` 证明四个 quoted upper 减 22 个 quoted lower 的精确有理恒等式。
- `component_error_and_both_reserves_lt_currentK` 还需要 26 个实际有向误差界与误差总和 `< upperSlack`。
- `compiled_density_of_component_errors` 还明确需要 `hraw`（该真实 raw coefficient 的密度）和 `hcompiler`（同一 coefficient 的编译误差），以及 small/rough 支撑和 β 范数。
- `lower_error_and_both_reserves_gt_currentC` 还需要真实 lower estimator 与采用 lowerRaw 的比较；它没有证明实际 Chen 计数下界。

其常数为 `currentK=8452171/1250000`、`currentC=49044063/25000000`。手稿 `num:upper-table` 后的总账与 `eq:current-E`、`eq:current-u` 对应上界；下界 paired-fibre 增量和两个 reserve 的归属在 numerical appendix 末节，不能挪用。

已有 `P4AAll22OriginalKLedger`、`P4AAll22AdditionalActualSuppliers` 与 `P4AActualFirstIntegralSelectedK` 分别接了若干真实积分。它们的陈述明确保留其他 quoted slots，不能把“两项/三项 supplier 总账”写成全部实际密度。旧 `CurrentUpperEighteenBudget` 也不能代替原 22 项。

## 4. 1106 手稿真正要求的量词

以下行号均指固定手稿版本的 `.tex` 源行；公式标签比 PDF 分页更稳定。

| 手稿位置 | 明确要求 | 对当前任务的含义 |
|---|---|---|
| `argument.tex` 97–114，`eq:current-PP` | 固定有限 smooth 几何族；原素数槽有固定正 cutoff；polylog mixed Euler 控制；同一 ρ 的有号余项与精确 coprime mean | P3 是真实同系数分布输入；不能用任意 weight、普通 BV 或不同 ρ 替代 |
| `argument.tex` 343–408，`prop:current-positive-product` | 固定族的正乘积计数；同一 ρ 同时具有正性、密度、分布；先 N 极限后几何精度极限 | 有限个固定族可以取共同常数/阈值；零质量片需绝对误差 |
| `sieve-appendix.tex` 878–938，`sv:seed-parameters`、`sv:finite-seed`、`sv:seed-base-certificate` | S=11/5、Kseed=681/100；增强支还须 L/S<χ；对每个**固定有限** admitted marked-family 集统一；先取得 J0=1/50 | 不需要先宣称全部移动 Wu BoxIndex 的最强统一定理 |
| 同文件 941–1027，`sv:seed-lower-child`、`sv:seed-feedback-integral`、`sv:seed-feedback-certificate` | 旧 J 先供给真正 lower child，再做下一轮；三个 singleton、四个 pair、无 D5− feedback；四轮严格 surplus | 精确四个小数或 λ 积分恒等式本身不是计数种子许可 |
| 同文件 1030–1101，roots/descendants 与 `sv:feedback-error` | 保留原 total Q、old squares、ceiling；深度至 440；有限正母盒精度先固定，随后 N→∞；正质量顶点 Θ/H_N 有正极限 | 固定有限 marked-query 路线在稿内。它仍须真正闭合几何准入与实际算术余项 |
| `numerical-appendix.tex` 302–374，`num:table-seed`、`num:action-map` | 真 seed 后才启动原 400-entry 表；70+36 动作均只读旧代；430 只用于 U3/U4，其他指定点用248 | 不可用一个任意 sound state 假设或430表冒充指定248 |
| 同文件 404–408、658–668、876–898 | 只在完全 admitted state 上使用完整 ordinary+h248；原 17,572 矩形、closed minima 与补项身份 | 原保存整数须连接到指定真实完整积分，再连接到原计数 |

### 4.1 为什么有限族不能直接证明当前原生 H/h 输入

`P2TableActionSoundness` 的自身说明明确：当前源族为固定 δ 的 `wuSourceBox`，它与增强 stable-prefix family 的识别尚未提供。`P2OriginalPositiveSeedLicense.actual_short_support_uniform_count` 的结论直接量化

```text
固定 k,δ,ε → 存在 T → 所有 N≥T、所有 i,Δ,V 满足 wuSourceBox → count bound。
```

这与手稿“先固定一个有限的标记族及精度，再取 N”并非同一输入类型。不能用有限 maximum 消除 `BoxIndex`，不能把 `wuImprovementLimit` 改为递归数组，也不能把原 `BankEndpointLicences` 偷换成只对选中 roots 的许可。

若坚持复用当前 native binder 原结论，必须供给它真正需要的原生 H247 比较，或者证明一个足以传递到该原生函数的真实语义桥。有限特定 marked families 本身不推出全原生函数下界。

若以手稿的实际最终计数为目标，可以沿已有有限 marked-family 路线证明指定历史数组对这些实际族有效，再把原数值证书、原积分和原计数完整接上。**这需要一个新的、明确的语义连接定理；当前尚未闭合，不能作为已存在的捷径。** 保持旧 native H/h 和旧 binder 原样，分别报告两种陈述及各自信用。

### 4.2 已经补齐的 moving-profile 工作怎么用

`docs/source-only/20261124-p2-wu-uniform/README.md` 记录了实际验收的 `P2WuJointWindowProfile`、`P2WuPrefixLogProfile`、`P2WuPrefixLogDerivativeBudget` 等五个轻量模块，共 88 个 owned 声明。它们给移动对数窗口 smooth majorant 和统一 mixed-derivative budget，是可复用的解析构件。

原生已有 `wu_boxTheta_lower`，固定 k,δ 下有 Θ ≥ cN/log(N)^(5k+2)；已有 collar/prefix Theta error payments。不可重做或声称原生 Θ 下界缺失。它们也没有自动给完整 sharp carrier、所有 Γ word 的同一 ρ 分布和 family admission。固定 k,δ 的正指数不能随意替成 1/90。

`P2WuPrefixLogTheta` 的较大依赖图仍缺原 `P5AllWordAmbientOccurrenceBound` 指定字节（已保存缺件审计）；不应为让图看似完整而重写一个不同证明。本次不重复缺件搜索。

## 5. 固定有限 marked-family 路线：现有工作与真正未供给输入

### 5.1 真实计数骨架已存在

下列是已有源码候选和准确作用，编译信用需沿各自原收据确认。

| 现有声明 | 源码目录/文件 | 可复用范围与边界 |
|---|---|---|
| `P2ActualMarkedCountState.iterate_actual_count_enclosure` | `docs/source-only/20261028-resume-30f/certificate_enhanced/P2ActualMarkedCountState.lean` | 从实际 Rosser polynomial 初态证明 marked count enclosure；不供给采用正 seed |
| `P2AllW1FrozenReceiverFiniteAction.all70_original_W1_marked_count_actions` | `docs/source-only/20261028-resume-30g/certificate_enhanced/` 下同名文件 | 70 个 W1 的真实 frozen receiver、same-Q 负项与原 quotient-mask 正项；正成本尚须付款 |
| `P2AllW2ImmutableCountRecursion.iterate_encloses` | `docs/source-only/20261102-resume-30i/w2_feedback/P2AllW2ImmutableCountRecursion.lean` | 任意 frozen E、同一 Q 的 70 W1+36 W2+Buchstab，旧代不变；从真实初态归纳，不要求 final count 假设 |
| `P2W2StablePrefixCountConsumer.pathState_actual_recursivePhi`、`recursivePhi_le_each_W2` | 同目录 `P2W2StablePrefixCountConsumer.lean` | 接独立定义的 stable-prefix 实际路径及其标记权重；不是所有十一根的完整 compiler |
| `P2CausalMarkedThetaSupply.finite_book_common_floor`、`source_Theta_exact` | `docs/source-only/20261102-resume-30r/actual_causal_marks/` 下同名文件 | 真实 finite mark book、共同正 cutoff、保留等乘积标签重数、Θ 字典 |
| `P2CausalBankOccurrenceBinding.W1_actual_occurrences`、`W2_actual_occurrences`、`actual_source_W1_profile`、`actual_source_W2_tuple_upper` | 同目录 `P2CausalBankOccurrenceBinding.lean` | 原两项 W1/九项 W2 occurrence、same-Q profile；仍保留 `countRemainder`、`W2Charge`，未识别 saved H/h |

不能因某个较早文件仅支持 `E=true` 就重写任意 E 递归：较新的 `P2AllW2ImmutableCountRecursion` 已有它。但正 pair 的 transport 使用真正 `complementCount`，不可把 complement 从不等式中删去。

### 5.2 最接近有限 seed 的现成终点仍有明确债项

目录：

```text
docs/source-only/20261110-yellow-closure-10t/
  t07_h34_actual_counts/successor_base_seed/
```

这里已有独立数值 helper `P2SeedOmegaOriginalNumerical.actualJ2omega_gt_safe_base` 与 `P2SeedFeedbackOriginalNumerical.actual_lambda_gt_thirteen_hundredths`。因此 `P2EnhancedSeedActualFeedbackAssembly` 的旧注释“λ 尚开”不应被当作最新研究结论；应复用后续数值源码/证据，不再从头证明 λ。

`Part5OriginalH430SeedFourMarkedRounds.seven_actual_on_marks` 接实际七个 physical window 的反馈质量；`previous_round`、`fourth_surplus` 给四轮算术。但 `four_physical_round_count_debts` 的右侧仍显式保留真实计数债项。

最明确的后续终点在子目录 `seed_pair_closure/Part5OriginalH430SeedSameCarrierPP.lean`：

```lean
def switchedPPBalance (B : Finset (LevelIndex ...)) : ℝ :=
  ∑ l ∈ B, levelMark l *
    (switchedFibre true N Q (wordProduct l) -
      (K / 4) * thetaConversion N (wordProduct l) *
        switchedFibre false N Q (wordProduct l))
```

`actual_seed_and_four_rounds_at_common_prime_restriction` 保留真实 seedPositions S、真实 C=Σ levelMark·trueAt、真实 Θ，并得到原型：

```text
5·(C − (1−1/50)Θ) + credit + pairCredit
  ≤ ordinaryAP S + switchedPPBalance S + εΘ

5·(C − (1−J_(j+1))Θ) + credit + pairCredit
  ≤ ordinaryAP S + switchedPPBalance S
      + 5 J_j·Σ(levelMark·physicalFeedback) + εΘ
```

`credit` 与 `pairCredit` 的非负性已保留。第二式不是“下一轮已证明”：必须使用前一轮的真实 upper/lower child bounds，支付/抵扣相应项，再做四轮归纳。单独把 `switchedPPBalance` 设为小量也不能跳过该步骤。

这些声明的 `Root` 来自 `Part5OriginalH430PhysicalRoots.lean`，明确定义只有 `U3 | U4`。它们的强 uniform 形式可用于固定有限子族，但不能不经新桥就给原17,572矩形或其他指定248根信用。

### 5.3 全 106 动作的剩余输入可以按名字定位

同目录 `Part5OriginalH430AllBankSignedCounts.lean`：

```lean
all_106_signed_count_bases
```

把真实选中位置的 `physicalDefect` 与舍入损失约束到实际 `debt` 总和加 εΘ。它没有把右侧证明为 o(Θ)。债项在：

- `Part5OriginalH430W1SignedOrdinaryBase.fixedDebt`、`lowerDebt`、`switchedDebt`。
- `Part5OriginalH430W2SignedOrdinaryBase.fixedDebt`、三个 `lowerDebt`、四个 `childDiscrepancy`、`switchedDebt`。
- `Part5OriginalH430W2SignedOrdinaryBase.positive` 仍保留原 rejected occurrence、higher switched、collision 和 restored-window bad-prime 项。

历史248数值已有专门复用，而不是把430表直接换进去：

```text
docs/source-only/20261123-yellow-node-owners/y10_bank_semantics/ImbalancedChen/
  P2HistoricalArchivedActionFeedback.lean
  P2HistoricalW1RealBase.lean
  P2HistoricalW2BaseRepricing.lean
```

`actual_w1_list`、`actual_w2_lists` 绑定共有权重/原列表；阶段-specific baselines 保持区别。W1 的 `historical_base_true_integral` 等已有源码；W2 的 `lower_K_base`、`variable_kernel_base`、`added_base` 仍显式要求 `h₀`（ordinary−priced mass 的原 base 许可）、`hm` 与 `hs`，这些不是 authentication 自动给出的分析输入。

### 5.4 两个真实 carrier 必须保留

`docs/source-only/20261123-yellow-node-owners/y09_w1w2_exceptions/ImbalancedChen/` 中现有：

- `Part5OriginalH430MaskedSievePlateau.counts_equal`、`member_window`：保留原 root roughness 的 receiver 在低于原 cutoff 的窗口上是平台；完整 receiver 的变化留在 outside receiver 中。
- `Part5OriginalH430ActualMaskedBankWindows.strict_single_carrier_empty`、`strict_pair_carrier_empty`、`selected_masked_switched_zero`：原 root-preserving receipt 上某些 fresh windows/word 确实为空。
- `Part5OriginalH430OriginalReceiptSwitches.owned_106_exact_net`：原 occupied fibre 上仍保留 `strictDebt + correction + (modelRow−parentModel) − switched` 的完整有号恒等式。

这些是**载体区分的已有工作**，并非手稿反例。它们禁止把“full receiver 的数值 H/h 收益”无条件套到原 root mask，也禁止因一侧 switched mass 为零就删除 outside/correction。下一桥须明确实际 receiver、增强 square/ceiling 和 full/outside 两侧的方向；任意 E 的计数恒等式不许可任意 E 的分布主项。

## 6. 同一 ρ 的 PP：真正外部输入与已有接收器

原型定义在 `ImbalancedChen/Part3DistributionTargets.lean`，并明确是未证明义务，不是公理：

```lean
def UniformPrimeProductTarget ... : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → Even N → ∀ i : ι,
      |primeProductSignedError k (cap N) N (Q N) (rho N) (W N i)| ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ A
```

当前 P2 原生 Ω3 接收器位于：

```text
docs/source-only/20261121-resume/manuscript-distribution-and-receivers/ImbalancedChen/
  P2NativeOmega3RankTupleReceiver.lean
  P2NativeOmega3SameRhoNormalization.lean
```

`uniform_indexed_signed_error_dictionary` 只证明真实 distribution error 等于按实际 rank 分解的上述 PP functional；`uniform_actual_rho_normalized_comparison` 仍留下：

1. 实际 attached coefficient 的 `physicalDensitySum ≤ K·singularSeries/log N`；
2. 相同 coefficient 下的 `p5z_labelledDistributionError`；
3. `p5z_labelledCoprimeCorrection` 与 `p5z_labelledSmallPrimeMass`。

已有 density 候选必须复用：

```text
docs/source-only/20261123-yellow-node-owners/y07_uniform_upper/ImbalancedChen/
  P4BOriginalFineAttachedUpper.lean
```

`exists_counting_selection` 和 `Selection.attached_K` 的源码已与远端蓝分支逐字匹配（已保存上游复用审计）；没有找到其完整 strict/kernel 收据，不能直接给绿色。自然适配为固定 `nu=1`、`v=19/96`、`cap=id`、同一个 Selection retention 与 beta，阈值取 max。不得另外选一个“密度好”的 ρ，再把 PP 的 ρ 当作同一个。

P3 已公开的 8 模块/176 声明补齐 proper-power/prime-minus-von-Mangoldt 等局部付款；`ExceptionalWeight*` 是 transport，不是 full-spectrum uniform supplier。已保存复用审计仍记载：实际 `hlambda`、两个 classical windows 的 full-uniform energy、无限谱截断控制、restricted medium 与 `UniformPrimeProductTarget` 整体未闭合。不能因 P3 局部通过就声称本节输入已供给。

固定有限 marked 路线可以把 P3 保留为**明确上游接口**进行下游形式化；这样得到的结论须标为“依赖 P3 的条件结论”。若报告“P2 全部无条件证明完成”，则这些实际输入必须已有可靠证明，或项目明确把它们归入其他节点且最终 theorem 诚实保留该接口，不能写成 `axiom`。

## 7. 最小可实施闭合顺序与停止条件

### 第一条：完成已授权的 Winner9 有限端点

1. 复用已验93几何、11核心、Ledger、row/selected checker及已完成页。只续跑未验数值页，保留 schema-bound cache。
2. 全11,026行及44blocks齐全后验证 complete aggregator、archive integral 与 complete terminal；保持完整原声明/类型审计。
3. 对四个原 owner 的 refactor 使用真正 native snapshot，联合检查同名冲突和原 Full87 imports；然后给具体 cell 的完整 floor 信用。
4. 把这个 floor 接回原 22项对应位置，其他槽逐一从已有对象/源码选择复用；不得将该步骤升格为整个 P2。

### 第二条：优先闭合稿内固定有限族语义

1. **先冻结一个最小、真实的原 finite mark book 和 receiver。** 直接采用现有 causal/history 定义，固定其 Q、prefix、weights、receiver、old-generation source 与实际积分。以 `SeedSameCarrierPP` 的原 `seedPositions` 为第一个目标，比重新从任意 Wu BoxIndex 建题更接近现有手稿链。
2. **给该实际族提供 admission 与同一 ρ 的条件接收。** 使用已有 `P4BOriginalFineAttachedUpper.Selection` 候选及现成正乘积/PP 字典，先证明所用 sharp/smooth source 确实是 P3 许可的实际几何族；只把 P3 保留为准确上游目标，不把完整 count 结论当输入。固定有限族允许有限 max 统一阈值，仍需正确的 signed mean、coprime、小素数、full-product/outer 付款。
3. **消去已有具名债项，而非再写一个同形接收器。** 首先支付 `ordinaryAP` 与 `switchedPPBalance`；随后利用前一轮真实子计数证明四轮，取得采用2327/100000的真实 seed。数值基项与 λ 已有候选，优先核验/复用，勿重做积分。
4. **按原 schedule 完成动作许可。** 支付 `AllBankSignedCounts.debt` 各项，保留 full/outside carrier 与有号纠正；把历史 W1/W2 的实际 base、原权重、closed-min、old-read 和舍入一致性接上。现有430/U3U4代码不能替代指定248其他根。
5. **建立真实最终计数桥。** 在不改原生 H/h 定义的前提下，要么真正证明其 H247 的29个所需比较从而解除当前 binder 的 `hbank`，要么针对稿内原增强族另证一个完整的“同一历史数字 → 同一实际积分 → 同一原始计数”定理，并如实保留旧 native binder 尚未解除。后一方案只有在 target 与全部原 occurrence 对应已经证明时才可计为稿内目标的完成。
6. **归并 P2 其他节点。** 看板仍给 P2.1/2/4/5/6/7 蓝色 scoped状态，P2.8绿色仅为总账等子范围；需复用并核实其指定producer、真实端点、同一策略与reserve付款后，才进入实际 currentK/currentC 的总装配。

在步骤2–5开始前，不建议为了当前 native 接口方便而扩大为“所有 k,δ、所有移动盒、任意完整 carrier”的新强命题。已有 moving-profile 成果保留复用；若选择继续原生路线，应先证明它确实缩短解除现有目标的路径，且不把接口强度误报为手稿必要条件。

### 缺口分类

| 项目 | 本次判断 | 不能作出的推断 |
|---|---|---|
| Winner9剩余页/整族汇总、原owner联合编译 | 有限证书与验证闭包工作 | 已有一页/六行 ⇒ 整族完成 |
| 原档缺件、source-only图对象身份 | 来源与工程绑定 | 新运行相同数字 ⇒ 原档恢复 |
| native H/h 与有限增强marked族的类型差别 | 形式化接口/对象识别问题；需实证桥 | 固定有限 max ⇒ 原生全移动统一 |
| prefix smooth与mixed导数、已知Theta/collar接口 | 可补齐省略推导已有阶段成果 | 这些helper ⇒ 实际完整PP供应 |
| four-round实际前代债项、全W2base、full/outside纠正及最终计数桥 | 稿内实质性**未完成证明义务** | 有recurrence恒等式 ⇒ 真seed或采用bank |
| 实际same-rho PP/full-spectrum medium供应 | 明确上游仍开；P3局部证明不够 | 普通BV、任意weight或不同ρ可替代 |
| 当前H24729条 | 现有binder确需的未供给输入；未找到通过记录 | 数值看起来正 ⇒ 真H函数比较成立 |

本次没有发现足以断言1106手稿错误的反例。已定位的是形式化对象/量词差别、现有数值许可桥中的实际未支付项，以及来源与验收边界。后续若某个原增强族的真实债项不能从稿内相应段落推出，应先在该命名输入处核对手稿并分类，不能通过缩小族、变换ρ、删去carrier或引入公理来“闭合”。

## 8. 固定字节清单

下表记录本次实际读取的核心入口。相对路径均相对上述 `goldbach-p2` 根；前三个路径的绝对前缀为 `/workspace/scratch/89135e928d3c/goldbach-p2/`。它们是定位记录，不是编译收据。

| 源码 | SHA256 |
|---|---|
| `ImbalancedChen/P2TableActionSoundness.lean` | `c4fa01de5f1c7348755ce35c3cf9877cd3d894a4d8d0afbe31232be3c66dc937` |
| `ImbalancedChen/P2HistoricalSavedFloorFullBinder.lean` | `dfd4e58b7a0d0baad4fc70ac1f7179ea8f1b031bc4f7f29186d8d9f1626b63be` |
| `docs/source-only/20261112-resume/t08/bank-next/successor-low-frontier/P2HistoricalLowTargetEdges.lean` | `22076697ef78850902c1af0c8860035bf68cbb7c879c6092b1cc8362e392bc9b` |
| `ImbalancedChen/P2HistoricSavedOrdinaryDefectAssembly.lean` | `b55a5da27e96cdd1ff0dbb9c9a6461f11759e2b028879d591888a32a75298675` |
| `docs/source-only/20261124-p2-winner9/ImbalancedChen/P2Winner9CompleteSeedTerminal.lean` | `cbe31372844d4b98426b9237756154b75c294520f53a9d1c69d816d74f77aca8` |
| `ImbalancedChen/P2OriginalCertificateBudgetAssembly.lean` | `927c1f586b80fe61e85bc6df4201d251b4e1e47eefea64b3baf98c0f69486b1a` |
| `ImbalancedChen/Part3DistributionTargets.lean` | `a0b43f877bb7bcdf7606e19281521a0165538c08c0495a2a3e2d58b66aeb08cc` |
| `docs/source-only/20261102-resume-30m/h248_historical_authentication/P2Historical248Authentication.lean` | `8df8e689073d67fbffe6aaf1393ce35fe011863e1c07b49f872aa4626e712a96` |
| `docs/source-only/20261102-resume-30i/w2_feedback/P2AllW2ImmutableCountRecursion.lean` | `0132d08cc8b0dbbb4836b6f97d8d2b084855765428f3d7f72ad75c5246e6c730` |
| `docs/source-only/20261102-resume-30i/w2_feedback/P2W2StablePrefixCountConsumer.lean` | `034e1a7533dbafa90a2aab67237943b2726d3f34a84bff31b0083593a71f6b1e` |
| `docs/source-only/20261102-resume-30r/actual_causal_marks/P2CausalBankOccurrenceBinding.lean` | `d9a7a59eee6581997e9527ea6c52f03509f16d9614cb3e58d2ce5a7dae8593f2` |
| `docs/source-only/20261102-resume-30r/actual_causal_marks/P2CausalMarkedThetaSupply.lean` | `2fd4f30baa9e7a04c29e116b5b803e61e91dd93297a23744b68e5a7ddac8f608` |
| `docs/source-only/20261102-resume-30m/h430_common_approximation/Part5OriginalH430PhysicalRoots.lean` | `560c588ed72d45ba8d8d2b28ba5b2b964fdc69a8acf27b066d835e702c4759be` |
| `docs/source-only/20261110-yellow-closure-10t/t07_h34_actual_counts/successor_base_seed/Part5OriginalH430SeedFourMarkedRounds.lean` | `89dcf2ed8f218e80503c73eea3ebb276ab63245f88ff3510ada966d4f584417d` |
| `docs/source-only/20261110-yellow-closure-10t/t07_h34_actual_counts/successor_base_seed/seed_pair_closure/Part5OriginalH430SeedSameCarrierPP.lean` | `689ea0aa4a88049843a7ef80ea1ec14c9256053ac614c15e41ee9abf14b3a4c7` |
| `docs/source-only/20261110-yellow-closure-10t/t07_h34_actual_counts/successor_base_seed/Part5OriginalH430AllBankSignedCounts.lean` | `cc536202edaa9ad9518904e281b2235e79e2c5aa361ae216e2602d8f8c34ed17` |
| `docs/source-only/20261110-yellow-closure-10t/t07_h34_actual_counts/successor_base_seed/Part5OriginalH430W2SignedOrdinaryBase.lean` | `dac6250a7ec8c163419b77c77c0ed251342263623b30d976c49e287c0b92a933` |
| `docs/source-only/20261123-yellow-node-owners/y10_bank_semantics/ImbalancedChen/P2HistoricalW2BaseRepricing.lean` | `10180f9ddc3a75af74ae152f1224356f05caa5930ebc759cdabfb2a2814890b6` |
| `docs/source-only/20261123-yellow-node-owners/y09_w1w2_exceptions/ImbalancedChen/Part5OriginalH430MaskedSievePlateau.lean` | `809c93d267bccfbeb3a9befee99c0ec5f53d67f0576189c129f3dec5a6e0b81a` |
| `docs/source-only/20261123-yellow-node-owners/y09_w1w2_exceptions/ImbalancedChen/Part5OriginalH430ActualMaskedBankWindows.lean` | `835efce72e5a9e5bc4ba7b07a7c23f39544b2c10d745795129d91e9cd039d922` |
| `docs/source-only/20261123-yellow-node-owners/y07_uniform_upper/ImbalancedChen/P4BOriginalFineAttachedUpper.lean` | `df408b9aa888b3f09dff72db76221faa004c33dba029a5c69e2e297b9f15dc61` |
| `docs/source-only/20261121-resume/manuscript-distribution-and-receivers/ImbalancedChen/P2NativeOmega3SameRhoNormalization.lean` | `6b17c6d6d7972facf7959de657e4358365bcf8c58c4d00dd3dd0c8760bc9c9dd` |
| `docs/source-only/20261121-resume/manuscript-distribution-and-receivers/ImbalancedChen/P2NativeOmega3RankTupleReceiver.lean` | `6ec68a0008464374fdc6e3810ea31d2216d095a291afa45aa1b575b1a544c6b3` |
| `docs/source-only/20261124-p2-wu-uniform/UPSTREAM_REUSE_REVIEW.json` | `35bc60dca5d93d390b57aade48b715b5a5f4528095022ccee5c81ff2c69464dc` |

手稿三份原源文件 SHA256：

| 文件 | SHA256 |
|---|---|
| `paper/release-20261106/en/argument.tex` | `87f5b5f2e25082e00b2b04d8ecc684630d64846912457dc0adade1a36fd67182` |
| `paper/release-20261106/en/sieve-appendix.tex` | `15c9f561b870edb43ec1de3a8adf88b0b4561982f0617b58b26b1de966f9f9d8` |
| `paper/release-20261106/en/numerical-appendix.tex` | `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232` |

本地看板 JSON SHA256：`4e461c8bd8dbe9bbbfa972912ef9adf74fea70e226a32f21d907da81d6975498`。
