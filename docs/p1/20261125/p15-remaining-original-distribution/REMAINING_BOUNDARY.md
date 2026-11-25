# P1.5 原实际分布误差：剩余证明与复用边界

状态：只读源码／手稿审查；**不是 Lean、kernel 或完整 P1.5 验收**。本记录基于 P1 源码提交 `e1a80f6c306b58eadf2a8c6f58f4cbc7385e32d5` 的相关不变声明，以及下述定向读取的新 P3.4/P3.5 远端回执。没有重新搜索九份已登记缺失 owner，没有编译、云任务、Git fetch 或新数学假设。

当前完整 signed M 在实际物理族上的接入仍是直接阻塞。P3.4/P3.5 已有新验收增量，后续沿其原接口复用；P1 不重做这些谱核、有限 packet、test-jet 或 whole-height 证明。另一条可推进的稿内工作是 singleton 两长分支的活项几何、原 rough/strip 还原及有限预算装配。以下检查没有提供明确反例或证明推导矛盾，不能据源码／接口尚未闭合推断手稿存在实质数学缺口。

## 1. 固定手稿与审查范围

主手稿：`UyNewNas/chen-imbalanced-semiprimes`，提交 `a988cba584d803ae2856a0de50efb582f4f3dd6a`，`paper/release-20261106/en/`。

| 位置 | 本次使用的合同 |
|---|---|
| [argument.tex，`prop:current-medium`](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/argument.tex#L29) | 完整 signed M：四个尺度门槛、实际 residue、rough individual medium slot、辅助 SW、补系数 divisor order、三个 primitive 因子 |
| [coefficient-appendix.tex，252–271](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/coefficient-appendix.tex#L252) | 先固定物理族与裕量，后选 `zeta/kappa/kap0` 和最终阈值 |
| [同文件，491–641](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/coefficient-appendix.tex#L491) | 原 PP 的 trim、HB、完整乘积尺度、Fourier、medium 与剩余 Type I 组装 |
| [同文件，803–820](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/coefficient-appendix.tex#L803) | 一长／两长 rough 还原的各项误差；E4 不是全部误差 |
| [analytic-appendix.tex，951–1057](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/analytic-appendix.tex#L951) | 已登记 ABL、Kim–Sarnak、Pascadi 与 regular large-sieve 输入的实际归一化、谱测度和量词 |

`coefficient-appendix.tex` 的 Git blob 是 `10f3e2efb2074a9b97148a5151956e1d450be13f`，SHA-256 为 `267af54481f344e806d4cb3ad602aa7f32020b930845e2aa152b7daaa2f9a440`。`analytic-appendix.tex` 的 Git blob 是 `7cf3bbb16cd8924565eb439e474e0674f04631da`，SHA-256 为 `e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`。P3.4 新文档另引提交 `8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703`；对这两个提交精确读取同一 analytic 文件，返回的完整 Git blob 相同。

同时保留 [PROOF_SCOPE.md](../p15-actual-means/PROOF_SCOPE.md)、[历史调用说明](../../../source-only/20261125-p15-historical-onelong/README.md)、该目录 `SOURCE_BINDINGS.json` 及 [恢复索引](../p15-actual-means/history-source-recovery/SOURCE_INDEX.json) 的边界：23 个均值模块的验收不支付实际物理分布误差；历史 remainder 的写出不等于 remainder 已小。

## 2. 三项义务的精确分工

| 原义务 | 已有结果 | 尚需的具体连接 |
|---|---|---|
| original signed von Mangoldt discrepancy | `P1OriginalSingletonProperPower.eventually_original_singleton_prime_sub_vonMangoldt_logAccuracy` 支付原 prime error 与同源 VM error 的差；保持原 `Q/rho` 和精确 mean | 该比较不估计 VM error 本身。通过原 Atlas 的 medium、Type I、OneLong 和已单列修正项闭合主分布量；普通 BV 的 `panModulusCutoff` 结果不能直接支付其上的 remaining 区间 |
| `mediumAtlas` | 原 rectangles、Fourier、live-row、actual `MediumAdmissible` 与 auxiliary SW 源码；U06 的准确短 rank-3 子域 | 完整 signed M 的实际族 supplier，以及 dead/live 分支、全 Fourier tail、外层 chart/HB 标量和统一阈值。U06 只支付低首指数、`U ≤ x^(1/16)` 的指定 rank-3 项；不能提升为全 medium |
| `remainingTypeIAtlas` | 原精确分支定义、one-or-two-long 活项几何、任意 `Q/rho` 的两长有限字典、squarefree 内部 P2 源码 | 在原 singleton 支撑上导出恰两长和 long roles，再支付 rough restoration、个别端点 strip、短系数质量、模数矩、Fourier L1/tail 与完整外层预算 |

具体 medium 连接已有源码：

- `docs/source-only/20261120-resume/p1-singleton-medium-rectangles/ImbalancedChen/P1OriginalSingletonMediumRectangles.lean`：`source_to_actual_rectangles`，同一 `Q/rho` 的 literal rectangle identity。
- `docs/source-only/20261115-resume/p1-singleton-medium-window/ImbalancedChen/P1OriginalSingletonMediumWindow.lean`：`eventually_original_medium_window`，完整乘积 `x` 与实际 `N`、medium `U`、rough cutoff 的几何。
- `docs/source-only/20261123-resume/ten-task-continuation/selected-api/ImbalancedChen/P1OriginalSingletonMediumAdmissible.lean`：`eventually_original_admissible`、`eventually_original_with_auxiliary`，固定 `kap<1`、`0<zeta≤1/20000`、`0<kappa≤zeta/200000`、`kap0<kappa/(4*(1+kappa))`，连同原 `e/q/mesh/omega/ell` 条件。
- `docs/source-only/20261121-resume/manuscript-distribution-and-receivers/ImbalancedChen/P1OriginalSingletonMediumFourier.lean`：`original_eq_fourier`、`retained_mode_reconstruction`、`amplitude_l1_budget`；复原支付使用 L1，不能替换成频率盒基数。

这些路径中的 source-only 文件没有因本审查获得编译信用。完整 M 的四条 `MediumAdmissible` 不自动满足已有 shared-boundary 或 short-LCM 的更强专门条件；已有 U06 审查 [CONTRACT_REVIEW.md](../u06-reuse/CONTRACT_REVIEW.md) 应保持其原子域。

## 3. 两长分支可以直接复用的实际 API

### 3.1 同一 `Q/rho` 的有限字典

文件：`docs/source-only/20261121-resume/p4-two-long-actual-row/ImbalancedChen/P4BOriginalTwoLongActualDictionary.lean`，声明 `P4BOriginalTwoLongActualDictionary.same_rho_mode_eq_fibres`，原位置 25–80。

参数为 `bs : Fin r → Block`、`Z : ℝ`、`y xi : Fin r → ℝ`、`rs : Fin r → Role`、`i j : Fin r`、`i ≠ j`、`N : ℕ`、`S : Finset ℕ` 和任意 `rho : ℕ → ℂ`。它把

```lean
exactDiscrepancy (rectangle bs) S rho completeProduct N
  (fun n => hbSlots Z y rs n * occurrenceMode (scales bs) n xi)
```

精确改写为原 `shortSupport` 上同一 signed `shortSequence` 乘以 `∑ q ∈ S, rho q * roughFibreCore ...`。没有要求 `rho` 等于 P4 专用系数；可以令 singleton 的 `r=2*(j+1)≤6`。整数载体、顺序重数和精确 coprime mean 全保留。

下方 `actual_pair_mode` 是两个 P4 mother 经 `Fin.append` 的专门化，不能直接作为 P1 singleton terminal。文件 SHA-256：`0a8f213e63afc934afd1afa4aa8eaeeb850d5298201ec3db2a4232623ff69b33`。

### 3.2 原物理 squarefree 模数的内部 P2

文件：`docs/source-only/20261121-resume/p4-two-long-expanded-core/ImbalancedChen/P4BOriginalSquarefreeP2.lean`，声明 `P4BOriginalSquarefreeP2.mellinBrunCore_internalP2`，原位置 212–241。

前提完整保留：`Squarefree q`、`0<q`、`a.Coprime q`；`0<delta≤1/4`、`U,V>0`、`H≥0`、`|t₁|,|t₂|≤H`；`label : Fin 3`、两个 log flags、任意复 `alpha`、自然数 `m,d₁,d₂,a`、`d₁,d₂>0`。结论是

```lean
‖mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha m d₁ d₂ a q‖
  ≤ pairCost delta U V H * ‖alpha‖ * modulusBudget q
```

这份已有证明没有 `CompositeWeilInput` 前提。它先调用同文件 `naturalCore_P2_refined` / `naturalCore_P2`，保留原 `UV/q²`、双零轴、精确 coprime mean 和非primitive短积的零分支。其 `P4BOriginalSquarefreeWeil.squarefree_weil` 由已有 prime Weil 加 literal CRT 得到，包含 `q=1`、`p=2`；不推断变换模数 `c²*d` 也是 squarefree。

| 源文件 | SHA-256 |
|---|---|
| `P4BOriginalSquarefreeP2.lean` | `5ab54a8ebe7872b147a17615c9aa864104d2da578361d07676873d4a8628d876` |
| 同目录 `P4BOriginalSquarefreeWeil.lean` | `f94cf46ddd007696088098b86fabd77e43a3f69c8007babdb3fb897e0442e18f` |

这是已有 source-only API 的可实例化性判断，不宣称其完整导入闭包或对象已验收。

### 3.3 P1 仍须完成的有限连接

`remainingTypeIValue` 的定义只是剔除 one-long 的 Type I，不能直接读成“恰有两长”。已有 canonical `P5Z.ActualHBMediumRoleSupports.original_noMedium_actual_alternative` 要求实际 `blockCoefficient≠0`、`j∈range 3`、`firstMedium=none`、`64*originalLower^6<n<originalUpper^3`、`hbCutoff≤originalUpper` 和正性条件，才给出一长或两长及每条 long role 为 `.one` 或 `.logarithm`。应从原 profile 支撑、原 chart scale、固定正 `zeta` 和统一大 `N` 导出门槛，然后在 remaining 分支排除一长。

后续按稿内顺序使用上述字典、原 Brun rough restoration／各个 sharp interval 的 strip、P2、signed short mass 和模数矩，再恢复 Fourier L1/tail 与外层 chart/HB 标量。两长 E4 的典型指数门槛是 `40*zeta + 2*epsilon + 3*theta/2 < 1`；可先取 `.599/(1-kap0)<theta<.6`，再缩小固定参数。E1/E3、strip 和 tail 不能被 E4 的成功掩盖。

历史物理 `Q` 已有 squarefree、与 `N` 互素、单位系数界，适合直接在原物理 `Q` 上用该 API。free tensor 的产品模数不自动 squarefree；移到 free carrier 前必须另有相应理由。

## 4. 参数顺序、full PP 与两个历史调用

1106 的顺序允许：先冻结有限物理系数族、factorization 条件及正裕量；取 `zeta`、`sigma=zeta/2000`、beta support 与 mesh；知道固定 Fourier/moment 阶数后选

```text
0 < kappa ≤ min(kappa*, sigma/200, 1/(2*Kmom)),
0 < kap0 < kappa/(4*(1+kappa)).
```

还可令 `kap0<1/600`，从而 `.599/(1-kap0)<.6`，并保留各个低 rank 的半水平裕量。物理系数不依赖后来选的 smooth trim。因此历史定义中的 `kap0=kap` 可以取同一个足够小的正数；它不构成终局矛盾。

`P1Full87HistoricalOneLongRemainder.exists_original_count_remainders` 的 `∀ kap` 结论是“原 count − 原 mean − 显式 history remainder 很小”。最终只需对先固定实际有限族选择的足够小 `kap` 支付 remainder，不能把中间强量词误读成必须对所有 `kap` 证明完整 PP。

历史 `Q=remainingModuli B N (trueDDeltaSupport ...)` 与 `rho=trueDDeltaRho ...` 的 positivity、严格 `.599` 上界、squarefree、coprimality 和 unit bound 由已接入 TrueD 源码提供。trim、proper-power、rough-zero 及原 OneLong consumer 都保留任意满足这些条件的同一 `Q/rho`；OneLong 源码仍受其已登记导入闭包状态约束。

两调用的符号固定为：comparison 的 `(old,fresh)=(S false,R false)`；saving 的 `(old,fresh)=(eight false,six false)`。完整 medium 还要为这些实际 policy 连接原 whole-atom factorization／`MediumIndex` 覆盖，不能只凭 `|rho|≤1` 得到三个 primitive 因子。已有 `P1Full87TrueDPolicyDelta.trueDDeltaRho_test` 可把带 remaining filter 的原 signed delta 拆成 fresh、old 各自原有限族，再分别套其原许可并合并阈值；本审查没有证成任意 old/fresh 都满足最终 `P.Params` 的专用合同，也没有断言相关适配在所有历史来源中不存在。

对最终 compiled coefficient，`docs/source-only/20261112-resume/t03/p1-single-middle-next/P1OriginalSingletonMiddleTensor.lean` 已写出 `eventually_singleton_collision`、`actual_middle_to_tensor` 与允许独立 profile `kap`／trim `kap0` 的 `singletonAtlas`。应复用其 free→physical collision 和原系数，不重复证明，也不把其 Params 专用结论扩展成任意历史系数许可。

## 5. 新远端增量：复用范围与精确回执

本次只对已登记的两条分支执行精确 `ls-remote`，再按返回的新固定 head 读取相关说明／回执；没有 fetch，也没有扫其他 branch 或旧缺失 owner。观察值为：

- `codex/p3-5-full-kernel-20261125`：`ce38b7e8a5a2e7d501afe3a0213e08641dfbc777`。
- `codex/p34-kernel-20261125`：`b945f39a1e355ff4fcca9865ab59ffc97f2172c0`。

### P3.5：新增实际 test-seminorm 支付

[精确回执](https://github.com/UyNewNas/goldbach-formalization/blob/ce38b7e8a5a2e7d501afe3a0213e08641dfbc777/docs/part3-distribution/continuation-20261126/test-seminorm/RECEIPT.json)，Git blob `b10a7b2d655377e50b64469676595ecec62dc6d6`；[数学边界](https://github.com/UyNewNas/goldbach-formalization/blob/ce38b7e8a5a2e7d501afe3a0213e08641dfbc777/docs/part3-distribution/continuation-20261126/test-seminorm/MANUSCRIPT_BOUNDARY.md)，Git blob `4cbf7966a45e7f4b541e998f9d52d294c4f32691`。

数学提交 `0ef2ad29bfa30917b3b9ec7008cb831ad1af9408`；P3 task `83126d04315b4091805fa85e6da8d6e7`；两个模块共 40 owned declarations，strict/kernel/完整 ownership、types、transitive axioms 全通过。原归档 `p35-test-seminorm-0ef2ad29.zip` SHA-256：`4941a7950ca6850f7f6e922f435db473b22c2f2379b0161582a131feef14ae67`。

| 模块 | source SHA-256 | strict object SHA-256 |
|---|---|---|
| `Part3ActualSpectralTestJets` | `2e582af63a626283ee492189dd293a0ca3f64808c49fbb9da88246940df582df` | `074938d5fde13d0c5c542333f741eb5557140ccf07091444307d706f9c752e65` |
| `Part3ActualSpectralTestSeminorm` | `2d3407eb356b62ce75c5cd6edaa076015c2c98b076915a99556e4b95cf809252` | `302afd830f1fbbfe22857148011edc4219de33da660cfafcf5d59f123d1401a9` |

根定理 `Part3.ActualSpectralTestSeminorm.actual_uniform_testSeminorm_budget` 对任意固定自然数阶 `d`，先选 `C_d>0`，再对 `rho≥0`、`|sigma|≤1`、`Y>0`，支付逐 mode、逐导数先取 supremum 的真实 seminorm Fourier 和，预算 `C_d*(1+rho)^(4*(d+3))`。这扩展了已接受的 continuous Cauchy 与 whole-height 组件，不能重复重做。

回执明确 `actual_positive_negative_transform_application_completed=false`、`p35_closed=false`。实际正／负 transform 与 Pascadi Lemma D 的归一化、真实 cumulative energy 与谱行、physical family 统一性仍待接入；旧 Y04 六附件可用性仍按其既有边界处理。固定 `d` 的结论不宣称 Lemma D 只需 `d=4`。ABL、Kim–Sarnak、Pascadi 是原登记输入，此增量没有重新证明它们。

### P3.4：有限 packet、primary licences 和 exact dyadic assembly

[新说明](https://github.com/UyNewNas/goldbach-formalization/blob/b945f39a1e355ff4fcca9865ab59ffc97f2172c0/docs/part3-distribution/p34-20261126/README.md) 的 Git blob 为 `6d3f4d92dd405c4df74d7a2f560e35ad12e51f0e`；[EVIDENCE_MANIFEST.json](https://github.com/UyNewNas/goldbach-formalization/blob/b945f39a1e355ff4fcca9865ab59ffc97f2172c0/docs/part3-distribution/p34-20261126/EVIDENCE_MANIFEST.json) 的 Git blob 为 `778296b624d0a610c35e0f5a064fa4cf86f51170`。

| 已验收独立范围 | 精确数学源 | 模块／owned 数 | 原 report SHA-256 |
|---|---|---|---|
| packet／actual fixed-height cusp pairing／scalar phase | `145be87ff0a88914b607baa2a330bc88105a08d6` | 13／167 | `87a3c0d71452f34f9f6efe82ce6cadc8efa4b32e7c4bc7d4462d7c82888dc1b4` |
| actual finite primary arithmetic／ABL arithmetic licences | `e84c5a1c2f70f983de7bafc80472fa2d2eb947d0` | 4／63 | `745e03bb0d977a587ee22ce07b84e68ca53d3a1cecb9e9599c8a9981ee28c28c` |
| exact dyadic source／beta／energy assembly、short endpoint | 同上 | 9／168 | `3816662876f02fa036943164e682ec98c808ad9e9126434c9cdbaa3d2c6e5ff9` |

对应 report 为上述目录的 `packet-cloud-report.json`、`primary-clean-cloud-report.json`、`dyadic-clean-cloud-report.json`。范围有重叠；`ACCEPTED_SCOPE_UNION.json` SHA-256 `4e60281505e56b6d7980eb6d20cf61f58e61f441c9bd23c7e47c3751db271bda` 给出 19 distinct modules／294 distinct declarations，不是一次新 19 模块联合 kernel run。

[REMAINING_BOUNDARY.md](https://github.com/UyNewNas/goldbach-formalization/blob/b945f39a1e355ff4fcca9865ab59ffc97f2172c0/docs/part3-distribution/p34-20261126/REMAINING_BOUNDARY.md) 的 Git blob 为 `dd34c19d0fb015988661506256e00f22f20d498d`，SHA-256 为 `108418f04b04895b1f5cf913233a074678034f18daa6500dd4efe8a3f62d7e7f`。它仍要求真正 `FixedBlock/OriginalData` 闭包、实际 Fricke／completed-Eisenstein 接口、normalized spectral `R(n)` 识别，以及 actual oldform／regular-trace 装配。有限相位消去和固定高度 Fourier integral 不能充当 oldform spectral relation。

## 6. 下一步的最小工作分配

1. **P1 两长**：先接实际 singleton 活项几何与上述 generic 同系数字典，再逐项组装原 rough/strip/P2/有限总预算；不先造一个假设目标估计的结构。
2. **P1 medium**：保持原 live/dead、retained/tail 与 whole-atom 系数合同，复用现有 admissibility、SW 和 U06 子支付；完整 signed M 供应端跟随 P3.4/P3.5 当前工作，不另开同一谱核证明。
3. **full PP／history 终局**：核对最终 Params 与两个具体历史 policy 的原族覆盖，固定物理系数后选小解析参数，最后取同一充分大阈值；继续保留 source、box、sixth omission budgets 及 exact coprime mean。

本记录只确定源码连接路线和已登记接受边界。它不新增任何 Lean 接受、依赖对象可复用证书或完整 P1.5 完成声明。
