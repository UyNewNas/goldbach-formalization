# Q04 — P 后剩余供应模块定位

范围：只读核对本批简报、P30相关报告/独立审查、原稿对应段落、生产模块、P/O/M/I source-only 目录、显式隐藏 `.lake/proof-continuation/source-reviews/drafts`，以及 WSL native Goldbach 包源码。没有写 Lean、运行工具链/编译、Git、proof guard、数值回放或子代；只写本 Q04 目录。本报告是定位与边界说明，不重证。

原稿 `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex` 哈希与 BRIEF 一致：`ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`。相关约束在 795–817（同一 Q、Theta 归一化、true alpha）、823–855（70/36 action、三个 singleton/四个 good pair、D5 excluded cost、unit masses）、857–877（只读前代、430 seed-only history、嵌套近似和 reserve），以及 887–895（正测度 max-two clamp）。

## Enhanced：旧 collision 与新 repeat/center 必须分开

### 已有旧 selected-collision 同 Θ 付款

生产源 `ImbalancedChen/P2EnhancedCollisionThetaPayment.lean`（SHA256 `57e32fb7044442b6ebe68cef95a078a58f344b5eaf8bfd48ede34eea60f2049e`）的 `collision_theta_payment:50` 已给 `weightedCollisions ≤ epsilon * Theta`，见 50–90。阈值先于 N、Q、D、sigma 与所有标记 tuple；条件包括 even N、Q≤N、d>0、sigma≥0、1<Q/d，以及旧前缀质因数和新 prime cutoff 的固定 `N^eta` 下界。它以

- `ImbalancedChen/P2EnhancedCollisionWeightedBudget.lean::weightedCollisions_le`（约 163–186，SHA256 `60304cb46666459fca73b38d9090c02738fe5b3afcb6cb2d5c899cc31859a0c8`）
- `ImbalancedChen/P2EnhancedThetaReciprocalMass.lean::Theta_lower`（48–80，SHA256 `a1b6b5bc76c7724a5584cf71c18fc154559dffe457532d4481455a286243de1c`）

为每个原标记项保留 `sigma(d)/d` 调和质量，并用原 same-Q Theta 的下界付款。不可将这项称为“仍完全缺失”。P `reviews/t30_review_enhanced_final.md:43` 的最终审查也明确要求复用此供应。

### repeat / center：已有有限清理，尚无聚合付款

P20 `enhanced_switch_mass/P2EnhancedReceiverRoughPurification.lean`（`dfd047a5bc3d57f4ecee4078208f1de9fc777f9b6342a9cd4f72973dc1c075e6`）在 `repeatReceiver` / `centerReceiver` 定义处 28–46，给出精确 receiver 事件。48–99 给普通 rough receiver 的覆盖及注入比较；103–144 将 center 事件纳入 N 的 primeFactors，将 repeat 事件界到完整 divisor D 的 prime-factor floor sum，且保留 `d ∣ D`；147–160 排除 quotient=1。229–260 把有限逐词比较附到原始 word，并保留 collision；坏 Gamma5 的原 ordered labels、a0 cutoff、含等号 square gate 在 283–293。每一项仍是逐 receiver/逐 word 的有限上界。

真正仍缺的是把新出现的 `repeatWordMass` / `centerWordMass` 在真实正 marked family 上统一付款为 `o(Theta)`：要从实际 marks 推出旧前缀粗糙性和来源 multiplicity，且阈值需先于移动 d/actions/Q/正权。P20 `enhanced_switch_mass/REPORT.md` 的 “Purification and the remaining nonunit step” 和 P final independent review `reviews/t30_review_enhanced_final.md` 的 HOLD 均明确此缺口。可供转化的 native 候选和定义：

- native `MathlibNt/Wu2008DoubleSieve/SecondFunctionalHighNonunitActualFamily.lean`：`actualFamily_dictionary:30`、`actualFamily_test_dictionary:58`、`actual_source_geometry:85`、`actual_source_relative:104`、`actual_family_uniform:128`，SHA256 `7b10a3d8c033cd614e74da071e5f4c6fffd47b75e8753af0f8560ab832b05beb`。
- native `SecondFunctionalHighNonunitExceptionPayment.lean`：`source_bad_primeMass_log_uniform:65`、`source_bad_primeMass_pair_log_uniform:81`、`source_bad_primeMass_pair_theta_relative:106`、`sourceFamily_pair_le_good_primeMass:136`、`mother_source_pair_le_good_primeMass:155`。它针对该 native source family 的特定正 prime 例外。

这些是原生 HighNonunit source family 的候选定理，不等于 enhanced 原始 Gamma word 的 repeat/center 聚合：family、物理截断、same-Theta 规范化与所有 label/multiplicity 仍要建立实桥。不要跳过此适配或把 native 声明名当成增强供应已完成。

## Enhanced nonunit：有真实 finite density/quadrature 模块，缺原始 Gamma 汇总装配

native package 中相关候选包括：

- `SecondFunctionalHighNonunitActualFamily.lean`（上列 hash）：保留 literal physical family、实际 fibre/mass、标签 weight/cofactor 数据字典，及母源到 family 的比较。
- `SecondFunctionalHighNonunitClosedQuadrature.lean`：`uniform_finite_rows:16`、`closedPrimeK20_uniform:56`、`closedPrimeK21_uniform:75`、`closedPrimeK_pair_uniform:95`，SHA256 `0616fe4c5cd3db5ba4ec01e0494f52536a603fd59168b635bd6a376c424866cb`；这是 finite closed affine rows 的 prime-sum到 K integral uniform bridge。
- native 文件集还存在 `SecondFunctionalHighNonunitFiniteDensity.lean` (SHA `dba63a5edbc83f95f686ea146438bb3f71dd5f5957375b6cc08a67b38ad5e2e1`)、`SecondFunctionalHighNonunitExceptionPayment.lean`、`SecondFunctionalHighNonunitClosedMaskMass.lean`、`SecondFunctionalHighNonunitKThetaJoinedSource.lean`、`SecondFunctionalHighNonunitRoughPurification.lean`、`SecondFunctionalHighNonunitFiniteToClosedK.lean`、`SecondFunctionalHighNonunitErrorPayment.lean` / `FiniteErrorPayment.lean`、`SecondFunctionalHighNonunitRoughDensityJoinedSource.lean`、`SecondFunctionalHighNonunitSourceKQuadrature.lean`。这些是可核对的 native suppliers，而不是已绑定的 P enhanced Gamma 端到端结果。

本题所要找的差项是：将上面 native nonunit tuple/profile sum 逐项对齐 P20 `P2EnhancedReceiverRoughPurification.quotient_word_upper` / `original_word_upper` 与原文 Gamma5、Gamma9–21 所有颜色词/重复位置/target deletion/原 cutoff；再对 moving enhanced Q 和 true alpha 实现统一 endpoint/tail、bad Gamma5、repeat/center/collision 分项、同一 Theta 的 positive weighted lift。P20已供单位 Gamma20/21上界、true-alpha/true-li代数转换与零Theta处理，以及 per-tuple Buchstab 比较；它未声称上述原始 nonunit 聚合积分。原 production classical-Q `P2SeedOmegaSwitchedArithmeticFour` 的 `2/(1-2δ)` 和 source-box 前提、以及 classical receiver count 模块不能通过改名/提升 Q 来承担这里的 K/4 增强供应。

## H247：profile 基础可用，oldCount/seed许可和 occurrence 接口尚未闭合

1. **几何/积分公式：** O `h247_step_profiles/P2OriginalHalfOpenProfileCarrier.lean`（SHA `b03c234d28e28919745f5453cb23c672e6a6ce5c3b90777b3ecb26d93c820484`）保留原 half-open 单、双 prime 窗口、四个 pair domains、物理 ceiling 以及所有 cell/knot atom。`below_two_comparison:397` 是 frozenCount 对严格 cutoff 的 antitone 比较；`below_two_defect_transfer:408` 保留完整的 `A(w)-A(v)` baseline correction。两者都条件于 comparison argument v 上已经有实际 scalar licence。不能从此推出任意旧 H(v) below two 的上/下计数估计、seed或 H248/430 许可证。P `h247_step_profiles/REPORT.md:57` 也明说这项不能替代 old count/seed licence 与物理 comparison cutoff。生产 `P2HistoricDefectIntegralMeasurability.guardedH_below_two:63` 仅说明 `s<2` 时 guard 的 H 被置零，是积分可测封装而不是历史 count 数据。
2. **W1旧 prefix：** P9 `h247_moving_mass/P2OriginalPrefixMaskMass.lean`（SHA见P9报告：`12717d05bc4ba7c92679f37eaefec969f0c7f263a38284019f64c547a21fdf49`）在同一 `localPrimeFactor=1/p` 上给 `primeWindow_prefixMask:26`、`primeWindow_prefixMask_difference_le:40`、`compact_uniform_prefixMask_difference:66`；P9 `P2OriginalLiteralW1OldProfile.lean`（`4a55a30209362e327d91be162b305dee7990aec24d9ad46f78267f1d27968fe9`）给 `prefix_le_target_of_true_alpha:28`、`true_single_eq_N_window:44`、`all70_masked_old_profile_passage:99`、`all70_literal_sameQ_Theta_profile_passage:192`。它修复 W1 `primeWindow(d*N)` 对 O profile N-window mask；不是 count licence。
3. **W2物理窗口/状态：** I `w2_feedback/P2W2PhysicalChildFeedback.lean`（SHA `1865b377610c9bc2a05b76d9cfcbea350c571f669ce2d7687c829335a4ef2b50`）的 `negativeWindow:138` 保留 `primeWindow N` 和可能 p|d；`negativeWindow_eq_old_children:168`、`all36_negative_children:179` 识别真实上一代 lower child `d*p`。`window_child_query:144`、`PairGate:115`/`pair_query:118` 保留同 Q 的 full-square residual query，pair quotient cutoff 还通过 `quotient_pair_eq_frozen:95` 固定为 p。结合 `P2AllW2ImmutableCountRecursion.lean` 和 `P2W2StablePrefixCountConsumer.lean`，可复用 immutable predecessor read、all36 raw W2 action/labelled sigma 与实际 recursivePhi count consumer。I 报告说明：仍有非平凡 frozen-E complement counts，positive-child/repeat/collision/bad-Gamma costs 未付款；sharp filtered母体、analytic seeds、full history/count license及所有路径到actual rho仍 open。不能把 physical child query 证明误当成 W2 原始 occurrence到H247积分 profile 的完整 source reindex。

## H430：primitive L1预算现存，但实际 Theta/Jacobian 到 localBudget 的桥没有找到

- M `h430_common_approximation/Part5OriginalH430AbsoluteQueries.lean`（SHA `66f3223b1d05776561349063a48e00cd0cd90b54be2081c676565b729bd47b13`）：`data:84`、`atomSet:120`、`actual_query_integral:142`、`queryError_tendsto:159`、`queryError_zero_mass:199`。QueryIndex 是 `Fin441 × Primitive × FloorAtom`，证明了给定 primitive/固定表值的积分与其近似误差。
- M `Part5OriginalH430GeometricWalls.lean`（SHA `2732c16e9b1c0b6d7d07cdbe59ae4073271dd8e639c38aacd609450aee966284`）：`fullCell_keeps_equality:132`、`totalAbsoluteError_tendsto:147`、`exists_one_total_absolute_stage:154`、`exists_one_nested_absolute_stage:170` 给公共 refinement 的有限总误差/reserve。但被求和的查询标签并非原始 physical graph `GraphVertex/Program` action。
- O `Part5OriginalH430NativeQueryPaths.lean`（`118c03b4a44068a8cbb696f39699d12ff83b84d95a46f6d77b07b109f440cdeb`）：`W1_components_exact:43`、`W2_components_exact:48`、`actual_child_query:88`、`nativeRank_exact:148`、`actual_ancestor_choice:214`、`occurrence_query_exact:235` 有真实 query/component labels；全祖先与真实 arithmetic history仍需 caller/source许可。
- P `h430_smooth_causal_boxes/Part5OriginalH430MovingBuchstabAtoms.lean`（SHA `e315a51795bd9b3d77232857a1f743b67e223959696e69f78f272fbf93f6c873`）：`occurrence_moving_atom_exact:112` 连至 O Program occurrence，`startAbsoluteError_bounds:194`、`actual_upper_start_absolute_error:213`、`actual_lower_start_absolute_error:226` 给**固定物理父状态**的 moving Buchstab start一维 L1误差；未对父prime family以真实Theta密度积分。
- production `ImbalancedChen/RenewalFiniteErrorPropagationP5.lean`（SHA `804709bc71b85ce677a585c1dbe6e9d90527eb40befad03f99214e7b6a0eeadd`）: `localBudget:29` 精确要求 base差 + 对实际 atoms 的系数差乘 old table value 绝对值；`actionValue_total_error:96` 是对实际hlocal的通用消费，`iterate_430_rounds_11_depth:239` 才接入真实441步传播。没有来源模块把 M 几何总L1误差等同于这个本地加权和。

所求缺桥因此仍是：对 immutable seed-only430 的真实历史与 physical parent occurrences，按 `actualTheta` 权重/原prime-carrier密度及真实坐标 Jacobian 积分每项 moving/local错误，保留base/weights/table values/重复 occurrence/scalar，再把该积分之和等同或上界到 producer 的 actual `localBudget`，并将其接到 `iterate_430_rounds_11_depth`。M summary 的 `Fin441×Primitive×FloorAtom` 不自动是物理源 occurrence 列表；P 的一维 start L1也不自动给这一聚合上界。P t25 review与P H430 REPORT明确仍缺 immutable430 source history、weights/base/scalars、各代旧状态读取与预算恒等式。

## 隐藏草稿和 native 搜索结果、判定

显式用 `rg --hidden --no-ignore` 搜过 hidden `.lake/proof-continuation/source-reviews/drafts` 的 `repeatWordMass`、`centerWordMass`、`actualTheta`、`oldCount`、`below_two`、`localBudget`、`Theta/Jacobian` 相关标识。隐藏稿中存在一批先前 upper/H430、source integration、nonunit候选；在本次目标词下没有发现一份端到端供给以上增强Gamma异常、oldCount/seed许可、W2全 occurrence-to-profile、或 H430 `actualTheta`/物理Jacobian-to-localBudget 拼接的额外现成模块。可重用范围以上列正式模块和native声明为准，隐藏稿只作候选/历史材料，不把文件名或登记中的目标当作证明。

此清点将缺口归为：enhanced repeat/center 总量、原始 nonunit Gamma 对 enhanced marked source 的积分拼接、H247 oldCount/below-two 的真实历史计数许可及W2 occurrence消费、H430 physical Theta/Jacobian/localBudget身份仍未供应。没有据此重证或判断原稿为假。所有相关source-only Lean均uncompiled；数学适用性须由证明代理判定。


