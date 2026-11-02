# P / task 21 — actual rank-three restoration and finite signed history refinement

状态：**SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT；P1.4.history、P4A.4.actual_all22 均 OPEN。**

新增两份 Lean，只写本任务 P 目录。没有修改 O、production、旧批次、共享索引、原稿或 Git 状态；没有运行 Lean/lake/CI、finite guards、数值重放或子代代理。

## 实际新增内容

`P4AOriginalRankThreeRestorationSource.lean` 补上 O 已有 rank-three admission 事实与真实 finite source 之间的缺项。

1. `beforeThirdPolicy` 在真实历史 first/second decisions 后枚举**所有候选第三节点**。`signed_difference_before_third` 直接从 `signedTest`/`firstExitDepthFrontier` 递归证明 before-admission 差等式。它不从 old retained rank-three frontier 开始，所以不丢新恢复的三元组。
2. `secondChange_eq_candidate_sum` 把 O 的 `secondChange` 接到这个实际 occurrence List。`activeSecond_append` 与两个 continuation 定理证明 support 和 cap 只读取同一第三/第二祖先。
3. `rowChange_eq_retained_add_restored`、`secondChange_eq_retained_and_restored` 给出完整分解：旧已接纳项是新续树减旧续树；旧拒绝而新接纳项是**一个完整新续树**。旧接纳蕴含新接纳由实际 `originalSeed_lt_second` 与普通 Rosser admission 单调性证明，未假定 signed coefficient 单调。
4. `disabled_small_third_row_zero` 证明 `p3 < N^omega` 时 before-test source、retained 项及 restored 项同时精确为零。没有把该分支从 `Theta-2e` 换成 `v(x)`，也没有把它的极限损失当作已付。
5. `restoredTerm_eq_actual_lower_residual` 和 `retainedTerm_eq_actual_lower_difference` 对真正 `roughPrimeUniverse` 上的候选前沿给出 literal ordinary residual 字典。记实际三元组质量为 `m`，真实旧 coarse level 为 `Qold=rawLevel(...)`，第二新 cap 为 `Qnew=N^secondExponent`，则新减旧的源为：
   - 旧已接纳、support 激活：`m * (Minus(Qold/prod) - Minus(Qnew/prod))`；
   - 旧拒绝、新接纳、support 激活：`-m * Minus(Qnew/prod)`；
   - 未激活：零。

其中最后素数 cutoff、完整三元组乘积、负号、质量和 remaining carrier 全由 `actualPrimeFrontier_geometry` 供应；旧 admission、未来 continuation 相等或 residual 恒等式均不是公共定理的目标型假设。这里没有 Chen quarter、ordering factorial 或额外 gain。

`P4AOriginalFiniteSignedHistoryRefinement.lean` 为上述真实源建立同一个 pre-N finite **source partition**。

1. `nativeTests d` 的数据在 `N` 之前固定，包含原 first decision、第二/第三 guard、第三 support、旧/新第三 admission、small-third gate、**全体**第三 half-open mesh owners（包括 unselected owners）、原第四/第五 row eligibility 和实际重新检查父 cap 的十一 sixth cells。
2. `PrefixTest.read` 只读取自身 rank 的 `rosserAncestor`；未到该 rank 返回 `none`，已经到达则保留 true/false。`signature_coordinate_causal` 证明后来的选择不能修改已经确定的祖先标签。此构造没有投影 child wall 来选父决策。
3. `refinedSum_eq` 对有限 signature 的原始 List fibers 证明 exact signed regrouping；未转成状态集合，不丢重复 occurrence。`refinedRoot_eq`、`refinedSecond_eq`、`refinedThird_eq`、`refinedAction_eq` 把共同分区分别接到真实根叶、before-third restoration source、当前第三前沿及当前各 action 前沿。
4. `common_refined_original_gain_telescope` 将新 restoration 字典接入 O 的同一 `rho`、同一完整 modulus test 和同一 beta-sign attachment telescope。原第四/第五 gain 只扣一次，sixth/eighth 仍是 held constructor 的真实 `sourceChange`。`refined_archive_fifth_gain_preserved` 直接复用 O 的 signed preservation，而没有重建第五积分 kernel。

**边界：finite source partition 不等于有限 buffered cap approximation。** 本文件没有把点态 `v` caps 变成所需的有限 strictly buffered boxes，也没有建立整个 All22/87 的共同历史 margin。

## 精确复用与去重

以下路径均相对 repository root。完整 SHA256、声明及 direct imports 见 `REGISTRY.json`。

| 已有源 | 本次复用的真实结论 |
| --- | --- |
| `docs/source-only/20261102-resume-30o/all22_common_history/P4AOriginalCausalHistory.lean` | `secondStage`、`secondChange_eq`、`original_second_third_telescope`、`small_third_not_selected`、`archive_fifth_signed_gain_preserved`、`held_final_source_with_original_gains`。此文件的实际 4/5 gains 与 telescope 已存在，不重写。 |
| `docs/source-only/20261102-resume-30o/all22_common_history/P4AOriginalCommonArchiveSchedule.lean` | 已有 `exists_fixed_archive_and_whole_fourteen_schedule` 统一 retained14 与原 fifth archive 的 schedule；本次读取但不导入/复制。它没有提供所有源的完整 schedule。 |
| `docs/source-only/20261102-resume-30k/fallback_payment/P5OriginalCommonThirdScreenedSource.lean` | `selectedThird_append`、`originalSeed_lt_second`、真实 supported/unsupported dispatch。 |
| `docs/source-only/20261102-resume-30k/fallback_payment/P5OriginalCommonThirdActualLowerSource.lean` | `old_third_continuation`，用于真实旧 coarse continuation 的 residual 字典。 |
| `docs/source-only/20261028-resume-30e/coefficient_physical/P5OriginalCommonRefinedPreservation.lean` | `old3_after_two`；由实际 `frozenLevel_eq_rpow_seed` 认证旧 cap。 |
| `ImbalancedChen/ActualFrozenFrontierDensity.lean` | `actualPrimeFrontier_geometry`、`firstExitRetainedPolynomial_frozenParity_frontier_density`。 |
| `docs/source-only/20261028-resume-30e/coefficient_physical/P5OriginalCommonRefinedSource.lean` | `sourceChange`、`source_next_sub_current`，原 sixth/eighth 范围完整保留。 |
| `ImbalancedChen/HistoricalJointMeshFiniteRefinement.lean` | 已有单一历史 mesh 的完整 fallback fiber/祖先求和恒等式；没有复制这些结论。新文件只补不同真实 source occurrence lists 的共同 finite signature 重组。 |
| `docs/source-only/20261102-resume-30k/all22_remaining/P4AOriginalSecondResidualSupplier.lean`、`docs/source-only/20261102-resume-30m/catalog5_source_integral/P4ACatalogFivePrimeIntegral.lean` | 已有 catalog5 ordinary prime-pair source 与 integral limit。读取并保留，不再推一次积分；未把它们的 endpoint pair source 无证等同为历史 finite source。 |
| `docs/source-only/20261102-resume-30k/saving16_glue/P2OriginalSaving16CommonOldPolicy.lean`、`ImbalancedChen/P4AAll22OriginalKLedger.lean` | 已有 retained14 history 与 exact rational budget；读取，未把这些局部/数值结论当 All22 history。 |

O 同目录实际只有上述两份 Lean，没有 REPORT.md/REGISTRY.json 可读。本批没有修改或替换它们。两份新文件的 direct imports 顺序为 O CausalHistory → P RankThreeRestorationSource → P FiniteSignedHistoryRefinement；历史 source-only modules 仍须按 registry 安装，未声称当前本地 import closure 已编译。

## 原稿定位与未闭合项

主稿 `manuscript-body.tex` SHA256 为 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`，已核对 371–509、1327–1369。

- 371–374：successive new-minus-current-parent；改善一个 enclosure 不能产生第二 cap/gain。新 finite telescope 遵守此规则。
- 379–418：真实有限上筛及 ordinary residual 身份；本批只实现上述有限源字典。
- 453–458：pre-N 有限因果近似及 proper-wall/structural-equality 处理。新的 partition 保留所有实际分支，但完整近似误差仍未实现。
- 494–509、1327–1336：四正项减 22 savings，full third tail 只替换一次。未声称本批 telescope 已对应这 22 个 source。
- source note `global-positive-upper-completion-20261010.txt` 55–127、183–216：旧 fourth/fifth/sixth telescope、above-mu 二/三分离、small-third tail、各自祖先标签与所有 allowances。本批 finite restoration 实现了其中一个遗漏的有限 deduction。
- `eighth-prefix-family-20261009.tex` 105–124：共同有限历史必须证明各 retained descendant 的 `H3,H5,H7<lambda3`，不能用理想 `L3=R` 替代。本批不作这种替代。

仍需完成：

1. 将本批 exact coarse/restored residual sum 与 catalog5 的 endpoint ordinary **pair** source 连接，实际支付 `rawLevel` 到 `v(x)`、未选 coarse cells、order-wall 及 disabled-small-third 的统一误差。已有 M prime-pair limit 不会自动支付这些项。
2. 将第二/第三 pointwise `v` caps 作原稿要求的 finite strictly buffered approximation；统一误差选择顺序，保留先前 ancestor decisions。`nativeTests` 是 exact source-label bank，不能代替这个构造。
3. 原第四 archive rows/licence 仍是 primitive data；`FourthGeometry s.data` 仍是 O 实际 fifth signed-preservation theorem 的几何前提。
4. full87 理想 dictionary/dispatch 由 task12 负责；本批不定义、复制或冒认其完成。held eighth `sourceChange` 尚未与全部 adopted source groups 同一化；完整 all22 history/source associations、全 third tail replacement、两 reserves 及最终 K 密度仍 OPEN。

## 困难分类与静态检查

分类 (2)：before-rank-three 全候选源、restored whole continuation 和小第三禁用项，是可补的遗漏推导；本批已写出独立递归证明与真实 residual 供应。分类 (1)：Lean 表达/API 仍未编译；已逐项核对主要现有 declaration，修正递归 parity 的 length 推断、`signedTest_one_eq_polynomial` namespace 和 finite-sum tactic 的静态问题。分类 (3)：未发现足以认定原稿有实质数学缺口的证据；余项付款与全 history 不能由当前局部代码推出。

只做文本读取、声明/API 对照、SHA256 与 metadata 检查。新 Lean 中没有 `axiom`、`sorry`、`admit`、`native_decide`、`#eval` 或 `#check`；未运行任何 Lean proof guard。task26 审阅给窄 finite-source 内容正向静态意见，明确未升级为 compiled/kernel-verified。
