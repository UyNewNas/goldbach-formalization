# R07 / D05 — actual catalog-five global losses

本目录只供应同一 `HistoricalThirdCoarse` / `OriginalData` 的实际损失。七份新 Lean 源码均 **SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT**；未运行 Lean、Lake、compiler、guard、数值重放、CI 或 Git。有限 guards 一律 **UNEVALUATED**。七份完整 proof bodies 已经 R25/R26 独立静读，原生产 actual-tail/moving-budget/prime-log 和 Q 字典签名也已交叉核对；不将其窄范围 source-level PASS 记为 kernel 验证。

本次已实际消去 Q21 所列的完整 `coarseRow` 加权误差、`omittedRow` 的两个 order walls、disabled-small-third 的完整绝对加权尾和，以及未 trim 历史 pair 域的边界损失。末端 `exists_complete_actual_catalog5_approx` 将原实际 `-secondChange` 在 `T=1` 下接到 M/J 原 `physicalSaving`，**不再带 `smallOmittedSum` 或任何未付尾项前提**。此前四份中保留尾项的中间结论继续有效，末三份直接支付该项；没有把 disabled action 等于零解释成 comparison omission 等于零。完整 full87/All22、beta-attached `hdensity` 和两 reserves 仍 **HOLD**，本次不把 ordinary catalog5 供应冒称这些总装已成。

## 原稿及复用边界

原稿 `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex:371–509,1327–1369` 的原 `rho=19/96`、全部四正项减二十二 saving、共同 pre-N schedule、保留粗历史决定和 firstStop，是本供应的范围。原始 SHA256 为 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`。

对应 source note `../chen-imbalanced-semiprimes/paper/source/modules/global-positive-upper-completion-20261010.txt:55–281` 的 SHA256 为 `49d61d20569c83bc05e6221992262c9c42aea275b90ab67d74b0d33514832a42`。其中 198–205 的完整激活 tail 界 `18 h/(u-h)^2 * (log(rho/h)^2+2 log(rho/h)+2)`，`u=rho/2`，是趋零的解析尾界；它本身没有提供本目录实际有限 `omittedRow` 加权尾和的字典及统一误差。

先读 Q21 的 REPORT/REGISTRY 及 `Q/reviews/q30_review_history_final.md`，并检索 production、全部 source-only 和被忽略的 `.lake/proof-continuation/source-reviews/drafts`。复用 Q21 的有限 retained/restored 对 endpoint-pair 的带两差项恒等式、真实历史 pair carrier、compact 精确 carrier 相等和 rawLevel 单项统一阈值。没有重做该有限字典，没有换成另一套 ordered-portions dyadic policy。调用的 canonical lower factor regularity 仅是实际 residual 的解析函数界。

## 新源码及实际证明内容

| 源码 | 可消费声明 | 供应范围 |
|---|---|---|
| `P4ACatalogFiveCoarseWeightedPayment.lean` | `coarseRow_normalized_eq_gated_difference:171`，`exists_complete_coarseRow_payment:264` | 将实际 old/endpoint admitted continuations 连同 strict own-cube gates 接到 Q 的统一 residual 估计；对**全部候选 occurrence 的绝对值和**付款。 |
| `P4ACatalogFiveHistoricalPairBoundaryPayment.lean` | `exists_uniform_discarded_pair_payment:163`，`exists_historical_endpoint_approx_integral:222` | 未 trim 历史 pair 的**绝对**算术边界付款；完整历史 endpoint source 逼近原 M/J `physicalSaving`。 |
| `P4ACatalogFiveOmittedOrderPayment.lean` | `compactOmittedAbsoluteSum_eq_actual:51`，`exists_compact_omittedRow_payment:235`，`omitted_sum_sub_small_abs_le:314` | `t3>=h` 上 actual omittedRow 的绝对权重总和；原 firstStop 推出真正未选候选落在两个 order strips；小于 h 的部分保持显式。 |
| `P4ACatalogFiveGlobalLossReduction.lean` | `normalized_actual_identity:44`，`actual_saving_plus_small_omission_error_le:68`，`exists_actual_saving_approx_with_small_omission:90` | 对同一 d 的三个已供应付款取 min width / max threshold，得到只剩一个显式尾项的实际 saving 逼近。 |
| `P4ACatalogFiveSmallThirdMass.lean` | `lastLogMass_le:62`，`exists_uniform_secondMoment_bound:109`，`tailBox_mass_le_harmonic:148` | 原 `[3/16,rho)^2×[0,h)` actual prime box 的第三坐标二阶矩 `<=M h²`，M 先于 h；包含全部原子及 target deletion。 |
| `P4ACatalogFiveSmallThirdEndpointTail.lean` | `guard_geometry:42`，`tail_physical_gaps:58`，`exists_eventually_endpointDifference_tail_bound:109` | 原第二 guard 导出固定 rho 物理分子 gap、两 strict own-cube gates；真实 lower residual pair 的完整 tiny/middle 界，常数和统一 N 阈值先于 h/tuple。 |
| `P4ACatalogFiveSmallThirdPayment.lean` | `smallOmittedAbsoluteSum_le_tailAbsolute:64`，`exists_uniform_smallOmittedAbsoluteSum_bound:167`，`exists_complete_omittedRow_payment:231`，`exists_complete_actual_catalog5_approx:262` | 原候选 List 的全部 small omitted absolute rows 付款；完整 omitted absolute sum 付款；无尾项的原实际 catalog5 与物理积分统一逼近。 |

完整 coarse 证明先从实际 rank-three frontier 的 geometry 得出质量、奇偶和递减素数历史。`admittedOrdinary_normalized:51` 保留当前 admission gate；`old_admitted_eq_ordinary:88` / `endpoint_admitted_eq_ordinary:119` 把实际 continuation 转为该字典。旧 prefix 被拒时对应零 gate，未假定 before-test 候选已通过旧测试。active triples 的第三素数至少 `N^omega`；固定 `0<h<=omega` 后所有 active tuples 都在 `[h,19/96)^3` 的实际 target-deleted prime box。原 List 到 admitted tuples 的已有精确求和定理保留 occurrence 权重；不是任意去重。

全域 pair 证明使用生产 `P1ActualUpperNearOneBound.exists_p1_actualSmallRosserPlusDensity_endpoint_normalized_bound:209`，它控制实际 upper residual，包括 s=1 端点。原物理域使所有历史 pair 落在 `[3/16,rho)^2`；两个 residual 的绝对值给整个 pair saving 的统一界。未 trim 部分位于 M 原四墙 `trimForms` 的闭 strips，含 prime atoms；`AffinePrimeWallReserve.exists_actualPrimeAffineWallStrip_mass_lt:132` 支付实际权重。Q 的 `historical_trimmed_sum_eq_catalog_arithmetic:583` 接回 M 的 compact prime limit，再让 trim 积分趋向 `physicalSaving`。全程没有由正积分推出有限 residual difference 逐点非负，没有免费丢历史 pairs，也没有抹去 firstStop。

order 付款使用两条真实墙 `t1-t2=0`、`t2-t3=0`。Q `candidate_original_firstStop:187` 从同一 before-third 历史导出原 firstStop；Q 的 actual unsupported localization 随后排除 `p3<N^omega` 或定位至 order strips。在 `omega<=h<=t3` 时前一分支不可能。两个 endpoint 的完整 gated residual 由 Q all-cap compact supplier 和已有 canonical lower factor normalization 控制；闭 wall mass 付款处理全部等号及原子。`smallOmittedSum:308` 仍是原 List 中 `t3<h` 的 signed omittedRow，含禁用 small-third 的 comparison source。

完整 small-third 付款不改变这个定义。首先 Q 的 `secondRegion_iff_catalog_domain` 和 J 的 `physical_denominator_bounds` 供应 `rho<=v(x)-x-y` 与 `rho<=v(y)-x-y`。**这是原第二 guard 的固定 gap，与 d.omega 无关。** 当 `t3<rho/6`，两 actual own-cube gates 严格通过，两个除去完整三素数乘积后的 residual levels 均至少 `N^(rho/2)`。`P1FifthMiddleNormalizedPointwise.exists_eventually_actualMinus_middle_quadratic_bound:262` 是任意实际 residual levels 的 arithmetic supplier；仅消费其通用声明，不使用任何第五 policy/source carrier。它给 movingCutoff 以上的真实 lower pair `<=B t3²`。

在 `t3<movingCutoff(rho,N)`，已有 `sourceBudget_of_power_cutoff`、actual `exists_actualMinus_pair_exp_bound` 和 `tailEnvelope_le_uniform_exp` 给完整 lower deficit 对的 `A exp(-movingBudget(N))*|logN/SS(N)|`。两个 residual 使用同一实际 cutoff `p3`、同一目标和同一 Euler product；baseline 已在原 actual pair-exp theorem 中准确抵消，完整主 tail 与显式源误差均保留。之后使用真实 Euler product `<=1`，并未凭有限 residual 正性丢项。整个候选 tiny 质量被原全三维 harmonic box 的 `H(N)^3` 控制；`H>=1` 给 `H³<=H⁵`，已供 normalized moving majorant 真趋零。

middle 权重使用新实际二阶矩：前两轴固定正 box 的质量有界，第三轴的 `sum log(p)/(p-1)` 由已证 Chebyshev/Abel prime mass 控制，得到 `sum weight*t3²<=M h²`，M 先于 h，不要求在零端点套 Mertens。原 List 的 `smallOmittedAbsoluteSum` 通过真实 frontier tuple 精确求和保持 occurrence/mass，再扩到带原 second guard 的 tail box；只作非负绝对值上界，不把候选视为另一政策。于是有统一 `D>0`，先于 h 与**所有** d，对每个 `0<h<=rho/6` 供应 N0（可依赖 h，先于 d），所有后来 even N 的 `smallOmittedAbsoluteSum d h N<D*h`。这直接包含 disabled-small-third 的 comparison omission。

## 参数顺序及同一实例

1. coarse：先给 `0<h<19/96` 和 `epsilon>0`，供应 `delta>0,N0>=2`；随后任意 d 满足 `h<=omega`、`0<e<(3/256)/100`、`chi<e/10`、`3chi/2+2e<=delta`，任意 even `N>=N0` 都有 `coarseAbsoluteSum d N<epsilon`。不是每条后来的 prime tuple 另取 N0。
2. pair：给任意正 epsilon，供应 `delta>0,N0>=2`，随后所有 `e>=0`、`4e+meshStep(m)<=delta` 的 d 均满足 `|normalizedHistoricalEndpoint d N-physicalSaving|<epsilon`。firstStop 仍属于实际 carrier，δ 清除内域历史障碍的依据是 Q 已供 compact carrier 定理。
3. compact omitted：先给 `h,epsilon`，再供应 `delta,N0`；随后所有 `omega<=h`、`meshStep(m)<=chi`、`2meshStep(m)<=delta` 的 d 均有 `compactOmittedAbsoluteSum d h N<epsilon`。
4. 中间 joint：固定 h 后，三者各分 epsilon/3，取一个共同正 δ 与一个共同 N0，再任意选择满足上述宽度条件且 `omega=h` 的同一 d；所有后来 even N 有

   `|normalizedActualSaving d N + smallOmittedSum d h N - physicalSaving| < epsilon`.

5. 最终 ordinary actual catalog5：给 epsilon>0，先由实际尾项常数 D 选 `h0=min(rho/12,epsilon/(4D))>0`。任意 `0<h<=h0` 后，取中间 joint 的 epsilon/2 共同宽度 δ，以及它与尾项 N0 的 max。随后任意**同一** d，`omega=h` 且满足第 1–3 项原宽度、任意后来 even N，有 `|normalizedActualSaving d N-physicalSaving|<epsilon`。`exists_complete_omittedRow_payment` 同样先 h0、再 h、再 order δ/N0，给整个 original omittedRow **绝对值和** `<epsilon`；不是只支付其 signed sum。h=omega 是允许的一套共同参数选择，固定 rho gap 的证明未使用或改写 omega；独立 cutoff 的更一般变体不是此数学供应的额外义务。

这里 `meshStep(m)=(19/96)/(m+1)`。尚未从本目录构造包含 full87/全高秩 cap 的最终共同 d；这些明确的几何宽度可由 R08/R10 的原 schedule 消费。R10 可在其原 schedule 的 h 选择中再取上述 h0 上界，从新终端直接消费普通 actual catalog5 无尾误差；整个 beta-attached density 仍需其余真实来源。原 ledger 已支付的第三 finite-density `u_d/4` 没有再次支出；本目录也没有花 compiler reserve `u_c`。

## 已消除的前提与剩余工作

已消除：完整实际 coarse absolute sum 小于任意精度的前提；完整 source-domain pair complement 小于任意精度的前提；正 cutoff 以上原 omitted order sum 小于任意精度的前提；**完整 actual small-third omitted absolute sum 的统一小量前提**。末端从实际对象供应整个 ordinary catalog5 近似，不接受目标同义尾项/误差、有限 residual 正性或 firstStop 消失前提。caller 只供应原正参数、所显示的共同宽度及 even large N。

仍需：把 actual secondChange 的新全域供应接到同一完整原政策的其余 All22 增量；完成其余 density/独立 compiler reserve、beta-attached physical coefficient 与 full87 的 source 映射。七份代码的 ordinary residual 字典针对 `T=1`；不能宣称任意 beta terminal test 的密度误差已供。此前原 small-third 欠项现已补齐，不再把它重复列入 ordinary catalog5 的缺口。

复用生产 actual-tail/moving-budget/Chebyshev 声明只计原供应；本次新增的是原第二 guard 固定 gap、三阶 actual endpoint residual 的严格门控转换、真实小坐标矩、原 candidate List 的完整尾量付款及共同 pre-N 消费。REGISTRY 单列这些真实复用声明与原路径哈希，不把旧 supplier 重新计作新证明。

困难分类：(1) source-only imports、Lean elaboration/API 核验属于表达与验核；(2)本次已补的实际字典接回、四墙/两 order 墙加权、完整 small-third 加权和共同阈值，属于可补的遗漏推导；(3)目前没有由这些形式缺项证明原稿有实质反例。full87/最终 attachment 仍属另行所需的真实来源工作；未运行 compiler 不是数学反驳。

## 冻结记录

| 文件 | SHA256 |
|---|---|
| `P4ACatalogFiveCoarseWeightedPayment.lean` | `d75c3fe5a6ad1b1cb0288a963c85883066cfb71c11b278d2170bd23385cbad40` |
| `P4ACatalogFiveHistoricalPairBoundaryPayment.lean` | `6f5e7afb57917f802a69f56e060d545eed88aa9c4b250d2a68405758b75eb066` |
| `P4ACatalogFiveOmittedOrderPayment.lean` | `513c1f780a01b14daa00e389e76198b5c660db12cec0948eddb52f2ecf058259` |
| `P4ACatalogFiveGlobalLossReduction.lean` | `d94fb146bdb77803d9b88fbafdb15a39a81ee332e639ea70ae29bc63371008aa` |
| `P4ACatalogFiveSmallThirdMass.lean` | `8ad9e0ac507338562765be5fe75cb6b91085336e93fd3dc9c1225c0a4d66b660` |
| `P4ACatalogFiveSmallThirdEndpointTail.lean` | `8b5b95d9c39fbe73105195416ebd898aa1ca75fb7001fc33c5c42f5de4f20e5c` |
| `P4ACatalogFiveSmallThirdPayment.lean` | `7df560c710c07b0c823f92c7bddc29f6ded9b8bf0f3246e5029aa186d8b5dfc7` |

`REGISTRY.json` 给出每份新源的 raw bytes/行数/namespace/所有声明及 import 行，直接 source-only imports 的唯一复用路径，以及本次实际使用的原 source 与生产证明声明。源路径解析不是已安装的 import closure；未安装或改写任何旧文件。REPORT 的 hash 记录于 REGISTRY；REGISTRY 自身不做循环自哈希。
