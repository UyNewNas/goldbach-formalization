# all-source S 之后：原 U5 的实际 (F) 与 common-Q 下一义务

日期：2026-11-25。源码审查基点 `e4ad395e4901628d85a27d17d0f87a16ea943433`。本报告只核对这一条供应链，不重复全仓审计，不执行编译，不重写既有 greedy、tail 或 whole-height 数学。

**结论：all-source/signed 候选已在源码层供应字面 selectedPolicy 的全部实际历史与完整词两套平方；它没有自动供应 (F) 的合法子集、整个 atom 上固定的三因子表示或 common physical Q。最窄的新推导是原 root 的真实 V winner → 原 singleton/pair prefix → exact local critical interval 和 remainder budget。此推导现已写成独立 `P3OriginalU5RootVInputs` 候选，仍未编译。W、fresh-row whole-box licensing 与完整系数族接线继续开着。**

## 1. 稿件与量词

手稿只采用 `UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`：

- [coefficient-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/coefficient-appendix.tex)，blob `10f3e2efb2074a9b97148a5151956e1d450be13f`，`coef:full-squares`、`coef:selected-squares`、Three-factor representations、`coef:three-monomials`、`coef:tensor-identity`、`coef:parameter-order`、`coef:prime-product-insertion`。
- [sieve-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex)，blob `bf8bae30ff18f21d716138af0cc6d9fbb4a80747`，`sv:finite-feedback`、`sv:child-state`。
- [argument.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/argument.tex)，`eq:current-PP`：原 signed AP 项与原互素均值保持同一 rho。

coefficient appendix 的本地参数为 `q₀=log_x N`、`alpha₀≥q₀`、`theta_cov=q₀ ell+2ζ`、`D=x^(theta_cov−2ζ)`、`A=U x^(−ζ)`。所选 upper-endpoint exponent 必须满足

\[
2\theta_{\rm cov}-1\le b_I\le
\min\{(32-39\theta_{\rm cov})/34,
(2-2\theta_{\rm cov}-7\alpha_0/32)/3\}.
\]

所有 exponent 已换成 base x；全部 full/selected squares 在 `q₀ ell` 上检验。算法必须只读整个 atom 的端点和 medium length，不能按个别算术 tuple 或 discrepancy 符号重新挑 partition。

`q₀≥1` 的精确来源是 compact-margin 段明写的 `q₀∈[1,1+κ*]`，或另行证明该局部 chart 有 `x≤N`。一般 medium complete-scale 条件只写 `c₀x≤N≤x^(1+κ)`；不能由它无条件推出 `q₀≥1`，也不能用 `q₀≈1` 声称普遍不相容。先前 `.599` 必要不等式审查仍按其明确分支量词成立。

## 2. root S-mask 与 (F) 子集的实际区别

原 `Part5OriginalUpsilon5CausalDictionary.level` 是 `max(v(t), max(v(t+u), B(a)))`。all-source 的 `.root` S-mask 有两个 true 外标；这只是已供应的 selected-square mask，不是已证明的 (F) winner。

一个精确几何见证说明不能直接填入原两标乘积：取原 triangle 内 `u=3/25`、`t=7/50`、buffer `b=1/1000`、`ζ=1/10000`，在具体局部基 `x=N` 取 `q₀=alpha₀=1`。则

\[
v(t)=57/100,\quad v(t+u)=801/1600,\quad
B(a)=90621/160000,
\]

原赢家为 `v(t)`。使用已有 once-buffered cover，`ell=569/1000`、`theta_cov=1423/2500`；临界上界为 `12857/60000`，而两标和 `13/50` 比它大 `2743/60000`。singleton `t=7/50` 则落在所需区间内。

这是原 geometric domain 内的精确点，不是假称某个 N 已存在相应整数素数组。它揭示的是**接口缺项**；并没有推翻已证明的两套 S squares。

正确下一步为：原 `v(t)` 路由取 `[t.2]`，原 `v(t+u)` 路由取 `[t.2,t.1]`，原 `B(a)` 路由保留 W。两条 V 的 complement support 可直接由原 full support 和现有 `actualDwell_selected_prefix_budget` 得出，无需改 all-source 的 mask 或重新做归纳。

## 3. 已实现的具体后继候选

新文件位于 `docs/source-only/20261125-p36-root-v-inputs/ImbalancedChen/P3OriginalU5RootVInputs.lean`；同目录 README 给出完整量词。

`native_U5_root_V_inputs` 从字面非零原 native rho 内部取得原 witnesses，再保留 `SignedSupply`。当其返回的真实最后来源为 `.root` 时，它内部计算原 max 的 route，返回 W 原值，或返回以下 `RootVInputs`，而不把这些结论变成前提：

- 合法原 singleton/pair 以及其真实 `rootLevel=v(s_I)`。
- `q₀=log_x N` 的 exact 换底，`alpha₀=1+3κ≥q₀`。
- `D=N^(rootLevel−b)=x^(theta_cov−2ζ)`、selected product 的 exact 幂恒等式。
- `theta_cov+b/8≤v_(1+3κ)(q₀s_I)` 和完整两上界的 critical interval。
- 同一 canonical 完整 modulus word 的 full D-well 及所选 prefix 的 remainder D-well。

附加输入仅为明确局部域 `1<x≤N≤x^(1+κ)` 和原 buffer 的标量分配 `0<ζ≤b/8`、`0≤κ≤b/4`。这些可在 `x=N` 的具体局部基非空地实现；但尚不能代替实际 medium family 的尺度证明。

新换底估计是 `q₀v(s)−κ≤v(q₀s)`。原 buffer 先给 `theta_cov+b/4≤v(q₀s)`，再直接复用旧 `actualSelectedSubproductV_residue_margin` 和 `actualSelectedSubproduct_critical_iff`。middle line 在扰动后的结论中完整保留。

此文件属于真实逐词供应，而非 whole-atom factorization；没有对 W 或 fresh-row 来源给出虚假结论。它只新增必要的 routing/scale/接口推导，不复制既有 allocator 或 tail/small-factor 证明。

## 4. 可立即复用的真实旧消费者

下列源码均已定点阅读实际类型。旧 source pin 主要为 `UyNewNas/goldbach-formalization@298670f119d24874b719facb3ef756f1e01223a1`；具体 blob 见本轮 `SOURCE_SELECTION.json`。下表的“存在”指真实算法/定理源码存在，不给它们新增本轮编译信用。

| 已有接口 | 真正供应 | 当前实际接线缺项 |
| --- | --- | --- |
| `actualDwell_selected_prefix_budget` / `actualDwell_selected_prefix_allocate` | 原 initial prefix 的完整 remainder budget；C≥1 时原 deterministic two-capacity allocation | root V 新候选已供应 prefix、full 与临界 interval；实际 medium A、whole-box端点仍需接入。 |
| `actualDwell_full_vector_repair` | C<1 时重新消费原 full word，返回真实两因子，第三因子可为 1 | 从实际 medium A 范围导出 `1≤D/A`；不能把原 selected product 强行留作第二因子。 |
| `selectedPair_monomials` | 任意实际正 a,b,c 的三项 logarithmic monomial 代数 | 需要实际容量和选定 interval；`.599` 总 carrier bound 不供应它们。 |
| `actualFrozenCapacityFactors_on_box` / `actualFrozenCapacityAssignment_sum_partition` | 端点一次计算的固定 slot assignment；整 box 不拆成 tuple-specific 选择 | literal U5 原 source 的共同 box、固定上下端点与全部 endpoint squares。 |
| `actualDwellSupport_upper_inflation` / `physical_support_upper_local` | 原 full squares 的 exact local rescale 与 `(J+1)τ` endpoint 支付 | 先固定 rough rank J、原 endpoint block 和真实 reserve；selected/complement reserve也须保留。 |
| `actualExtendedThirdSelectedPair_frozenUpperTargets` | 旧 compact-upper policy 的实际 winner 6/7、整个 box 的 endpoint 与三项 bounds | source/policy 是 compact upper，不能直接声称是 lower U5 的任意 rank3/4/5 SourceForm。应复用内部通用数学并接原来源。 |
| `actualPrimeTuple_threeGroup_sum_normalized` / `actualFrozenSelectedPair_signed_regroup` | exact signed scalar 和三组卷积等式；完整 occurrence/multiplicity 保留 | literal U5 rho 到有限原 labelled boxes 的 exact 分解、原 marked/residual factorial scalar。 |
| `actualPrimeSlotBox_normalized_abs_le_one` | prime-slot box（含重复 interval 标签）的 normalized one-bound | 原 rho atom 的 labels、factorial 分母及三个实际 group 的关联尚须给出。 |
| `P5CausalRhoFactorization.pair_product_injOn` / `rho_at_pair` / `rho_eq_fibre_convolution` / `coefficient_abs_le_one` | 同 signed small/rough factor identity、唯一分解与原 pair coefficient one-bound | 不自动等于已归一化 group-three 卷积的 one-bound；应将原 sign-selected beta 与实际 group 接上。 |

已知 W 供应也确实存在，不能列成算法尚未写：

- `Part3ActualWThreeCapacityRun`，blob `bfaeb3f36f9f8a19c9e477291eb0fbc224d6ad4c`，有真实 `run`、`run_spec`、overflow original-square 与 `actual_W_gap_run`。
- `Part3ActualWResidualCompletion`，blob `aa8dea2c32fc30fa8228279b546a5b139a4c5406`，有 `finish_correct`、`actual_overflow_completion`、`complete_correct` 和 actual compact-frontier consumer。
- `Part3ActualCompactAllRankSupport`，blob `653709d962f8d9fca1889bbb6d11d48edf86a0f9`，已有真实 upper frontier 的 all-rank full support。

它们不是空泛假设壳。所缺是 literal lower U5 原 W 路由在同一局部尺度和整 box 上的 initial-capacity/third-slot/reserve 绑定，以及同 rho atom instance。尤其 nominal W 达到最大值并不自行提供一个已固定的 whole-box positive winner gap；手稿通过 coarse A/W 分流与 cover choice 付这个条件。

## 5. 最早未供应命题与后续顺序

在新 root-V 逐词候选之后，最近的未供应命题是：

> 从原有限 U5 policy 的一个实际 coarse root-V box（及其 descendant query）内部导出同一个固定 V route/initial prefix、同一个局部 cover 和端点向量，使该 box 内全部原 tuples 的 full/selected upper-endpoint squares 与 perturbed critical interval 同时成立；随后原 endpoint allocator 的 slot partition 对整个 atom 固定，并保持原系数及外标。

当前缺少这个实际 coarse box → route/reserve/endpoint 数据供应；不是缺 two-capacity greedy 或其 overflow 证明。若先完成数值 C≥1/C<1 的点态组合，也必须明确它仍未建立这条 whole-atom 命题。

之后同样需要 fresh-row SourceForm 的实际 critical interval/local-rescaling 接线，以及 W whole-box初始许可。再用已有 normalized regroup 得到原 signed rho 的 exact finite atom identity，保留外部 scalar `epsilon M1 M2 M3 / M_res`，将 small beta 按原 sign 附到 group three，并支付 global-squarefree analytic collision。

**rough rank 与完整 canonical word 必须分开。** small beta 的 prime word 可含没有固定正指数下界的小素数；不能对完整 signed word直接套 `actualRoughPrimeVector_length_le` 得到固定 J。已有候选保留了 `s` 与原 rough list，故可继续按手稿路线处理，无须推翻或重做其完整词平方结论。

common physical Q 的 first missing supplier 是有限家族层面的：一个在 N 增长之前固定的非负 marked prime-box family，具有共同原 physical `Q=N^lambda`、固定正 `L`/marked cutoff、`alpha≥2`、实际 (F) 分支和小追加稳定阈值 `chi`。`sv:finite-feedback` 还要求 `chi` 不超过最小已指定 exponent（未指定第三槽时也不超过其 cap），以及原 physical cutoff `N^(L/s)<N^chi`。`P5OriginalU5NativeRootCover.levels N` 的 exact per-N level regrouping 不能单独充当这种固定有限家族。

`.599` 仍只作 complete-carrier envelope，并在 `coef:parameter-order` 的 `theta_star/(1−kappa0)<3/5` 支付中使用；它不替换 `theta_cov`、原 common Q 或该 family 的 lambda。

## 6. 分类与已验收工作

上述问题应分类为**原稿内部的具体供应/适配尚缺**。本审查没有证明手稿数学不可能，也没有因点态源码缺失宣称实质数学反例。两套 S 已供应与 root F 子集仍待识别完全相容；本轮新 root-V 候选已实际填入后一项的一部分。

P3.5 的 whole-height 数学不属于剩余清单。已读取 `5285d4f5d8c40eddf92c108b492c909de8b43cef` 中的原 receipt：数学源码 `94cff537f2e60173aaf936c2345d5af0ee5e6585` 的 `RegularCumulativeShellPayment`、`RegularPositiveMeasureExhaustion`、`ContinuousTraceExhaustion` 共 81 owned declarations 已经 strict/kernel/types/传递公理验收。receipt 仍将实际 row adapter 标为 source-only、P3.5 未整体关闭。应复用这份信用，后续只接实际 row/physical-family estimate，不重建 whole-height 桥。

本轮 all-source/signed 及 root-V 新候选尚未获得该类验收；源码审查、hash 和无 placeholder 检查都不算编译或 kernel 通过。
