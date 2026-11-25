# 原 U5 coarse root-V：可实现的辅助 cover 与最早 physical-Q 缺项

2026-11-25。只读构造检查，当前 HEAD `f51893bfc54e056786617f033759087fc63633a9`。本记录不写 Lean、不改主源或 manifest、不编译、不提交，也不重做 RootV 的逐词证明。

## 1. 直接结论

**可以小步构造一个在 N 前固定的 coarse V route 和辅助 covering exponent，并消费现有 endpoint allocator，同时保持当前 native rho 原样。此构造不自动给出共同 physical Q。** 当前最早的系数运输缺项是：尚未把字面 U5 原 rho 的 decision-filtered fibres 识别成满足 whole-atom tensor/admission 条件的固定有限族。与 coarse 常量 seed 的 predicate/rho 同一性或已支付误差的比较，是一种充分实现路线，不能误写成手稿的必要假设。

这不是把已写 RootV 改成 (F) 假设。下面的 route、reserve 和上端点平方均应作为具体定义的输出。

## 2. 能保持原 rho 的最窄具体小步

先固定原 `R, bank, buffer=b>0, epsilon`，再在 N 前选择 pair mesh 宽度 `delta≤b/32`。可以复用 `P2PhysicalIncomingPrefixCells.exponentCode_membership` 的半开 grid，以两坐标 label 构造有限集；`PairSourceReceiver.qPoint/qLo/qHi` 已给同一有理 mesh。只保留其 closed box 与原 triangle 有交的 labels，代表点从这个纯几何交集中选定，不能从某个 N 的实际 prime pair 反向选择。

这里无需另建泛化 box 体系：取一个仅供辅助分类的 `m_aux`，直接使用已有 `codeAt R m_aux 2 [t,u]` 的 rank-two code（五槽中的后三槽仍是原 padding），其 first-two `qLo/qHi` 和现有 `box R code` 给 closed hull。原 bank 的 mesh 及 `pairPlan` 不作更换。`tendsto_logPrimeMeshStep` 在 N 前选择 `m_aux` 使 `(ceiling−R.epsilon)/(m_aux+1)≤b/32`。所有实际 U5 外标都在 `R.epsilon≤u<t<h<ceiling` 内，故两有效坐标不会落到 `none` 的 top singleton；`exponentCode_membership` 和 `exponentCell_unique` 给实际归属与唯一性。

有限 label 集可取现有 `Code m_aux` 全集上“其 rank-two geometric cell 与原 triangle 非空”的 filter。这个 predicate 只量化实坐标，不出现 N 或任何 prime。每个保留 label 的代表点由其非空 geometric intersection 固定选择，因而 `route_j,U_j,ell_j` 全部位于 `∀N` 之前。其后才用 N 的 actual coordinates 读取这个已固定 label。

对于一个固定 label j，设代表点为 `r_j=(u_j,t_j)`，原几何 level 为

`lambda0(u,t)=max(v(t),max(v(t+u),B(a)))`。

在代表点按原三个分支的最大值内部决定 singleton / pair / W，tie priority 可沿用原 RootV routing。不是要求调用者给 `hwin`。定义

\[
U_j=\lambda_0(r_j)+3\delta,\qquad
\ell_j=U_j-b/2.
\]

这里 `ell_j` 明确是 **辅助 cover**。原 `rootLevel false N t`、`rootSeed=rootLevel−2b`、`selectedPolicy`、rho 与 density 不作改写。

旧 `VariableEnvelopeRegularity.v_abs_sub_le_of_le` 给全局 Lipschitz 常数 3/2；根 max 的两个 V 输入分别变化至多 `delta`、`2delta`，而 B(a) 不变。于是对 box 内每个点 z，内部导出

\[
|\lambda_0(z)-\lambda_0(r_j)|\le3\delta,
\quad \lambda_0(z)-b\le\ell_j-b/2.
\]

若代表点的实际输出是 V 分支 i，则同一个 i 在整个 box 上合法（不必仍是每一点的最大值）：

\[
V_i(z)\ge\lambda_0(r_j)-3\delta,
\quad \ell_j+b/4\le V_i(z),
\]

因为 `6delta≤3b/16<b/4`。同时由原 triangle 的 level bounds 和 `b≤1/1000` 得 `1/2<ell_j<153/256`。这些是小量仿射/Lipschitz 推导，未要求 route、winner gap 或 reserve 作入口。

### 建议 theorem statement 的实际量词

这是拟议的具体命题，不是已声明的 Lean 定理：

> 对固定的原 scalar allocations，存在 N 之前固定的有限 pair labels、half-open cells、代表点、`route_j`、`U_j`、`ell_j` 及正 fine mesh；对每个 N、原 pair t、同非零 native rho 的实际 witness，若 pair 在 cell j 且返回的实际 last source 为 root，则内部返回 W outcome，或返回同一个 `route_j` 的 initial prefix、统一 `ell_j`、整 box 的 V reserve；每个相应 rough fine atom 的 upper vector具有 full 和该 prefix-complement D-well，并由旧 frozen allocator 得到对整 box 固定的 slot lists。原 rho 和其外标在所有结论中保持字面一致。

`source=.root` 仍是实际 witness 的分支限制。不得将其写成整个 family 的 (F)。代表点输出 W 时保持该分支待供应；不假装已经完成 W 初始化。

### 真实输入来源与 endpoint 支付

1. 原 pair 坐标 membership 由 `coordinates_mem_triangle` 提供；其 fixed grid label 由 `exponentCode_membership` 计算。
2. 同 native rho 的原 witnesses、真实 root source、rough/full squares 用已写 all-source/signed；不再次假定 `hfull`。
3. 固定 rough lower exponent `attachmentNu*epsilon^2>0` 来自原 rough universe，旧 `actualRoughPrimeVector_length_le` 给 N 无关的 J。small beta 继续保留为单独因子，不纳入这个 rough J。
4. 在每个长度至多 J 的 fine labelled box 上固定 upper vector。选 mesh 使 `(J+1)tau≤b/4`，旧 `actualDwellSupport_upper_inflation` 把原点 full squares 推到 upper vector；initial-prefix 的 complement 直接用旧 `actualDwell_selected_prefix_budget`。
5. 换底与 residue 扰动应继续从尚余的 scalar reserve 支付，复用 RootV 的 `v_rescale_lower`、旧 `physical_power_eq_local`、`actualSelectedSubproductV_residue_margin` 和 `critical_iff`。不要把 fixed auxiliary `ell_j` 误写为新的 physical seed。
6. `actualFrozenCapacityFactors_on_box` / `actualFrozenCapacityAssignment_sum_partition` 已经给 endpoint-only assignment；selected-prefix C≥1 和 full-vector C<1 使用既有 allocator。这里不需要新的 greedy 程序。

fine prime intervals 也直接复用同一 mesh。上端点可定义为 `floor(N^hi)`；实际 prime 的 cell membership 给 `p≤floor(N^hi)≤N^tau*p`，从而匹配既有 `hsize` 字段，而不是由调用者给任意 inflated upper vector。fixed J 的 slots 是 `[t.2,t.1]++chosen`，没有加入 `s.primeFactorsList`。

### small beta 保持第三组的准确承接接口

先对 rough slots 使用 `actualPrimeTuple_threeGroup_sum_normalized` / `actualFrozenSelectedPair_signed_regroup` 和 `actualPrimeSlotBox_normalized_abs_le_one`。在一个已经拥有固定原 signed scalar 的 atom 上，令 `beta_sigma` 为该原 sign 选中的 `actualSmallRosserMinus` 或 `actualSmallRosserPlus`，第三组取 `gamma3_star=smallRoughRho small rough3 gamma3 beta_sigma beta_sigma`。两个 beta 参数取同一真实 `beta_sigma`，所以 generic sign attachment 不会重新决定原 atom 的 sign；外部 signed scalar 原样保留。

- `smallRoughRho_mul`：严格 small / inclusive rough 分离后，`gamma3_star(s*r3)=gamma3(r3)*beta_sigma(s)`，无额外 fibre multiplicity。
- `sum_smallRoughRho_mul`：对任意实际 test F 的精确有限 reindexing，可与三组 normalized identity 组合，不需要展开 small 的 prime word。
- `abs_smallRoughRho_mul_le_one`：直接消费 group3 one-bound 与真实 beta one-bound，给附着后 one-bound；support 外用 `smallRoughRho_eq_zero_of_not_mem`。
- `actualSmallRosserSupport_smallPrimeSupportedAt`、`actualSmallRosserMinus_abs_le_one`、`actualSmallRosserPlus_abs_le_one`、两种 `_active`：供应 small universe、norm 和 `s<L`。第三 rough group 的分离字段由原 rough-labelled prime intervals及固定 slot partition的 subset/product 得到，不能只把整个原 rough coefficient 的 norm换个名字。
- `P5CausalRhoFactorization.rho_at_pair` / `signed_physical_sum_fubini`：保持原 native rho与实际 small/rough witness的精确入口。

这些旧接口已给 algebra/one-bound，但还缺 literal U5 原 atom 的固定 sign/scalar 与 group3 的实际归属接线。**small support 的 size 支付也不能省略：**当前 `halloc` 只给 `ell_beta=attachmentNu*epsilon≤b`；手稿 group3 attachment 的三项成本为 `2ell_beta,2ell_beta,(39/16)ell_beta`，相对于 ζ reserves。`ζ≤b/8` 与 `ell_beta≤b` 并不自动支付这些成本。可按稿件参数顺序选择更小 beta（同时满足原 `R.epsilon≤attachmentNu*epsilon^2`），或另证现有 b surplus 如何支付同样成本；不能把已写 all-signed squares 当成这条 monomial size 支付。

一个 nonempty fine atom 的真实 accepted tuple 可以用于**证明其已定义 upper vector**满足平方条件；upper vector 与 partition 本身仍只由固定 labels、N 和 medium length 决定。这并不证明该 atom 上原 coefficient 的 policy indicator 已经恒定，也不把受原 policy 过滤的子集变成 Cartesian prime box。

因此建议第一实现边界只到固定辅助 cover、实际 upper-vector支持与现有 fixed assignment，独立说明剩余 coefficient-identity 义务。若以完整 whole-atom normalized tensor / common physical Q 为验收目标，还不能开始声称已供应。

## 3. 为什么不能直接冻结当前 physical root

`P5OriginalU5NativeRootCover.native_policy_at` 的精确输入是 `t∈marks N v`，即真实 `rootLevel false N t=v`。它随后才得到 `selectedPolicy=policyAt v`。`levels N=(pairSupport N).image(rootLevel false N)` 是 per-N 有限 regrouping，既没有固定 label 数，也没有 N 之前共同 level 列表。

当前 `pairPlan` 直接把 pair-dependent seed 传给 `cap3/cap4/cap5`。`freshCheck` 比较 `parent<rowCap`，rank4 的 `arrivalGate` 还把实际 incoming parent放在 cube inequality 右边；原 `admission` 同样读取当前 cap。故换掉 seed 不仅是改一个报告字段，还可能改变 retained word、fresh/inherit 决定及原 rho。

几何上 root level 在一个合法 V box 内也通常不恒定。例如

`119/1000≤u≤121/1000`、`139/1000≤t≤141/1000`

是原 triangle 内一个小 box；它始终由 `v(t)=(1+t)/2` 胜出，level 从 `1139/2000` 变化到 `1141/2000`。这是 level 非恒定的几何见证，不假称已构造某一 N 的整数反例。选择一个共同上界只证明 support cover，不证明 coefficient/density 的 physical-Q 同一性。

### 现有 coarse 接口的精确边界

- `ActualExtendedThirdWholeCellActions`：真实 representative action、whole closed cell、统一余量，说明这种几何方法已有可复用原型。它的参数和 winner为 compact upper 的 rank3 来源，不能当作当前 lower U5 instance。
- `ActualExtendedThirdCompactUpperPolicy_on_cell`：确实给出常量 physical level的 policy equality；但其 `CompactRawLevel` 从定义起就读取固定 cell level，而当前 U5 root 定义不是这样。两者之间尚无原 U5 policy等式。
- `CurrentP5CausalCommonReceiverPartition`：精确保留原 receiver与十一项 signed ledger 的共同 finite label refinement；其文件明确不声称 fibres 是 prime tuple Cartesian boxes，不供应 Q/admissibility。
- `P2OriginalLowerAffineTieSelector`：已区分 identical inherit chambers 与 proper affine tie walls；未移除任何实际 arithmetic prime sum 的边界。不能把 closed tie-set 事实当作原 rho 冻结误差已支付。
- `ActualExtendedThirdCompactKernelApproximation`：旧 upper coarse scalar/kernel approximation；其文档和结论仍把 same-policy arithmetic count 单列。它不是当前 U5 rho transport。
- `BoundaryLogMesh` / `CurvedDiscrepancyReduction`：已存在特定 complete-product boundary 的算术预算，但当前 U5全部 seed/admission/fresh-check walls 的原系数差尚未识别为它们的输入。

## 4. common-Q 的原量词与最早真正未供应的命题

需要分清两个消费端。`coef:prime-product-insertion` 的量词是：本 appendix 构造的有限 upper/lower/marked coefficient families，固定 family 上所有充分大偶数 N；count 与 exact coprime mean 的系数相同。其证明消费 whole-atom tensor identity、one-bound、size/SW和统一误差，没有把“policy 点态等同 constant seed”写作独立必要条件。

`sv:finite-feedback` 则以非负有限 marked family `sigma(B)` 与共同 `Q=N^lambda` 为状态；admitted enhanced family 是 finite nonnegative combination of labelled prime-box indicators，具有固定正 marked exponents、L、enhanced lambda margins、full/selected squares、一个 factorization branch及稳定阈值 chi。children保持总 Q，并用这个 Q 的 `L=lambda−log_N B` 和 `alpha=(1−log_N B)/L`。这同样不明文要求原 policy 必须 pointwise 等同某个 constant-seed 程序。

所以 **constant-seed equality 是充分路线，不是已证必要条件**。若能直接对同一原 rho 给出上述 whole-atom/marked-family 数据与 exact count/mean/child identities，就可以不走这条 equality。可是单有 exact finite indicator regrouping 加共同 modulus 上界仍不足：它只保证有限 Fubini，不保证 decision fibres 为 Cartesian boxes、固定 scalar 与分离卷积，也不保证共同 Q 所定义的 residual、density、cutoff 与 child laws均接上。

当前应记录的 first unsupplied proposition 是：

> 对 N 之前固定的原 code/fine-interval labels，将 literal U5 原 rho（包括原 policy indicator）识别为固定有限的 admissible whole-atom coefficient family，内部给出 exact signed tensor/scalar、共同层的支持/size与实际 small attachment；若消费 finite feedback，还须给出同一 marked family 在所选 physical Q 上的原 count/density/child identities。不能以这些 family/admission 结论为假设。

一条可能的充分实现路线是：

> 在 N 之前固定的 whole-word atoms 上，从实际原 U5 测试与这些 atoms 的几何条件内部证明原 variable-seed predicate 与指定 constant-level predicate在所有相关 prefixes 上一致，从而通过已有 first-exit/attachment字典得到同 rho、同 density；其余原 atoms 若被裁去，必须保留 exact 原 rho remainder，并用实际 signed/moment boundary预算证明其损失。

或者证明更一般的 actual-family 接收定理：原 variable-seed coefficient无需替换即可属于共同 physical Q 的 admitted family，且 coefficient、density、child feedback all保持原义。当前已读接口也未给出这项。

仅写 `rho_original=rho_frozen+error` 的定义恒等式不能供应所需预算。只说 seed变化很小也不够：决定改变集中在哪些实际 tests/walls、sign和first-exit关系如何保持、以及它们的 arithmetic/mean costs 均须具体证明。

这定位为**稿内实际策略／系数适配缺项**，不是已发现的数学不可能，也不是对 alternative direct-admission 路线的否定。辅助-cover 小步可绕开 seed 改写而推进 allocator 支持；它无法偷偷关闭 physical-family admission。

## 5. 固定手稿出处

只使用 `UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`。

- [coefficient-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/coefficient-appendix.tex)，blob `10f3e2efb2074a9b97148a5151956e1d450be13f`：physical lambda / auxiliary ell 段明确禁止 obtaining cover 时改 coefficient/density 的 lambda；紧接的 coarse A/W 段从 `Gamma=inf max(A,W)` **定义** `lambda=Gamma−2e`，不是宣称它等于逐点 max 的原 seed。Finite approximation 段要求 ancestor decision先冻结，再细分children；Three-factor representations 段要求算法只读 whole-atom endpoints；`coef:tensor-identity` 要 exact 原 signed scalar/multiplicity。
- [sieve-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex)，`sv:finite-feedback` / `sv:child-state`：N 前固定正 marked family、共同 physical Q、原 residual L与alpha、保持 Q的children。它不能由 per-N levels regrouping 或辅助 support envelope替代。

本记录没有新增形式信用，也没有重新列已验收 whole-height 数学为缺项。
