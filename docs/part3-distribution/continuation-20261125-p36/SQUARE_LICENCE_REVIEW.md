# 实际 U5 平方许可与 0.599 载体上界：限定独立审查

日期：2026-11-25。源码基点：`edc2e68c360bf66bd33e4a3a5211cafd6d95f218`。

本审查只核对原 U5 selected policy 的平方条件、现有三因子供应接口，以及共同物理等级与载体上界的区别。没有修改 cap 源码，没有运行编译，也没有重新审计已确认的 cap 证明。下文是精确类型与手稿推导审查，不是新的 Lean 验收。

## 结论

现有源码已经写出实际 root、选中第五前缀、第五级之后接受尾部、以及符号敏感小 Rosser 附着的多段平方供应。不能将这些工作统称为“尚未证明平方条件”。但指定的两个文件并未提供一个从任意实际非零 U5 rho 直接推出完整 (S)/(F) 许可的定理：原 root 的选中补集是空列表；通用 integer 前缀供应使用普通 `CompactStart` receiver；实际 `PairRange` 的第五级供应仍需命中真实 fresh source，并接上同一 mask/cap。继承分支、较短词及完整 bank adoption 的统一连接仍未由这些类型给出。

`theta_* = 599/1000` 可以作为同一 rho 的共同 **complete carrier envelope**，保持实际 policy、root 和 density 不变。这正是本轮 cap 的用途。它不能替换三因子分解的 `theta_cov`，也不能把原 marked family 的物理 `Q` 改名为 `N^theta_*`。前者有下面的严格数值障碍，后者会改变原 residual 和 density 的参数。

## 固定手稿依据

全部引用固定在 `UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`：

- [coefficient-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/coefficient-appendix.tex)：`coef:full-squares`、`coef:selected-squares`；“Finite approximation and strict margins”；“Three-factor representations”；`coef:three-monomials`、`coef:tensor-identity`、`coef:collision`、`coef:parameter-order`、`coef:complete-scales`。
- [argument.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/argument.tex)：开头 admitted policy / marked family 定义、`eq:current-medium-ranges`、`eq:current-PP`。admitted coefficient 包含 Appendix 的实际三因子表示，只有模数范围不够。
- [sieve-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex)：`sv:finite-feedback`、`sv:child-state`。共同物理 `Q=N^lambda` 固定，`L=lambda-log_N B`、`alpha=(1-log_N B)/L` 与原 prime ceiling 一起保留。

以下 (S)/(F) 指上述平方支持／因子分解条件，使用当前 1106 文件的实际 labels，未把旧文稿的字母编号当成新的定理。

## 现有平方供应究竟给到哪里

| 现有 lemma | 已有实际输出 | 当前类型的边界 |
| --- | --- | --- |
| `P2OriginalPairBufferedRootProvenance.fifth_selector_root_gates` | 原 `pairSupport N` 上，`[(t.2,true),(t.1,true)]` 在字面 `rootSeed false buffer N t` 的 full / selected-complement integer gates | 只有两个外标；两项全为 selected，所以 complement 列表为空。不是任意后续 mask 或整个 retained word 的许可。 |
| `fifth_buffered_root_squares` | 原 triangle 推出 root 两个 square 和 `t.2+t.1+2*a < seed` 的第一个 rough head reserve | 未组装后续实际 run 的所有源选择。 |
| `P2OriginalSelectedIntegerPrefixSquares.physical_slots_to_integer`、`integerSquareGates_at` | 同一 tagged word 的实数 square 精确转 integer prefix square，selected product 保留在 complement 的初始乘子中 | 它们消费已有 full / selected square，不自行产生 policy 的分支许可。 |
| `selected_source_integer_squares` | 选中的 SourceForm 自有 mask、buffered cap，以及 full rank 3/4/5 的 integer gates | 参数是普通 `CompactStart S`、`select S`、`actualCode S`、`startCutoff S.start`；不是字面 U5 `PairRange R` receiver。即使 U5 外标落在 h 以下，也不能把两个不同 mesh/selector 当作同一个。 |
| `P2OriginalPairSourceReceiver.selected_fifth_point_squares` | 实际 `PairRange` 的选中第五前缀，在该 `branch.form.supportMask` 与 `rowCap` 下的两套实数 gates | 需要实际 `hx` 与 `hsel`；结论只覆盖第五前缀，不含后续词。 |
| `pair_run_three_cap`、`actual_fifth_source_cap` | 字面 pair-root run 的第五 frozen cap；后者由 `hsel` 与 `freshCheck` 得到确切 `rowCap` 身份 | 不能从“run 接受”单独推出 fresh：接受测试和 cap 选择是不同步骤。继承／fresh-check 失败分支仍须保持各自来源。 |
| `P2OriginalPostFifthRoughSquares.pair_atom_fifth_split` | 实际 rough-support atom 的 chosen word、真实 H5 与接受 suffix；第五级后 cap 不变 | 长词条件是 `3 <= chosen.length`，短词明确留在另一分支。 |
| `actual_postfive_tagged_squares`、`actual_postfive_integer_gates` | 从同一 H5 的两套旧 gates 与接受／递减 suffix 推出任意长度尾部的两套 gates；新增 slots 都 unselected | **这段 all-rank 尾部供应已经写出，应直接复用。** 尚须给出 H5 的原 mask、`hword`、`hfull`、`hselected`。 |
| `P2OriginalSelectedNativeSmallExtension.active_pair_small_word_well`、`actual_signed_small_extension` | 原非零 sign-attached `(s,r)` 的 canonical small word、完整 full / selected gates、原 selected labels 与原 rho 身份 | 需 `w^2 <= L`、原 rough word 的 gates、排序／cutoff，以及 `(B*r)*L <= N^cap`。不能只用最终 `(B*r)*s < N^cap` 代替这个更强预算。 |

`P2OriginalSelectedFifthRoughBudget.selected_fifth_actual_rough_budget` 已将多段供应组合起来，但仍是普通 `CompactStart` 版本，明确以 `hcap : H.cap = scalarCap ...` 为输入。Pair receiver 的 `actual_fifth_source_cap` 已经解决 fresh 第五分支的对应身份，故不应重新证明整段 post-five induction；所需的是使用相同 receiver、真实选择结果和 mask 的连接。

### 能立即复用的具体字段与仍缺字段

1. **小因子字段可以复用。** `original_U5_small_head` 给真实 `w^2 <= L`；原 active-pair factorization 给同一非零 `(s,r)`。本轮的 accepted-word rough bound 与既有 small-level allocation 能支付在全局 carrier cover 下的 `(B*r)*L` 预算。`actual_signed_small_extension` 的其余输入是完整 rough word 的两套 gates及原 mask；该预算本身不补出这些输入。
2. **fresh 第五分支已有直接路线。** 对真实 H5，可组合 `selected_fifth_point_squares`、`actual_fifth_source_cap`、`actual_postfive_tagged_squares` / `actual_postfive_integer_gates`、`physical_slots_to_integer`。还需具体供应 `hx`、同一 `hsel`、`freshCheck` 以及 slots 与 H5.word 的身份。现有 cap 的类型没有这些字段。对于 `hx`，原外标由 triangle 与 `R.epsilon<a` 给范围；粗素数下端还需与 R 的网格下端连接，例如 `R.epsilon <= attachmentNu*epsilon^2` 是一种充分安排，或另证实际 code 的上端控制。不能默认已有这项连接。
3. **全部 U5 尚未统一。** 需要覆盖 rough rank 0/1/2、rank 3/4 的 fresh/inherited 历史、以及第五级继承情形，追踪最后一个真实来源的 cap 和 mask。`codeAt` 使用 `marked word`，其布尔位全 false；分解选中集合来自 SourceForm，不能直接把 root 的两个 true tags 填入任意后续分支结论。必须明确后续 (F) 所采用的 I，并保持与其平方结论一致；这不是认定两种“标记”必须相同。
4. **平方 gates 之外仍有分解输入。** `sourceCheck` 保留 full / selected endpoint squares、tent side 和结构 eligibility，但不包含局部 rescaling 后的 `v0 <= b_I <= u0`、所有严格 reserves、whole-atom 固定分组或同 rho 的系数重建。`formRankEligible` 明确不许可 `wSlot` fresh 候选；root 本身的 max 公式仍含 W。完整 adopted bank／W 分支的实际许可不能从当前 tent checker 推出。

## 为什么 0.599 只能作载体上界

### 三个不同量

手稿区分：物理 `lambda` 决定实际 coefficient、density、`Q/B`；较大的辅助 `ell` 用于平方覆盖；局部 base-x 分解使用

\[
q_0=\log_xN,\qquad \alpha_0\ge q_0,\qquad
\theta_{\rm cov}=q_0\ell+2\zeta.
\]

完整 carrier 在 beta、端点和尺度处理后可以安全地由 `theta_*=599/1000` 统一控制。手稿在 `coef:parameter-order` 后确实使用这个数，并要求 `theta_* /(1-kappa_0)<3/5`。这不是将每个 atom 的 `theta_cov` 设为 `theta_*` 的许可。

### selected-subset 分支的必要不等式

“Three-factor representations” 的具体分支要求

\[
v_0=2\theta_{\rm cov}-1\le b_I\le u_0,
\qquad
u_0\le\frac{2-2\theta_{\rm cov}-(7/32)\alpha_0}{3}.
\]

所以该分支的一个必要条件是

\[
8\theta_{\rm cov}\le5-\frac7{32}\alpha_0.
\tag{*}
\]

若强行设 `theta_cov=599/1000`，则 (*) 强制

\[
\alpha_0\le\frac{832}{875}.
\]

这是精确的条件式障碍，不是声称对任意没有尺度限制的 x 都矛盾。

**手稿实际量词分两处处理：**

- “Finite approximation and strict margins” 固定有限 policy 和紧致片的正 reserves 后，明确选择某个 `kappa_*>0`，保持 `log_x N in [1,1+kappa_*]` 内的 admissibility。在这个明确范围内，`q0>=1`，再用分解节的 `alpha0>=q0`，(*) 给 `theta_cov<=153/256<599/1000`。在边界 `alpha0=1`，更直接有 `v0=99/500`，而 `u0<=2333/12000`；两者间隙为 `43/12000>0`。
- `coef:complete-scales` 的一般局部尺度是 `c*N^(1-kappa0)<=x<=C*N`，还给 `c0*x<=N<=x^(1+kappa)`。**这本身不保证 `q0>=1`**：x 可以略大于 N。若取固定 `C>=1`，N、x>1，则 `q0>=log N/(log N+log C)`。对所有满足 `43*log N>832*log C` 的足够大 N，这一下界严格大于 `832/875`；由 `alpha0>=q0` 同样排除 `theta_cov=.599`。这里仅使用固定 complete-scale 常数与原最终量词，不使用“约等于 1”作为证明。

因此，将 .599 用作 support cutoff 没有发现冲突；把它代入当前 selected-subset 分解公式则在上述实际范围不成立。这一判断只针对被检查的分解条件，不声称排除了所有可能的其他分解算法。W 初始化还有独立的第三-slot／容量要求，当前 cap 同样没有供应它。

### 不能把 physical common Q 同步提高

`sv:finite-feedback` 的 Q 是实际固定总等级。把它改成 `N^.599` 会改变 `L=lambda-log_N B`、`alpha`、后续 residual 和归一化主项。保持原 policy/density 的正确做法是另记 `D_*=N^.599` 作为算术求和的公共载体边界，同时保留每个原 physical Q 和其局部 ell/theta_cov。这样不会自动把逐 N 的 root-level 分组变成 N 之前固定的有限 common-Q 查询族。

## 与已有 (F) 工具的最小连接结论

`ActualFrozenSelectedPairSlots.actualSelectedPairFactors_targets_of_fullSupport` 可复用其既有数值分解，但它仍明确需要 `hfull`、`hgate`、`hblower`、`hbupper`、A 的区间，以及对应的三-slot selected-pair 形状。其 `hblower/hbupper` 正包含上述不能用 .599 自动满足的选中子乘积范围。更专门的 `actualExtendedThirdSelectedPair_frozenUpperTargets` 使用既定第三层 cell/winner 条件，不能直接替代全部 U5 的 source bank。

`ActualFrozenSlotCoefficientRegrouping.actualFrozenSelectedPair_signed_regroup`、`actualFrozenSelectedPair_group_support`、`actualPrimeSlotBox_normalized_abs_le_one` 已经提供 whole-box 固定分组、原 signed scalar 及 group one-bound 的有限恒等式，应复用。但仍须把实际 U5 first-exit / signed small attachment 的完整 coefficient 精确分解成这些 whole boxes，并提供原 multiplicity、squarefree 和 uniform scalar budget；仅有逐 tuple 的因子存在或 q 上界不能代替这项连接。

### 对三个指定历史源码的补充核对

仅定点读取 donor `298670f119d24874b719facb3ef756f1e01223a1` 的下列接口，未导入、恢复或编译两个 W 文件。三个 blob 身份均已确认；其中 AllRankSupport 当前本地文件的 `git hash-object` 也与指定 blob 相同。

| 原有源码与固定 blob | 实际已经完成的供应 | 对本轮 U5 的准确边界 |
| --- | --- | --- |
| [Part3ActualCompactAllRankSupport](https://github.com/UyNewNas/goldbach-formalization/blob/298670f119d24874b719facb3ef756f1e01223a1/ImbalancedChen/Part3ActualCompactAllRankSupport.lean)，`653709d962f8d9fca1889bbb6d11d48edf86a0f9` | `actual_compact_frontier_all_rank_support` 从实际 `firstExitDepthFrontier` 的 `hstate`、owned cell 得到同一 `state.selectedPrefix.reverse` 的 `actualDwellSupport`，包括 k>=3 的偶／奇 rank。`actual_compact_frontier_upper_local` 进一步支付端点膨胀，预算字段精确为 `q0*actualExtendedThirdPhysicalLevel + tau*(k+1) <= theta`。 | 这是实际 generator 的供应，不是以最终 support 为假设的壳。但 policy 是 `actualExtendedThirdCompactUpperPolicy`，属于 upper 第三层 cell；不是 U5 的 `selectedPolicy ... false N t`、pair-root lower continuation。它不声明完整 U5 rho 的 selected-complement gates或系数重建。 |
| [Part3ActualWThreeCapacityRun](https://github.com/UyNewNas/goldbach-formalization/blob/298670f119d24874b719facb3ef756f1e01223a1/ImbalancedChen/Part3ActualWThreeCapacityRun.lean)，`bfaeb3f36f9f8a19c9e477291eb0fbc224d6ad4c` | `run_spec` 真正实现按原 occurrence 顺序分配和首个 overflow；`run_overflow_original_square` 从原 full-list square 提取停止点；`actual_W_gap_run` 用实际第三层 least winner=4、W gap 初始化原前两槽，再产生成功／overflow 两种结果。 | W 分配程序和实际 row-4 初始化已经写出，不应重复。它尚未把 U5 的 root W 分支或后续 bank identity 接成该 third-cell/winner/gap 实例；没有完整 signed rho 或 whole-box tensor 身份作为输出。 |
| [Part3ActualWResidualCompletion](https://github.com/UyNewNas/goldbach-formalization/blob/298670f119d24874b719facb3ef756f1e01223a1/ImbalancedChen/Part3ActualWResidualCompletion.lean)，`aa8dea2c32fc30fa8228279b546a5b139a4c5406` | `actual_overflow_completion` 和 `complete_correct` 从原 full squares 证明剩余两箱确实无失败，并保持全部 product。特别是 `actual_frontier_W_gap_complete` 直接从上述实际 upper frontier 内部调用 AllRankSupport，产出同一 rough-prime product 的完整分配及容量二分；不是仅泛用条件壳。 | 该实际调用仍是 `actualExtendedThirdCompactUpperPolicy` 的 W-gap frontier，要求原 owned cell、winner=4、gap、shape、A 区间。输出是自然粗素数 occurrence 的 trace、乘积和容量界；没有 U5 非零 rho、实际 small attachment、整个 atom 固定端点分组、符号／重数重建或三条全部 analytic monomial 结论。 |

因此，“W 算法和尾部完成尚未写出”是不准确的。已存在真实 upper 源的中间 (S)/(F) 供应，今后应复用其算法和证明。本轮欠缺的是把**这一个 U5 同 rho** 的原 root／分支接到相应已有输入，或在证明源不相同处给出真正适配，而不是把 upper policy 与 lower pair policy 直接等同。这个定点读取没有发现一个已能无新增实质字段直接消费本轮 cap、并返回全部 U5 同 rho 因子分解许可的定理。

**本轮 cap 现在能供应公共 carrier range，并帮助支付原 small-extension 的标量预算；它不能立即使任何所检查的完整 (S)/(F) consumer 的所有输入闭合。** 下一处实际缺项是同一 U5 receiver 全部分支的 mask/cap／endpoint-licence 连接和其 whole-coefficient 三因子表示。此处不新增泛用条件包装，不重做已有尾部平方归纳、small-sign 证明、tensor identity 或外部分析输入。
