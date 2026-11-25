# 原 U5 root 的实际 V 子集与局部 (F) 输入

状态：**source-only；未编译；未做 kernel replay 或公理验收。** 本目录不修改主 cap、已冻结 fresh/all-source 候选、SOURCE_SELECTION 或编译队列。

候选为 `ImbalancedChen/P3OriginalU5RootVInputs.lean`，公开命名空间 `ImbalancedChen.P3OriginalU5RootVInputs`。它接续本轮已冻结的 all-source/signed 候选，而不重做其任何 rank、tail 或 small-factor 归纳。

## 1. 所解决的具体接口

原 root 使用

\[
\lambda_0=\max\{v(t),v(t+u),B(a)\},\qquad a=417/5000.
\]

all-source 的 root S-mask 保留两个原外标。这个 S-mask 本身没有声称它们的乘积是 (F) 的临界区间子集。候选从同一个原 max 内部计算 `rootRoute`：优先选择达到最大值的 singleton `t.2`，其次选择达到最大值的 pair `[t.2,t.1]`，否则记录真实 W 值。tie priority 只在值相等的原分支间选择，不改变 rootLevel 或原 policy。

`root_route_sound` 证明该结果确为原 root 的分支值。公开消费定理不以 winner、不以最终临界区间、不以 selected squares 为前提。

## 2. 精确量词与结论

`native_U5_root_V_inputs` 的原算术入口与 all-signed 相同：原 `pairSupport N`、字面 `selectedPolicy R bank buffer false N t` 的非零原 native rho，以及同一 scalar precision/buffer 分配。为保留严格余量，本文件要求 `0 < buffer ≤ 1/1000`。

局部参数为

\[
1<x\le N\le x^{1+\kappa},\quad
0<\zeta\le b/8,\quad 0\le\kappa\le b/4,
\qquad b=\operatorname{cast}(buffer).
\]

这是手稿 compact rescaling 的局部域；它尚未从完整 physical-family 的所有 medium charts 中供应，不能被解释为全局 family 已准入。特别是手稿一般 complete-scale 条件为 `c₀ x ≤ N ≤ x^(1+κ)`，其中并非每个未经处理的 chart 都自动满足 `x≤N`。候选没有假定普遍 `q₀≥1`，而是从所写的具体局部域证明它。

主定理先调用 `native_U5_nonzero_all_signed_squares`，返回原 `s/chosen/source/slots`、同一 `k=s*chosen.prod`、同一实际 accepted trace 和 `SignedSupply`。只有在返回的真实最后来源 `source = .root` 时，才进一步返回：

- W route 及原值 `rootLevel = B(a)`；或者
- 原 singleton/pair route 及 `RootVInputs`。

后一个结构的字段包括：

\[
q_0=\frac{\log N}{\log x},\quad
\ell=\lambda_0-b,\quad
\theta_{\rm cov}=q_0\ell+2\zeta,
\quad \alpha_0=1+3\kappa\ge q_0,
\]

\[
D=x^{\theta_{\rm cov}-2\zeta}=N^\ell,
\qquad x^{q_0 s_I}=\prod\text{factorPrefix},
\]

以及严格余量与完整两上界的临界区间：

\[
\theta_{\rm cov}+b/8\le v_{1+3\kappa}(q_0s_I),
\quad
2\theta_{\rm cov}-1\le q_0s_I\le
\min\left\{\frac{32-39\theta_{\rm cov}}{34},
\frac{2-2\theta_{\rm cov}-7(1+3\kappa)/32}{3}\right\}.
\]

它还返回同一完整 canonical word 的 `actualDwellSupport D`、所选 initial prefix 的 `actualDwellSupport (D/prefix.prod)`，以及该 word 与 `(fullModulus t k).primeFactorsList.reverse` 的精确等式。原 `SignedSupply.same_rho` 仍保留在返回值中。

W 与 fresh-row 来源均未伪装成 root V；原 all-signed 供应也没有被丢弃。`source=.root` 是返回的实际来源分支条件，不是任意输入的平方或 cap licence。

## 3. 新增推导和旧证明复用

新推导只有原 max 的具体 routing、V 的小换底损失、已有整数平方字典到 D-well 的直接投影，以及它们与同一 root signed witness 的接线。

对 `1≤q₀≤1+κ`，新 `v_rescale_lower` 使用已证明的 `v_eq_min` 得到

\[
q_0v(s)-\kappa\le v(q_0s).
\]

由于 `q₀ b≥b` 且 `κ+2ζ+b/4≤3b/4`，有 `θ_cov+b/4≤v(q₀s)`。随后直接调用旧 `actualSelectedSubproductV_residue_margin`，以 `e=b` 取得 `b/8` 余量，再调用旧 `actualSelectedSubproduct_critical_iff`。换底时使用两项表达式只发生于 residue exponent 为 1 的旧恒等式；扰动后的临界区间仍由旧三项定义保留全部条件。

| 已有接口 | 本次直接用途 |
| --- | --- |
| `rootLevel` / `Part5OriginalUpsilon5CausalDictionary.level` | 原 max，不改 policy/root。 |
| `original_root_seed_bounded`、`coordinates_mem_triangle`、`level_bounds` | 证明 `1/2 < ell < 153/256`。 |
| `native_U5_nonzero_all_signed_squares` | 原非零 rho 的所有实际 witnesses、全词与同 rho。 |
| `integerSquareGates_at`、`actualNatList_cast_prod` | 索引平方字典的直接转换。 |
| `actualDwell_selected_prefix_budget` | singleton 或 pair 的全部 complement squares；没有新 tail induction。 |
| `physical_power_eq_local` | 任意 signed level 的 exact 换底恒等式。 |
| `actualSelectedSubproductV_residue_margin` | 支付 `alpha0=1+3κ` 的旧三项 perturbation。 |
| `actualSelectedSubproduct_critical_iff` | 完整上下界转换。 |
| `chenY5PrimeSelector_ordered_prime_data`、`coordinate_power` | 原素数前缀 positivity 与 exact product。 |

所有三个直接 imports 都是已选旧闭包或紧邻 all-signed 候选；没有引入新的大链，也没有调用不稳定的 `_private` 名称。本候选不需要新的 visibility patch。

## 4. 下一消费点与明确范围

返回的 full support 与实际 initial prefix，可直接供旧 `actualDwell_selected_prefix_allocate` 的 `C≥1` 分支；`C<1` 使用旧 `actualDwell_full_vector_repair`。三项 monomial 的通用代数已有 `selectedPair_monomials`。这些算法与尾部证明不应重写。

本候选没有提供 whole-atom endpoint choice。`rootRoute` 当前取决于实际点，尚须把它固定在原 coarse box 上并把 endpoint enlargement 从 reserve 扣除。已有 `actualFrozenCapacityFactors_on_box`、`actualDwellSupport_upper_inflation` 和 signed slot regroup 是应继续复用的消费者。

完整 small factor 的 prime word 没有统一正指数下界，不能把它当作 rough rank `J` 的一部分来申请固定维度上界。实际 whole-atom 证明须继续分别保留 `s` 与 rough slots，并按手稿把完整 small beta 附到一个组；本候选所给逐词支持不等于这种系数恒等式。

W initialization/overflow/finish 已有真实源码；这里尚缺原 U5 root 的 whole-box W initial-capacity/rescaling 绑定。fresh-row 原 mask 的局部临界区间与整 atom绑定也不由本文件声称。common physical Q、global bank adoption、同 rho 的 medium/no-medium 分解和最终 PP 均未关闭。

## 5. 冻结来源

手稿固定：`UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`。

- [coefficient-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/coefficient-appendix.tex)，blob `10f3e2efb2074a9b97148a5151956e1d450be13f`：`coef:full-squares`、`coef:selected-squares`、Three-factor representations、`coef:three-monomials`、`coef:tensor-identity`、`coef:parameter-order`、`coef:prime-product-insertion`。
- [sieve-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex)，blob `bf8bae30ff18f21d716138af0cc6d9fbb4a80747`：`sv:finite-feedback`、`sv:child-state`。

旧数学来源 `UyNewNas/goldbach-formalization@298670f119d24874b719facb3ef756f1e01223a1` 的对应 manifest pin：

- `ActualSelectedSubproductParameters.lean`：blob `c513e9e9ef7a908db01875d3bbb85c7e653e02b6`。
- `ActualDwellSelectedRemainder.lean`：blob `0100f85608fd65fb1f40f79645d3ded6336657d0`。
- `Part3ActualCompactInitialSupport.lean`：blob `0c8a0debdac7bf1c623b4e15493aac6fcd09282d`。

这些完整旧文件仍原样使用；本目录没有抽取或修改它们。新文件及公开声明的精确 hashes 见 `FREEZE.json` 与 `PUBLIC_DECLARATIONS.json`。静态检查不能替代后续 strict compilation、kernel replay、完整 owned declaration/type 与传递公理验收。
