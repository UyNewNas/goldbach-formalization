# Gamma geometric separation — P task 13

Status: **SOURCE-WRITTEN, UNCOMPILED, ZERO FORMAL CREDIT; P3.6.same_rho_PP remains OPEN.**

Only this assigned P directory was written. No compiler, Lean/lake command, CI dispatch, finite proof guard, numerical replay, Git operation, or child agent was used. O and production files were not modified. Static independent review was coordinated with the already assigned t27 reviewer.

## Reuse and nonduplication

The frozen O directory actually contained only `P2GammaOriginalCartesianMask.lean` and `P2GammaSmoothLogGrid.lean`, with no O REPORT, REGISTRY, or retained-tensor file. The repository/source-only search did not locate a further Gamma retained-tensor supplier. Both existing O files are imported, not copied or repaired. Their exact definitions remain the source of the original head/complement dictionary and logarithmic hats.

| Reused source | SHA256 | Actual reuse |
|---|---|---|
| `docs/source-only/20261102-resume-30o/gamma_geometric_separation/P2GammaOriginalCartesianMask.lean` | `81f4482b1fbede16a46b7d4a946f0bc49df691f44e534b4843dc8c30680b30f4` | `rebuild_mem_root_iff`, `original_word_test_eq_cartesian`, original head/complete complement and target deletion |
| `docs/source-only/20261102-resume-30o/gamma_geometric_separation/P2GammaSmoothLogGrid.lean` | `ae94353d4ec8614a2f599d8f822be0542fd076793caf1bdcf0328068bbbd1985` | Exact partition, support endpoints, and `exists_complexWeight_Abel_budget`; no generic Fourier/tensor theorem is rewritten |
| `docs/source-only/20261102-resume-30m/gamma_short_fibre_bv/P2OriginalGammaDivisorNorm.lean` | `f9696bad18970592465f84146daa65ef8e72bb8cad11a43645298776709a98df` | `card_rootProductFiber_le`, `rootComplementCoefficient_norm_le`, actual root labels; source multiplicities are retained |
| `docs/source-only/20261028-resume-30f/transfer_lambda/P5OriginalSingletonLowerTrimPaid.lean` | `82cfc7b75510076d0ded95130504639cde2ee39d38cff4133964a092d5cbcf54` | Only the numerical `eventually_originalLowerCut_lt` cutoff bound; its singleton discrepancy estimate is not substituted for Gamma |
| `ImbalancedChen/Part3PolynomialResidueDivisorBound.lean` | `7cbc4c842aa4dbf18ab9644465e4983014c8aaf8bd38f74dd1b37a5574a2feda` | `PolynomialResidueDivisorBound.fouvryTau_le_const_rpow`, once for source multiplicity and once for nonzero target difference |
| `ImbalancedChen/P5OriginalPrimeEndpointDivisors.lean` | `65d6b1f423829e6160609121288a06bb4d6b4d02548c4c0f1548d70044735067` | `sum_abs_rho_congruence_le_divisors`; only the elementary nonzero-distance divisor bound |
| `ImbalancedChen/TotientReciprocalBudget.lean` | `aa80ff2ad79f77405951f1e56e993a851a1b32ad46c970e7914adb94bdb2db86` | `sum_reciprocal_totient_subset_le_log`, preserving the exact coprime mean |
| `ImbalancedChen/BoundaryArbitraryLog.lean` | `2694e8398198c9edeab5f0c4bad70c514a22de21a0cec6edec33c2faec742167` | Only `eventually_powerLog_le_logAccuracy`; its distinct two-prime geometric boundary estimate is not applied to Gamma |

Every import above is a source dependency. This report does not promote any uncompiled source dependency to a kernel-verified theorem.

## New concrete geometry

`P2GammaRetainedInteriorGeometry.lean` has SHA256 `9aa2884c2fe7d514576e41247cb2675d78894af38fe780a3f1812054d29afc1a`.

For head grid index j and complete-complement index l, `Retain` consists of the numerical conditions

```
H <= L_j L_l,  U_j U_l <= N,  U_j <= every remaining specified prime.
```

The beta label is the actual complement hat times this fixed indicator. It contains the old marked pair, the remaining original word, the original quotient and its masks, including quotient 1. The old pair is never promoted to a free long prime. Neither row, index set nor retention test has a q, conductor, character or moving-residue argument.

The new obligations actually discharged are:

* `retained_row_legal` / `retained_row_zero_on_illegal` (lines 59/90): O's previously unsupplied zero-extension premise follows from the explicit endpoints. Strict original ordering and product ceiling are proved, not erased.
* `original_retained_row_eq_cartesian` (102) and `retained_row_complete_scale` (117): a literal original row is a Cartesian prime/complete-complement row, with H < complete product < N.
* `rejected_row_support` (159): a nonzero rejected term satisfies `pm < H exp(4 delta)`, or `N < pm exp(4 delta)`, or `r < p exp(2 delta)` for some remaining specified prime. On original legal labels one additionally has p < r and pm < N; only with those original inequalities is the third alternative a narrow ordering strip. No small-mass conclusion is claimed here.
* `retained_add_rejected_eq_one` (221) and `original_word_eq_retained_rows_add_rejected` (267): the actual source equals the retained Cartesian rows plus an explicitly defined rejected weight. The only cover premise is `log N / delta + 1 <= K`. The arithmetic test F is quantified after the fixed rows. No source identity is an input.
* `retained_complement_norm` (314): the actual beta uses M's divisor bound, with no number-of-head-primes multiplier.
* `exists_fixed_grid_Abel_budget` (332), `gridSize_covers` (354), and `exists_fixed_logarithmic_grid_budget` (365): finite counting-measure integration of the two-index rows costs at most `K^2(1+2D/delta)`. For `delta=log(N)^(-B)` and `K=ceil(log(N)^(B+1)+1)`, this is at most `9(1+2D)log(N)^(3B+2)`, for `log N>=1` and `2 delta<=log 2`. D precedes B,N and all clipped intervals. These are proved numerical/variation budgets, not assumed Fourier or BV estimates.

## New complete-product trim payment

`P2GammaCompleteProductTrimPayment.lean` has SHA256 `6876350ce5144736ea6d5fb762df0f94683077a1fd60a2a8475fc24e4ba509f7`.

The actual smooth trim is `smoothTransition(m/T-1)`, with `T=N^(1-kappa)`. The removed weight is between zero and one and vanishes for m>=2T. The proof works at the complete integer m, not at the residual quotient.

* `lowLabels_card_le_divisor_sum` (48) groups the actual root labels without assuming product-map injectivity.
* `kernel_absolute_modulus_sum_le` (83) uses divisors of N-m only after m<N; its coprime-mean term is paid by the actual reciprocal-totient sum. No tau(0) appears.
* `exists_word_low_product_budget` (119) derives the finite bound `Y C N^eps (D N^eps + 4(1+log(max(1,M))))` for every bounded source perturbation supported below Y<N. C and D are supplied by separate divisor theorems, not hypotheses.
* `eventually_word_smoothTrim_logAccuracy` (267) chooses eps=kappa/4, giving source powers `1-kappa/2` and `1-3kappa/4` and arbitrary requested logarithmic saving.
* `retained_chart_smoothTrim_plateau` (221) and `original_retained_trimmed_row_eq_cartesian` (239) remove the literal coupled trim from a retained row by proving it equals one when the row's complete lower endpoint H is at least 2T. The smooth trim is not left hidden in F and then called separated.
* `gammaDiscrepancy_eq_trim_add_remainder` (337), `gamma_trim_sum_eq_literal_list` (418), and `eventually_original_Gamma_smoothTrim_logAccuracy` (443) bind this result to the complete original nested mother lists. List induction retains every repeated occurrence and produces one eventual threshold before t,Q,rho. It does not evaluate or assume a numerical occurrence count.

The full-Gamma trim theorem requires fixed `0<kappa<1`, every A and positive eta, `M<=N`, positive moduli `Q subset Icc 1 M`, and `|rho(q)|<=1`. It is uniform in every original marked pair t in pairSupport N and keeps the same signed rho and exact q-coprime mean. It proves only lower complete-product restoration, not full Gamma distribution.

## Remaining obligations and manuscript difficulty

1. **OPEN: literal head colour/window to the small-conductor prime-interval API.** The real carrier is preserved, with primality and target deletion already proved by O, but its colour-conditioned finite window has not been bound to the exact clipped-interval conventions used by O's variable-prime profile. The scalar budget is uniform for such intervals; their actual endpoint dictionary still needs attachment. This is category (2), an omitted finite geometric deduction, with category (1) endpoint/API work.
2. **OPEN: ordering and upper-product rejected mass after the modulus sum.** The support theorem is not a payment. Neither an assumed residual estimate nor a generic signed-BV premise is accepted in its place. A pointwise `tau(N-m)<=N^eps` times a logarithmic mesh width does not by itself give arbitrary logarithmic accuracy. The required quantitative actual-source strip estimate remains absent.
3. **OPEN: the complete rejected-sum assembly.** Choosing H>=2T makes retained rows lie on the literal trim plateau, but its rejected lower strip extends to H exp(4 delta). The generic finite low-product budget is available; the conversion of that particular residual weight and its enlarged cutoff into the paid lower-tail theorem has not been composed. No claim that the entire rejectedWeight is small is made.
4. **OPEN: final mother-row/interval/conductor composition.** Exact source reconstruction and the explicit grid norm do not yet supply every permitted row to O's small-/large-conductor consumers, nor do they prove the final Gamma bound or the manuscript q-range.

The original manuscript inspected first was `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, lines 258-278 and 316-341, SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`. Its first statement admits finite smooth weights with fixed polylogarithmic Euler derivatives; its second insists on complete-product scale and charged Fourier separation. Lines 543-559 explicitly give complete-product trim and positive smooth outer approximation with N tending to infinity before the approximation error tends to zero.

The original low-rank note, lines 114-150, SHA256 `88edfb5f605e65ad7f05a702a963b5dff1b21f0b4e757edbf4eaed304f4e8f56`, allows one-variable interval weights, insists on q-independent alpha/beta, and explicitly leaves hard coupled restrictions and tails to prior reductions (132, 144, 148). The completion note, lines 74-95 and 370-395, SHA256 `a953b3233c1249b4791830da33b76a58b19ca110a5e1b5b6172b3248a00053e1`, is the source for the smooth lower trim and fixed scalar norm.

Thus the new finite geometry and complete-product trim fill category (2) omitted deductions. All Lean elaboration remains category (1), untested by instruction. The further inference that these paragraphs already give an arbitrary-log estimate for the literal sharp ordered Gamma carrier is a **category (3) possible substantive source gap**: the stated two-stage positive outer approximation alone is not the quantitative logarithmic-mesh residual estimate required by that inference. This flags a missing argument, not a claim that such an argument is impossible.

## Static checks

New files were inspected for imports, explicit source bindings, quantifier order and circular estimates. No `sorry`, `admit`, `axiom`, `native_decide`, `run_tac`, or `unsafe` occurs in either new Lean file. A self-containing simp rewrite found in static review was replaced by `sourceTest_sub` and a pointwise algebraic equality. Hashes were computed from final bytes. No compile or kernel verification is asserted; finite guards in dependencies remain UNEVALUATED. No source-only dependency was installed into production.
