# Q16 — actual Gamma lower rejected strip

Status: **SOURCE-WRITTEN; UNCOMPILED; ZERO FORMAL CREDIT.** The bounded enlarged lower-strip combination is supplied. Full Gamma / `P3.6.same_rho_PP` remains **OPEN**. Only this Q task directory was written. No Lean/Lake/compiler, CI dispatch, proof guard, numerical replay, Git operation, old-file modification or child agent was used.

## Original scope and the precise missing deduction

The inspected manuscript is `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`. Lines **258–278** concern fixed finite smooth weights on labelled original primes, a fixed positive original-prime power floor, product `O(N)`, fixed polylogarithmic mixed Euler derivative bounds, no additional arithmetic filter, and the admitted actual upper/lower/marked/ordinary-descendant/positive-switched signed coefficients. The SAME signed rho occurs in the progression and exact q-coprime mean. That is the full surrounding PP scope; the present module does not claim to prove it for arbitrary coupled smooth amplitudes.

Lines **316–341** place the smooth lower trim below `2 N^(1-kappa0)` before the exact smooth chart partition. The local scale is the COMPLETE product, with the displayed original-N comparisons, and separated profiles must pay their Fourier norm. Lines **543–559** pay a power-small complete-product trim strictly below N and use positive outer approximation for fixed boundaries. The order there is N tending to infinity at each fixed approximation precision, followed by approximation error tending to zero; rho is the same within each precision, but may differ between precisions. No N-dependent approximation precision is inferred from those sentences here.

The completion note `../chen-imbalanced-semiprimes/paper/source/modules/distribution-prime-product-completion-20261010.txt`, lines 74–95 and 370–395, supplies the same smooth complete-product trim order, divisor payment, and separate singleton treatment. The low-rank note `../chen-imbalanced-semiprimes/proof-library/source/low-rank-convolution-bv-20261010.txt`, lines 114–150, requires q-independent separated factors and leaves coupled tails to previous reductions. Their raw hashes are in REGISTRY.

P supplied the actual low-product budget, smoothTrim plateau, original mother-list trim payment, exact retained/rejected reconstruction and `rejected_row_support`. P REPORT item 3 and the t27 addendum still left the following conversion: a retained lower endpoint `H >= 2T`, where `T=N^(1-kappa)`, creates a rejected lower support `m < H exp(4 delta)`, larger than the old cutoff `ceil(2T)`. Merely citing the old smooth-trim signed error would be invalid: signed discrepancy estimates are not monotone under pointwise weight domination. This module applies P's finite low-product budget to the ACTUAL enlarged-cutoff rejected weight instead.

## New source and exact source bindings

`P2GammaLowerRejectedPayment.lean`, intended module `ImbalancedChen.P2GammaLowerRejectedPayment`, imports only `ImbalancedChen.P2GammaCompleteProductTrimPayment`. The direct source dependency and all reused API/provenance hashes are recorded in REGISTRY. No frozen source is copied or repaired.

* `rejectedRealWeight_cast` identifies the displayed nonnegative two-index real hat sum with P's existing complex `rejectedWeight` exactly. `rejectedRealWeight_range` uses O's PARTIAL hat partition to prove this weight lies in `[0,1]`, without a `K^2` loss, a cover assumption, or an assumed residual bound.
* `rawLowerRejectedWeight` keeps the entire actual rejection precisely when the COMPLETE original product satisfies the STRICT test `m < H exp(4 delta)`. `rawRemainingRejectedWeight` keeps it on the complementary closed side. Thus any overlap with an upper/order reason is assigned to lower first, and the boundary belongs to the remaining term. `rejectedWeight_eq_lower_add_remaining` is an exact identity, not a support estimate.
* `wordLowerRejectedWeight` retains P's literal `smoothTrim T m` multiplier. An empty word has no head/complement row and is assigned zero in this lower-row component; its original source is left unsplit, not deleted. Every nonempty word is attached by `original_rejected_trim_split`.
* `original_trimmed_word_eq_retained_add_lower_add_remaining` composes P's actual finite reconstruction, P's proved trim plateau and the new split. Its original hypotheses remain `t in pairSupport N`, `T>0`, `H>=2T`, `delta>0`, and the numerical cover `log(N)/delta+1<=K`; the test F follows the grid. The identity displays the unchanged retained Cartesian rows, the lower rejected component paid here, and the UNPAID remaining term. The marked pair stays in the complete complement; all root-label multiplicities, original target deletion, signs and the quotient 1 remain in the imported physical labels.

## Enlarged cutoff payment and quantifier order

Fix `0<kappa<1`, `C0>0`, a real mesh ceiling `delta0`, a natural accuracy A and `eta>0`, BEFORE N. For useful positive meshes choose `delta0>0`. Set

```
T = N^(1-kappa),       E = C0 exp(4 delta0) + 1,
Y = ceil(H exp(4 delta)).
```

`eventually_enlargedCut_bounds` proves, at ONE eventual N threshold, for ALL later `0<=H<=C0*T` and `delta<=delta0`,

```
Y < N,                 Y <= E*T.
```

The `+1` pays the integer ceiling using `T>=1`. Strict `Y<N` is established before invoking P's divisor-of-`N-m` bound, so no `tau(0)` occurs. The weight vanishes when `m>Y` by its actual mask, and its absolute value is at most one by the proved hat and smoothTransition ranges.

`eventually_word_lowerRejected_logAccuracy` then invokes P's `exists_word_low_product_budget` with `eps=kappa/4`; the actual source multiplicity and nonzero-difference divisor constants C,D are P's original independent constants. The resulting numerical bound is

```
E C D N^(1-kappa/2)
  + 4 E C N^(1-3kappa/4)
  + 4 E C N^(1-3kappa/4) log N.
```

The existing `eventually_powerLog_le_logAccuracy` pays these three strictly sublinear powers. This is cutoff inflation and substitution into P's budget; the low-label count, divisor estimate and exact coprime-mean estimate are not reproved.

`eventually_list_lowerRejected_logAccuracy` inducts on LIST occurrences with halved eta budgets. It never evaluates a mother occurrence count or deduplicates words. `originalLowerRejectedKernel` uses the literal `secondFunctionalMotherPrefixIndices.map` and `secondFunctionalMotherGammaWords.map` nested lists and the same `rootLabels`; `originalLowerRejected_sum_eq_literal_list` binds it to P's exact flattened `originalMotherOccurrences`.

The final theorem `eventually_original_Gamma_lowerRejected_logAccuracy` has ONE threshold before every later marked pair `t`, H, delta, grid size K, modulus cap M, finite Q and signed rho. It proves

```
abs(sum q in Q, rho(q) * originalLowerRejectedKernel(N,t,T,H,delta,K,q))
  <= eta * N / log(N)^A
```

under `2T<=H<=C0*T`, `0<delta<=delta0`, `M<=N`, `Q subset Icc 1 M`, and `abs(rho(q))<=1`. The same rho and exact q-coprime kernel appear throughout. This is uniform in every later t, not a claim about an additional outside sum over all t. `K` denotes the grid cardinality here; no manuscript density constant is changed.

The upper comparison on H is necessary: `H>=2T` alone could place the cutoff above N and does not imply a power-small error. The admissible concrete choice `H=2T`, `C0=2` supplies the plateau. No change to P's mesh selection is required: its `delta=(log N)^(-B)` and numerical cover may be used once they satisfy the fixed ceiling, with B fixed before N. The payment itself is uniform in all finite K and all such widths, so it does not choose a new shrinking mesh to assert upper/order accuracy. Cover is needed for the source identity and remains an explicit hypothesis there; it is not needed for the lower payment.

## What is eliminated and what remains

Eliminated at source level: the actual lower rejected weight/range conversion, strict enlarged-cutoff support and ceiling payment, its combination with the original retained-row plateau, and full original mother-list lower rejected payment with one original-N threshold before all later t and arithmetic data. These are category (2) omitted deductions, with category (1) Lean/API verification still pending.

OPEN: the remaining upper-product/order rejected term (Q17), literal colour/window-to-prime-interval attachment, physical row scale/L1/L2/cap/gap data, final conductor assembly and full Gamma distribution. This module neither assumes their target estimate nor replaces them by a generic BV premise. It does not settle P's category (3) caution about deriving sharp-boundary arbitrary-log accuracy from the manuscript's fixed-precision positive approximation order. That caution is not a counterexample to the original smooth theorem.

## Verification boundary

Only source/static, declaration/import, raw SHA256 and forbidden-form checks were performed. No admissions, axioms, compiler/evaluation tactics or unsafe forms occur in the new Lean source. The independent Q27 review has inspected the actual range proof, lower-first boundary, original source reconstruction, cutoff inflation, mother-list identity and threshold order; its final frozen-byte record is maintained separately under the Q `reviews/` directory. Static PASS is bounded source review, not Lean elaboration, build/kernel acceptance or full-node closure. All finite guards remain UNEVALUATED.
