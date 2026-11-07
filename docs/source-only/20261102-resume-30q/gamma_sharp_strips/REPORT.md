# Q17 — actual Gamma upper/order rejected strips

Status: **SOURCE-WRITTEN: actual fixed-t upper/order remainder paid with arbitrary logarithmic accuracy. UNCOMPILED, UNVERIFIED, ZERO FORMAL CREDIT.** Full Gamma distribution, the outside marked-family sum, and `P3.6.same_rho_PP` remain **OPEN**.

Only this assigned Q directory was written. No Lean/Lake/compiler, CI dispatch, finite guard, numerical replay, Git operation, modification of an older batch/production file, or child agent was used. Q28 independently read the source; any static PASS is restricted to the source statements below, not elaboration or kernel acceptance.

## Exact target and conclusion

The source is P's actual `rejectedWeight`, after Q16's **first-priority lower** split. Q16's `rawRemainingRejectedWeight` is split at the strict upper condition `N < m*exp(4 delta)`. The remaining part is proved to lie on the actual strict order wall `p < r < p*exp(2 delta)`. The complete integer is always `m=(t.1*t.2)*word.prod*quotient`, and original legal labels satisfy `m<N`.

`P2GammaOrderingStripPayment.eventually_original_remainingRejected_logAccuracy` proves, for every natural accuracy A and eta>0, one eventual N threshold before every later marked pair t in `pairSupport N`, Q, rho, T, H, delta and finite grid K:

```
Q subset Icc 1 N,  |rho(q)| <= 1,
0 < delta <= (log N)^(-B)
    => |originalRemainingRejectedError| <= eta*N/(log N)^A.
```

Here J is the **symbolic maximum** of `(cs.length+2)^2-1` over the literal `originalMotherOccurrences` LIST; E=max(J+2,15), and B=J+E+2A+4. No numerical mother count, maximum, or finite guard is evaluated. All repeated mother occurrences are retained. The exact error keeps Q16's literal smooth trim, the old marked pair, the original labelled word, and quotient 1. Its identity with upper plus order is proved in `originalRemainingRejectedError_eq_upper_add_order`.

This is a bounded signed **modulus** sum for each later fixed t. It does not estimate an outside sum over t or replace the manuscript's positive marked-family normalization Theta_Q. No estimate for an arbitrary sharp signed coupled prime-product family is asserted.

## Upper-product payment

`P2GammaUpperStripPayment.lean` supplies the actual finite inequality

```
|wordError| <= u*N*(1+log N)^J + 34*Y*(1+log N)^3/u,
```

for a one-bounded original-label weight supported where `0<N-m<=Y`, with `1<=Y<=N`, u>0 and J at least the fixed original fibre exponent. This is derived from sources, not an assumed strip or BV estimate.

1. P's exact kernel bound is reused: the full modulus sum costs `tau(N-m)+4*(1+log N)`. The target difference is positive before any divisor function is used; the second term pays the original q-coprime mean separately.
2. M's `original_Gamma_word_square_sum_le` supplies the actual complete-product multiplicity second moment. No injectivity of the original product map is assumed.
3. The actual map `m -> N-m` injects the band into `(0,floor Y]`. The native unshifted divisor second moment gives `sum tau(N-m)^2 <= Y*(1+log N)^3`, and the same injection gives `card band <= Y`.
4. Scaled Young's inequality supplies the displayed estimate. The constant 34 comes from `2*tau^2+32*(1+log N)^2` and `(1+log N)^2 <= (1+log N)^3`.
5. `exp(-4 delta)>=1-4 delta` gives `N-m<=4 delta N` on the literal upper wall. With `u=(log N)^(-(J+A+2))` and `B_upper=J+2A+7`, the bound is at most `(2^J+1088)*N/(log N)^(A+2)`. The remaining two logarithms absorb any eta.

The actual rejection weight is attached using **Q16's existing** `rejectedRealWeight_cast` and `rejectedRealWeight_range`. Its aggregate is between zero and one for every finite K. Consequently no K^2 grid count is charged to this remainder. P's partition/support proof is not substituted for payment.

## Strict-order payment

`P2GammaOrderingStripPayment.lean` constructs and pays the actual label set.

For e>=0 and integer p, the follower set is `p<q<=N`, `q<(1+e)*p`. The injection `q -> q-p` into positive integers at most floor(e*p) proves **card <= e*p**. Strict order excludes the diagonal; there is no `+1` lattice loss.

For a real X>=0, `closePairs` allows `1<=p<=floor(sqrt X)` and all those followers. Its count is at most eX, since `sum_{p<=P}p<=P^2<=X`. This is an upper envelope; it need not retain the original product ceiling in every enlarged pair.

For an original word of length k>=2, strict Pairwise order makes a close later tail prime imply that the **second** prime is close. The concrete code is

```
((first prime, second prime), drop 2 word ++ [original quotient]).
```

`orderCode_mem_envelope` and `orderCode_inj` prove its membership and injectivity on the actual source. For remaining-factor product r, the code belongs to `closePairs(N/r,e) x orderedFactors(k-1,r)`. The old marked pair is only dropped when enlarging the positive counting envelope; it remains in every original source/kernel. M's exact `card_orderedFactors` and the native reciprocal divisor mean give

```
card(actual order labels) <= e*N*(1+log N)^(k-1).
```

The cases k<=1 have an empty order strip and are handled separately. The construction retains ordered factor multiplicity and the quotient equal to one; it uses neither a repeated-label factorial nor a replacement long prime.

The **actual label kernel energy** is also derived. If a_m is the full original product-fibre cardinality and b_m=tau(N-m)+4L, L=1+log N, then

```
a_m*b_m^2 <= a_m^2 + tau(N-m)^4 + 32*L^2*a_m^2.
```

This uses Young's inequality and the integer fact a_m<=a_m^2. M supplies the first term through its actual second moment; the positive reflection m->N-m and native fourth divisor moment supply the second. Thus the total actual-label kernel energy is at most `34*N*L^E`, E=max(J+2,15). No shifted-correlation or energy assertion is a premise.

Applying scaled Young on the thin label set yields the proved finite bound

```
|wordError| <= u*e*N*L^(k-1) + 34*N*L^E/u.
```

For sufficiently small positive delta, the elementary exponential tangent bound gives `e=exp(2 delta)-1<=4 delta`. Since k-1<=J, taking `u=(log N)^(E+A+2)` and `B_order=J+E+2A+4` gives

```
|wordError| <= (4*2^J+34*2^E)*N/(log N)^(A+2).
```

This is proved for the actual `wordOrderRejectedWeight`, then for the full literal mother list. Both the label count and the mixed kernel moment are supplied, rather than left as inputs to an abstract strip consumer.

## Quantifiers, common mesh and source reconstruction

J, E and B are fixed by the original finite occurrence list and A, before eta's eventual threshold and before all arithmetic/grid parameters. The proof uses eta/(list.length+1) for each occurrence; induction preserves repeated words and uses one threshold for all later t.

`B_order>=B_upper` is proved using E>=15. The final common-mesh theorem invokes the actual upper and order estimates at eta/2 and pays their sum. It keeps the same signed rho in both components and the exact q-coprime mean throughout.

The lower boundary itself is assigned to the upper/order remainder; the upper boundary itself is assigned to the order remainder. The old strict original product ceiling is unchanged. Payment of this remainder does not require the grid cover, because the aggregate rejected weight is at most one without a cover. **Reconstructing the complete original source** still uses P/Q16's already stated cover `log N/delta+1<=K` and their retained/trim plateau hypotheses. Those are not erased by the present estimate.

The final B can be chosen first. P's retained-row grid/Abel norm then costs a fixed logarithmic power `3B+2`; a stronger local conductor accuracy can be requested afterwards. Residual payment does not pay the K^2 grid again, so there is no circular requirement that B dominate its own grid cost.

## Original manuscript and difficulty classification

The original passages were checked before construction:

| Original source | Exact applicable scope |
| --- | --- |
| `manuscript-body.tex:258-278` | Finite smooth weights on labelled original primes, fixed polylogarithmic Euler norms, product O(N), same signed rho and exact q-coprime mean. |
| `manuscript-body.tex:316-341` | Smooth complete-product trim and smooth chart retained; no new sharp coupled HB boundary; Fourier norm charged. |
| `manuscript-body.tex:354-357` | Explicitly does not assert arbitrary signed sharp coupled domains. |
| `manuscript-body.tex:543-559` | Lower trim is power-small; positive outer smoothing takes N to infinity at fixed precision before precision goes to zero. The same rho is used at each precision, and may change between precisions. |
| `manuscript-body.tex:795-806` | H/h claims are averaged over a positive marked family, not pointwise B or a signed outer measure. |
| `low-rank-convolution-bv-20261010.txt:114-150` | q-independent one-prime/complement rows, exact multiplicities and full local scale. Hard coupled restrictions and tails must already be reduced. |
| `distribution-prime-product-completion-20261010.txt:66-70,74-95,370-395` | No sharp signed coupled-domain theorem is used; smooth trim, full scales, bounded actual rho and fixed integrated chart norm are required. |

The two-stage positive outer approximation alone never implied a moving logarithmic-mesh sharp residual bound. Equally, the absence of such an implication was **not a manuscript counterexample**: the smooth positive argument does not claim that general sharp theorem. The new local arithmetic proofs now supply the particular upper/order absolute errors introduced by the P/Q16 exact original-Gamma decomposition. This resolves that source omission as **category (2)**, rather than leaving a mathematical strip estimate as an input. Untested Lean expression/API work remains **category (1)**. No category-(3) contradiction in the original smooth theorem is asserted.

## Reuse and remaining obligations

Exact raw hashes, declarations, direct imports, intended modules and line locations are in `REGISTRY.json`. Principal reused suppliers are:

- Q16 `P2GammaLowerRejectedPayment`: real representative/range of the actual aggregate rejection and its first-priority lower split. This is imported, not copied.
- P `P2GammaCompleteProductTrimPayment`: actual `wordError`, nonzero-distance kernel modulus bound, and literal mother list.
- P `P2GammaRetainedInteriorGeometry`: original finite reconstruction and the row support alternative.
- O `P2GammaOriginalCartesianMask`: actual legal-head/complement dictionary, including strict ordering and old marked pair.
- M `P2OriginalGammaDivisorNorm`: exact ordered-factor count, root multiplicity, grouping, and actual whole-product second moment. The existing complement norm is not reproved.
- Native `LiLiuPrereqFouvryDivisorMean`: reciprocal divisor mean and unrestricted fixed moments, including fourth moment; no squarefree restriction.
- Production `BoundaryArbitraryLog`: only elementary power/log and reciprocal-log absorption.

Search covered production, all source-only batches, and hidden/ignored `.lake/proof-continuation/source-reviews/drafts`. Existing P4B ordering/physical-boundary sources concern different fixed-precision prime-pair positive mass reserves; they were inspected and not substituted for this original labelled Gamma modulus-sum error. No existing actual Gamma upper/order payment was found to duplicate.

Remaining: Q16's independent lower remainder and original lower-trim payment must be composed with the already reconstructed source; actual retained rows must be supplied to conductor consumers with their original-scale comparisons, and every external marked-family/scalar sum must be paid. The original signed PP assembly and full node remain OPEN. Neither current file is installed into production or kernel-verified.

Static checks: new Lean contains no admission, axiom, evaluation, unsafe or compiler escape form; imports and theorem premises were read; source pins were computed from raw bytes; REGISTRY JSON is parsed as data. These checks are not Lean verification. All finite guards remain UNEVALUATED.
