# P2.9 — original Γ5 fine-price supply audit

Date: 2026-11-25. Read-only source audit; no Lean source was added or changed, no cloud or local compilation was run, no numerical integral or certificate was recomputed, and no Git ref was moved. This report gives zero new formal, kernel, numerical, or endpoint credit.

## Conclusion and current frontier

The existing original Γ5 suppliers already give its precise relative price against the original raw-scale seed mass and the original marked Θ mass. The current actual atlas ordinary comparison reaches that same seed mass without changing its coefficient. The original same-N density conversion then permits the main term to retain the original Θ price.

**An independently evaluated scalar fine J for the whole U4 Entry family is not a necessary additional obligation of the current finite-fallback route.** The existing coarse J is enough for absolute correction/error estimates. A separate fine J would require a further whole-seed mass limit or numerical bound, and this audit did not find such a completed consumer. That absence must not be promoted to a manuscript gap or a new mandatory frontier item.

The original second-seed gain `actualJ2omega` is not this positive-product J. The fixed U3 clamp long-word J is also not the current U4 Γ5 family.

## Frozen manuscript anchors

Repository: UyNewNas/chen-imbalanced-semiprimes.
Commit: a988cba584d803ae2856a0de50efb582f4f3dd6a.
Files are under `paper/release-20261106/en/`.

- `argument.tex`, lines 359–407: admitted finite nonnegative labelled prime-product families, fixed positive prime floor, bounded rank/weights, ordinary mass hypothesis, positive smooth outer approximation, and the order “fix approximation, then N tends to infinity, then approximation error tends to zero.”
- `sieve-appendix.tex`, lines 763–776: the inclusive bad region D5− has v+2u≥1. Its cost is the positive K*cω*s0/4 kernel against du dv/(uv). The ordinary bad-pair term and its feedback are not retained a second time.
- Lines 837–869: the full Γ9–21 switched masses, including Γ20/21 unit surfaces, enter the two-step base.
- Lines 877–891: S=11/5, s0=227/50, (phi1,phi2,phi3)=(353/100,29/10,61/25), and K_seed=681/100. The text explicitly states K<K_seed.
- Lines 893–931: the finite seed and its directed certificate establish the original net gain above 20249/10^6 and 1/50, uniformly on each fixed finite collection of admitted marked families; the enhanced comparison also retains L/S<chi.
- `numerical-appendix.tex`, lines 616–697: the certificate map distinguishes `/gamma5_cost_decompositions`, `/seed_certificate`, and later tables.
- The release README states that the complete 1106 numerical supplement is distributed separately on Zenodo and is not committed to Git. This audit did not download or run that archive.

## 1. Exact Γ5 scalar price — already supplied

Selected source:

`docs/source-only/20261102-resume-30s/s16_gamma5_and_costs/P2EnhancedBadGamma5CostTheta.lean`

Git blob: `2341f72e4109bb8b668627962b44ef6477be1c0c`.

Public declarations:

- `ImbalancedChen.P2EnhancedBadGamma5CostTheta.actual_bad_inclusive_upper`.
- `ImbalancedChen.P2EnhancedBadGamma5CostTheta.original_badGamma5_cost_theta`.

The original coefficient is

```text
badRawCost = (omegaCap / a0) * badMassLog
omegaCap = 70893/125000
a0 = 50/227 = 1/s0
s0 = 227/50
```

`badMassLog` is exactly the original bad-region reciprocal integral. The identity `P2SeedOmegaLiteralFunctional.badRoughDouble_eq_original_log` is in blob `f63b0bab28f3308bc5c80ceec2945bca80f31371`, with original literal geometry in `P2SeedOmegaLiteralFibre`, blob `c8c48206f3a8d25baac9cd6859dfabde1dcecd12`.

The arithmetic reciprocal quadrature is already supplied by

`P2EnhancedBadGamma5PrimeQuadrature.reciprocal_quadrature`,

blob `fe4f2a282a0ab7227597cdf56a654dc7ef5b827b`, at the same `s16_gamma5_and_costs/` path. Its finite upper carrier includes closed boundary atoms, including 2u+v=1. It uses the original constant-cutoff kernel; it explicitly does not substitute the native feedback kernel gamma5MassH.

For fixed η>0 and ε>0, `actual_bad_inclusive_upper` chooses a single T before every Q and d. Its hypotheses are exactly d>0, N^η≤Q/d, and 2≤trueAlpha N Q d. Its conclusion is

```text
ordinaryBad N Q d <= rawScale N Q d * (badRawCost + epsilon).
```

The inclusive ordinary source includes the unit cofactor. There is no alpha reset, no new tail coprimality/distinctness assumption, and no replacement by a feedback triangle.

The definition

```text
rawScale N Q d = N / (d * log (Q/d))
```

is the existing `P2EnhancedNonunitWordMass.rawScale`, blob `32566a8425e4c2a3db37a2b0485377347f2c63ed`, path `docs/source-only/20261102-resume-30q/enhanced_nonunit/P2EnhancedNonunitWordMass.lean`.

The marked theorem retains the exact original Θ and proves

```text
convertedBad N Q D sigma
 <= badRawCost * Theta N Q D sigma + epsilon * Theta N Q D sigma.
```

Its additional hypotheses are only positivity of d on D and nonnegativity of sigma, plus the same scale and true-alpha rows. Empty support and zero Θ are permitted.

## 2. The actual seed consumer is already connected

`ImbalancedChen.P2FiniteMarkedGamma5SeedOrdinaryPrice.raw_and_converted_upper`,
blob `1e46d63390ee2cecdfca55b6a4642eac6451b8b1`, instantiates η with the actual `frozenResidualFloor`.

The original `scale_and_alpha` discharges the scalar scale and true-alpha hypotheses at every original LevelIndex. Original positive levelMark and `literal_eq` carry them through the actual seed sum. The threshold precedes n, root, and t. The remaining actual parameters are

```text
0 <= t, t <= 1/12, 1/((n:Real)+1) <= 11/384.
```

Writing Q(p)=rootQ N n root t p solely as notation, its two existing conclusions are

```text
seedMass (ordinaryBad N (Q p) w.prod)
 <= (badRawCost+epsilon) * seedMass (rawScale N (Q p) w.prod)

seedMass (thetaConversion N w.prod * ordinaryBad N (Q p) w.prod)
 <= (badRawCost+epsilon)
      * sum p in originalBand N root, markedTheta (seedPositions N n root t p).
```

Both retain original root primes, selected seed positions, old words, marks, and repeated product multiplicity. The error is proportional to the same original mass after summation; it is not an independently assigned epsilon per moving p or history.

The current atlas theorem

`P2FiniteMarkedGamma5SeedAtlasOrdinaryComparison.atlas_mass_le_original_ordinary_plus_epsilon`,
blob `c9d5255f97eff22d18d06b5f3296b58dd90ecc03`,

already compares the actual Entry family with that exact original seed ordinary mass. Thus the immediate composition yields, for the selected fixed approximation,

```text
norm N * actual Entry ordinary mass
 <= (badRawCost+delta) * norm N * original seedMass rawScale + epsilon.
```

This is finite-sum composition of supplied results; it requires no new Γ5 asymptotic analysis or integral computation.

The existing

`P2FiniteMarkedGamma5SeedAtlasFinitePP.density_times_seed_ordinary`,
blob `26b5b5adeb17598892a01462180ff578c896d4b0`,

uses `SeedConversionFloor`, blob `fab58db236dfa4654b746e6012b83c96ec586165`. If the same density D has the original bound D≤C*singularSeries(N)/log N with C≥0, then, for 0<delta_conv<1, the original ordinary seed main term is bounded by

```text
C / (4*(1-delta_conv)) * (badRawCost+delta_raw)
  * sum p in originalBand, markedTheta (seedPositions ... p).
```

This statement prices the original seed main term. Multiplication and payment of the atlas approximation loss use the same density/error branch and are not silently included here. The same-rho signed distribution/correction work is being handled separately.

## 3. What the original numerical seed gain actually says

`Part5OriginalH430SeedConvertedMass`:

Path `docs/source-only/20261110-yellow-closure-10t/t07_h34_actual_counts/successor_base_seed/Part5OriginalH430SeedConvertedMass.lean`.

Blob `d8e12e013fcdc888ee8f756c2f2a3f6188564559`.

Its existing `original_inclusive_converted_mass` handles the original complete converted source

```text
converted = convertedBad + original Gamma9--21 converted ordinary words
convertedCap = badRawCost + sum j : Fin 13, switchedMass j.
```

Here Fin 13 indexes the thirteen Γ9–21 rows. These are not thirteen Γ5 copies.

The existing identity is

```text
seed_split:
actualJ2omega = (ordinaryPart - (K_seed/4)*convertedCap) / 5.
```

`base_after_converted` and `first_seed_after_converted` use this net surplus on exactly the same Θ. The latter proves the initial 1/50 lower gain after all listed ordinary charges; it does not identify `actualJ2omega` with a positive-product mass upper bound.

The current original history owner is

`Part5OriginalH430SeedHistoryMass`, blob `697ed9e2b6d9cc96bcccff48cc78e30743960d5b`,
path `docs/source-only/20261125-p2-actual-source-rank/owner-postimages/ImbalancedChen/Part5OriginalH430SeedHistoryMass.lean`.

Its `real_word_theta` is the exact grouped product-weight identity; `converted_centre_on_histories`, `converted_on_histories`, and `positive_seed_positions` already apply the original seed cost to arbitrary actual LevelIndex subfamilies. This is the existing source to reuse.

The numerical source

`P2SeedOmegaOriginalNumerical`, blob `a5619dc5e977b4e367147fec68aea6792f21a569`,
path `docs/source-only/20261110-yellow-closure-10t/t07_h34_actual_counts/base_seed_required_helpers/P2SeedOmegaOriginalNumerical.lean`,

contains `sourceValue_eq_actual`, `sourceBound_contains`, `original_8192_lower_endpoint`, and `actualJ2omega_gt_safe_base`. Its Q80 Darboux supplier is blob `f99ae37ecb2a5ecebd3b76ef5ce1217fbaadac2b`.

**Qualification boundary:** the inspected historical registry `f7eaee618fda8d9e457b3813f762a092d10f6d05` records compilation false, kernel replay false, and finite certification UNEVALUATED for that packet. This audit identifies exact source/theorem binding and does not turn it into accepted numerical proof evidence. No saved endpoint was imported as an axiom or recomputed.

## 4. Checked candidates that do not supply the whole U4 fine scalar mass

| Existing supplier | Exact blob | Verified scope |
|---|---|---|
| Part5OriginalH430RootIntervalTheta.actual_interval_theta_limit | 28ae6ccaa118cab66261be32d10058982f1c7a47 | One fixed exponent L and one fixed half-open interval of root primes; requires 0<b<c<1 and c<L. It is not the complete selected descendant seed sum. |
| Part5OriginalH430ClassicalFixedClampSeedPrice.geometric_raw_J / original_price_common_limit | 87cd754e4093d53fb5a946c7ea41b73fc1de4f59 | The original U3 fixed positive-width clamp and its long-word source, with 1/3+7/128≤ν≤1/2 and κ≤1/112. It does not cover the present U4 Γ5 Entry family. |
| Part5OriginalH430OwnedThetaWord.owned_theta_density | 7537b2040f489d4604366bfec158004c12ea5026 | Exact original singular/totient insertion for complete ordered words, preserving repeats; uses actual owned membership and the original scale rows. |
| Part5OriginalH430AbsoluteWordBox.uniform_wordBox_normalization | ea46ca884a4234b3edcadb6586ab185f352ba2b5 | Arithmetic-prefactor normalization to the prime-box weight, uniformly for bounded actual word marks. It does not evaluate the selected seed domain's total integral. |
| Part5OriginalH430DiscreteThetaTransport.fixed_program_arithmetic_threshold | 41b25ff238bc7c76340c2744496854dbe780ae5e | Absolute displacement between the ideal and frozen Θ weights on the same word and same mark. |
| Part5OriginalH430FullPrimeTheta.all_program_arithmetic_threshold / emitted_prime_threshold | 62d13d87c0968bad7322836bb22b07c86e27e434 | The complete fixed Program family and positive native support; finiteTau n is the original approximation path. Still a displacement estimate, not a numerical total-seed mass terminal. |
| P2EnhancedThetaReciprocalMass.Theta_lower | 79c11753fd6fd8ce6c088984a5fe9aea34ae3c6f | A lower comparison with reciprocal marked mass, used for collision errors; not the needed upper fine total-mass bound. |
| P2CausalMarkedThetaSupply | f05664bfaaa689a2012c6034c73ce1ce6a73beeb | Exact sourceSigma/Θ and existing cost applications for its generated box histories; its own scope does not identify all adopted selected numerical histories. |

The source inventories searched were the untruncated active and source-only trees cached at the task baseline, the 764-source actual-small-payment selected-source manifest, current new source packets, and the exact candidates above. GitHub's default-branch code search returned no hits even for known symbols and was therefore not treated as evidence of absence.

## 5. Optional fine-J consumer versus necessary mainline

If an independently specified scalar fine J is desired, the missing supplier would have to bound the **original**

```text
norm N * seedMass N n U4 t
  (fun p w => rawScale N (rootQ N n U4 t p) w.prod)
```

at the fixed pre-N precision and selected-domain data. Equivalently one could first establish the original whole-seed Θ/singularNormalization limit together with the exact raw-scale normalization bridge. The required carrier must retain originalBand, shape/read-label selection, rootCode, original marks, and full ordered old words. Existing single-root interval limits cannot simply be substituted. Existing T23 precision theorems use the path t=finiteTau n and do not supply an unproved uniform limit for every moving t.

This is an uncompleted original-mass limit/aggregation consumer in the inspected formal sources. The manuscript's local relative-Θ price is already supplied, and no contradiction or mathematical gap in the 1106 argument was established.

The current route can retain that relative Θ price. Its independent coarse ordinary bound is already

`P2FiniteMarkedGamma5SeedAtlasCoarsePrice.ordinary_bounded`,
blob `057222493d1e5701d69f1da07e18718131dce0b4`,

using `CoarseAtlasMass.uniform_mass_bound` and `finite_marked_bound`. Current CoarseAtlasMass blob `7764b3e52b1842b4d949f6bcd08cf88a897795d6` differs from its predecessor only by exposing `weight_le_one_on_support`; no fine-price theorem was added. The fixed finite Entry coarse constant is sufficient for the absolute remainder suppliers. No 29 H247/native-Wu endpoints are introduced as necessary mainline obligations.

## Saved exact fallback composition

The already agreed composition `TestedSeedMass.tested_seed_le.trans (SeedAtlasFinitePP.fallback ...)` is recorded without a new synonymous Lean wrapper:

- Suggested path: `docs/source-only/20261125-p2-9-tested-seed/ACTUAL_SEED_FALLBACK_COMPOSITION.json`.
- Blob: `8e1a1609299f075c4c7e0310e8512d9cb9cabe28`.
- UTF-8 SHA256: `bd4fb843469bbad35d636018c802068e63cad5d133ba8279f75d6970672da3a6`.
- 4104 bytes; read back and compared byte for byte.

It preserves the same actual N, width, geometric mesh, fallback rho, original marks, full 2N prime tuple carrier, and all four right-hand fallback terms. It supplies no additional distribution or density hypothesis.
