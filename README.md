# Imbalanced Chen formalization

Work toward a Lean formalization of *Transferring quantitative Chen bounds to imbalanced semiprime representations* (8 October 2026).

## Verification status

At commit `af4eb77d48f9a13df138e566f5718a262face9ab`, the seventy-five-module checkpoint compiled, bundled `leanchecker` replayed every `ImbalancedChen.*` module and the root, and the transitive axiom audit passed for 1869 declarations using only `propext`, `Classical.choice`, and `Quot.sound`. [Successful CI](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37866504321). This verifies the stated lemmas and conditional transfers; the manuscript's main analytic theorem is **not formally verified**.

- `ImbalancedChen/Counting.lean`: prime-indexed finite representation sets, exact good/bad partition, subtraction and a conditional finite transfer lemma. The initial count excludes receiver 1; the separate Multiplicity module supplies the receiver-one correction.
- `ImbalancedChen/Constants.lean`: exact rational endpoint arithmetic and logarithmic inequalities, reusing mathlib's proved logarithm bound. This does not certify the integrals from which the quoted numbers originate.
- `ImbalancedChen/Multiplicity.lean`: exact multiplicity and receiver-one correction.
- `ImbalancedChen/AsymptoticTransfer.lean`: conditional epsilon transfer, with all analytic estimates explicit.
- `ImbalancedChen/RationalPowers.lean`: exact real-exponent equivalence and literal additive representation witnesses.
- `ImbalancedChen/OrderedBad.lean`: unique ordered prime factors and exact identification of the bad count.
- `ImbalancedChen/NumericalTransfer.lean`: numerical applications with explicit analytic lower/upper estimates.
- `ImbalancedChen/NormalizationGrowth.lean`: proved analytic growth of positive multiples of `N / (log N)^2`.
- `ImbalancedChen/SingularSeries.lean`: convergence and strict positivity of the manuscript's actual Euler product (without a leading factor two), finite correction, and normalization growth.
- `ImbalancedChen/ManuscriptTransfer.lean`: concrete-normalization conditional count and representation endpoints, removing the former growth premise while retaining both analytic count estimates.
- `ImbalancedChen/HalfProductGeometry.lean`: actual bad-factor roughness localization and the exact integral coefficient `log(1/b)`.
- `ImbalancedChen/BadSourceLocalization.lean`: exact bad-source reindexing, retained/discarded cutoff partition, and ceiling-correct real cutoff.
- `ImbalancedChen/LogCutoffError.lean`: proved negligible loss from the actual cutoff `N / (log N)^10`, including the full ceiling error, composed with the retained prime-partner source.
- `ImbalancedChen/HalfProductSource.lean`: exact inclusive half-product sieve source, unique ordered-pair counting including squares, and its prime-partner filter.
- `ImbalancedChen/PowerErrorBudget.lean`: fixed sublinear power-logarithm errors and exact floor/ceiling losses are negligible in the genuine normalization.
- `ImbalancedChen/SieveSourceCoprimality.lean`: actual strict-cap sieve product, primitive congruence and rough-source coprimality, with explicit small-prime-partner correction.
- `ImbalancedChen/ActualSieveGate.lean`: the original logarithmic cutoff eventually clears the exact fifth-root sieve cap, discharging rough-source coprimality conditions.
- `ImbalancedChen/FiniteSieveModel.lean`: genuine mathlib `BoundingSieve` on the actual shifted source, exact reciprocal-totient remainder, and finite upper-Möbius/λ² inequalities.
- `ImbalancedChen/TruncatedSieveLevel.lean`: exact level-squared truncation of the actual λ² main/error sums and a divisor-count coefficient bound.
- `ImbalancedChen/FiniteSieveEuler.lean`: exact finite Euler factorization with the explicit prime-two normalization, and actual Selberg terms on allowed squarefree divisors.
- `ImbalancedChen/CenterPrimeTail.lean`: exact center-prime correction tail, at most five omitted primes at the actual fifth-root cap, and uniform error at most `62 / N^(1/5)` for `N ≥ 1024`.
- `ImbalancedChen/EulerNormalizationLimit.lean`: genuine strict-cap product exhaustion, correction-tail ratios tending to one, and actual sieve-density normalization along positive even centers with the ordinary prime Euler product left explicit.
- `ImbalancedChen/SieveDimensionComparison.lean`: exact density quotients on half-open prime intervals and uniform comparison after excluding center divisors; no logarithmic dimension estimate is assumed.
- `ImbalancedChen/CurvedRegionDiscrepancy.lean`: exact finite discrepancy partitions and a full-carrier curved-boundary transfer with reciprocal-totient mass cost. This does not prove rectangle distribution or boundary lattice-point estimates.
- `ImbalancedChen/TotientReciprocalBudget.lean`: unconditional finite reciprocal-totient sum bound with explicit constant four, applied to the actual curved-boundary logarithmic mass cost.
- `ImbalancedChen/BoundaryGridBudget.lean`: four actual integer-pair collar bounds with explicit rounding and product-fibre multiplicities on a full carrier. Grid containment and rectangle distribution remain open.
- `ImbalancedChen/BoundaryCellContainment.lean`: genuine inside/outside cell witnesses imply all four collars with width `3δ`; includes exact ceiling endpoints and the derived smaller diagonal cap.
- `ImbalancedChen/BoundaryGlobalCaps.lean`: derives actual global ceiling caps from crossing cells and an explicit full-support boundary mass bound with all rounding terms.
- `ImbalancedChen/MultiplicativeGridPartition.lean`: exact finite half-open multiplicative grid, unique cell ownership, full exterior carrier and squared logarithmic rectangle count.
- `ImbalancedChen/ActualGridEnvelopes.lean`: literal full prime rectangles, exact lower/upper sandwich, boundary-fibre mass and source discrepancy bridge.
- `ImbalancedChen/BoundaryLogMesh.lean`: the full actual geometric boundary cost is negligible for logarithmic mesh exponent k > 4, uniformly in cutoff and modulus cap.
- `ImbalancedChen/RectangleDiscrepancyAssembly.lean`: exact actual rectangle discrepancy sum and full explicit boundary cost.
- `ImbalancedChen/CoprimeRecentering.lean`: exact reduced-residue partition and arbitrary common-main cancellation, yielding a factor-two error transfer.
- `ImbalancedChen/LogMeshGridCount.lean`: explicit polylogarithmic count of the complete grid and selected families, including final cells.
- `ImbalancedChen/SelectedGridRanges.lean`: exact selected rectangle endpoints and eventual fixed-log lower gates, uniform over all selected cells.
- `ImbalancedChen/CurvedDiscrepancyReduction.lean`: full actual curved discrepancy reduces to literal rectangle discrepancies plus an arbitrarily small normalized boundary remainder.
- `ImbalancedChen/PrimeRectanglePrefixes.lean`: exact full rectangle prefix subtraction, prime-indicator form and literal coprime recentering identities.
- `ImbalancedChen/ResidueSelectorBudget.lean`: finite maximizing residue selectors and factor-two recentering of a selector-uniform sum budget, with no modulus-count loss.
- `ImbalancedChen/RectanglePrefixBudget.lean`: actual full-rectangle discrepancy budget from two explicit selector-uniform prefix budgets, with cost 2Bhi + 2Blo and no modulus-count loss.
- `ImbalancedChen/ScaledRectangleBudget.lean`: fixed N-to-4N modulus-cap transfer with literal floor, and full polylogarithmic cell-count/recentering budget absorption.
- `ImbalancedChen/WeightedSieveError.lean`: actual progression caps and finite Cauchy transfer to the genuine lambda-square sieve error, retaining primitive modulus support.
- `ImbalancedChen/DivisorMomentBudget.lean`: unconditional squarefree fourth-divisor moment bounded by an explicit sixteenth logarithmic power, via finite Dirichlet convolution.
- `ImbalancedChen/BoundaryArbitraryLog.lean`: arbitrary fixed logarithmic accuracy for the actual geometric boundary cost, uniform in cutoff and selected moduli.
- `ImbalancedChen/WeightedSieveLogBudget.lean`: explicit logarithmic precision loss when transferring an unweighted primitive discrepancy estimate to the actual weighted sieve error.
- `ImbalancedChen/ActualSelbergCoefficients.lean`: explicit actual finite weights, support, normalization and coefficient bound by a proved positive injection.
- `ImbalancedChen/ActualSelbergMain.lean`: Mobius cancellation and exact optimized lambda-square main term 1/G.
- `ImbalancedChen/ActualOptimizedSieveBound.lean`: actual sifted count bound with the finite normalizer and literal primitive discrepancy.
- `ImbalancedChen/FullNormalizerCarrier.lean`: exact full squarefree, centre-coprime carrier at strict cap L+1.
- `ImbalancedChen/EnlargedSelbergCap.lean`: actual level, roughness, and negligible discarded-count gates for the enlarged cap.
- `ImbalancedChen/SingularProductIdentity.lean`: genuinely convergent natural-index Euler products, exact centre correction and the prime-two factor.
- `ImbalancedChen/HalfProductMassFibres.lean`: exact prime-counting fibres of the original half-product source, preserving strict power boundaries, squares and the real cutoff.
- `ImbalancedChen/MassLogIntegral.lean`: fixed-test continuity and exact logarithmic weight conversion, reusing the existing integral proof.
- `ImbalancedChen/HalfProductMassSplit.lean`: exact high/low prime rectangle and order-error envelope for the original source.
- `ImbalancedChen/UniformPrimeTail.lean`: uniform moving-endpoint and fixed-power consequences of the explicitly supplied real PNT.
- `ImbalancedChen/HalfProductMassError.lean`: negligible original-source approximation error, conditional only on that real PNT.
- `ImbalancedChen/HalfProductMassLimit.lean`: original cutoff-source mass limit from the explicit real PNT and literal fixed-test weighted-prime Mertens limit.
- `docs/PROOF_STATUS.md`: outstanding analytic dependencies and the frontier comparison.

Build: `lake exe cache get && lake build`. The workflow also runs `leanchecker` and a transitive axiom audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

No custom analytic axioms or proof placeholders belong in the verified core. A green core build is not a complete proof of the manuscript or a claim of a new frontier record.

- `ImbalancedChen/QuotientChenFourPrime.lean`: actual squarefree four-prime quotient roughness is equivalent to selecting the smallest two prime factors; literal Y10 and full Y11 support retain all strict endpoints.
- `ImbalancedChen/QuotientChenFourCounts.lean`: exact tuple-image bijections prove Y10 = choose(r−2,2) and full Y11 = (r−2)(s−r), with r,s the actual prime-divisor counts.
- `ImbalancedChen/RoughSquareException.lean`: actual positive integers at most N with a prime square divisor p², p≥z, have cardinality at most N/(z−1) for z>1, with no per-prime floor loss.

- `ImbalancedChen/QuotientChenInitialCounts.lean`: literal first-six quotient supports and actual finite count identities, including the unit receiver and exact second-prime band.
- `ImbalancedChen/QuotientChenSwitchGeometry.lean`: constructs the actual smallest prime pair and a third divisor, proves the strict square-root switching cap, and counts the genuine Y7/Y8 supports as indicators.

- `ImbalancedChen/QuotientChenNinthSwitch.lean`: literal Y9 support and its required lower bound from original squarefree source conditions and actual factor counts; four-factor exclusion and triple reconstruction are proved.

- `ImbalancedChen/QuotientChenWeightCases.lean`: complete actual repaired eleven-term pointwise weight inequality on the original squarefree size band, with exact fixed exponents, full Y11, multiplicity-count convention, and receiver one. This finite inequality supplies no analytic mean estimate.

- `ImbalancedChen/QuotientChenPositiveBound.lean`: uniform upper bound 246 for the actual weight on all positive receivers at most N, including nonsquarefree receivers.
- `ImbalancedChen/QuotientChenSummedBridge.lean`: original prime-indexed weight sum, once-only exceptional union, literal ceiling and square-divisor error, and explicit 984 N^(1-a) loss.
- `ImbalancedChen/QuotientChenElevenSum.lean`: exact eleven actual Upsilon sums, full Y11, manuscript endpoint equivalence, and explicit receiver-one correction.

- `ImbalancedChen/ChenWeightErrorBudget.lean`: proved eventual size gate and absorption of the exact 984 N^(1-a)+4 loss in the actual singular normalization, followed by a conditional transfer retaining the lower mean estimate on all eleven literal Upsilon terms.

- `ImbalancedChen/ChenInitialPrimeSource.lean`: actual initial additive-prime BoundingSieve, exact Upsilon1/2 sifted counts with strict real caps, literal prime AP fibres and both centre-prime/modulus-prime remainder corrections. No analytic lower sieve is assumed or proved.

- `ImbalancedChen/ChenInitialCorrectionBudget.lean`: explicit logarithmic prime-divisor bounds and complete centre/modulus-prime correction payment below the square-root level, at arbitrary fixed logarithmic accuracy; the literal ordinary prime-AP budget remains an explicit input.

- `ImbalancedChen/ChenLogLevelGeometry.lean`: literal floor-valued logarithmic distribution cap, strict Rosser level Q+1, limiting logarithmic ratios, and one common threshold for the numerical lower-sieve gates. Verified in the seventy-two-module checkpoint.

## Reproducibility

Lean and mathlib revisions are pinned in `lean-toolchain` and `lakefile.toml`. The attachment reviewed has SHA-256 `e89d35f219acfbc6018db56b99d7a5c6c70eeeba0a98723fbe1046041ca90fbe`. The companion certificate archive and all 249 payload hashes were preserved and verified. Nine numerical replays, including the full 2,000,000-split extended run, reproduce the stored mathematical results. This confirms numerical reproducibility, not the analytic interpretation or a Lean proof of the certificates. The extended run establishes an upper endpoint below 6.81, not below 6.809; the final 6.786 recombination additionally uses all three disjoint quoted gains.

- `ImbalancedChen/CenterEulerTail.lean`: strict real-cutoff centre Euler correction, explicit uniform exponential tail bound, and tail/relative-normalization convergence at every fixed positive real-power cutoff. Verified in the seventy-two-module checkpoint; no Mertens estimate is assumed.

## Verified quotient source and finite sieve remainders

`ChenQuotientPrimeSource.lean` passed the 73-module checkpoint above. It identifies the actual quotient receivers for selected multipliers with prime AP fibres at modulus `b*d`, retaining centre-prime corrections, repeated factors, quotient one, strict endpoints and the original Upsilon 3–6 outer multiplicities.

The new `ChenQuotientSieveRemainders.lean` constructs the genuine quotient `BoundingSieve`, proves the selected multiplier is coprime to the strict sieve product, and transfers its exact remainder to ordinary prime-AP errors plus both explicit centre correction costs. The reciprocal-totient density is justified only on proved allowed divisors. This extension passed the 74-module checkpoint above. No analytic bound for the selected-multiplier error sums or the full eleven-term mean is supplied.

## Verified pooled centre correction budget

`ChenQuotientCentreBudget.lean` pools the actual selected-multiplier centre-prime incidences before bounding them. For all four literal Upsilon 3–6 selectors and arbitrary row-dependent positive divisor sets capped by sqrt(N), the complete positive correction cost is at most 8/(log 2)^3 times sqrt(N) log(N)^3 for sufficiently large even N. The candidate derives arbitrary fixed logarithmic accuracy without a prime-distribution premise. It retains both centre counts, all outer labels and strict bands; only this correction cost is estimated. This extension passed the 75-module checkpoint above.

## Product-modulus pooling awaiting CI

`ChenPooledQuotientAP.lean` proves that the full product modulus b*d recovers its allowed sieve divisor as gcd(b*d,P). With actual ordered-prime label uniqueness this gives exact multiplicity-one pooling within each original Upsilon 3–6 term, for arbitrary row-dependent divisor sets satisfying b*d <= Q. The secondary base-modulus error and both centre costs are retained separately; the existing fourth-divisor moment is also transferred to the proved squarefree pooled support. The four terms are not claimed jointly disjoint. Compilation, kernel replay and axiom audit of this candidate are pending, and no analytic AP bound is assumed or supplied.
