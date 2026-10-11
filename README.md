# Imbalanced Chen formalization

Work toward a Lean formalization of *Transferring quantitative Chen bounds to imbalanced semiprime representations* (8 October 2026).

## Verification status

At commit `50c355b3260da1699447df805f0a58e74e4e465e`, the eighty-four-module checkpoint compiled, bundled `leanchecker` replayed every `ImbalancedChen.*` module and the root (85 targets), and the transitive axiom audit passed for 2043 declarations using only `propext`, `Classical.choice`, and `Quot.sound`. [Successful PR CI](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37880137858) and [same-head push CI](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37880133970) passed all three proof gates before optional cache handling. This verifies the stated lemmas and conditional transfers; the manuscript's main analytic theorem is **not formally verified**.

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
- `ImbalancedChen/LogCutoffError.lean`: proved negligible loss from the historical auxiliary cutoff `N / (log N)^10`, including the full ceiling error, composed with the retained prime-partner source; the current manuscript's power cutoff is handled separately below.
- `ImbalancedChen/HalfProductSource.lean`: exact inclusive half-product sieve source, unique ordered-pair counting including squares, and its prime-partner filter.
- `ImbalancedChen/RealHalfProductSource.lean`: arbitrary-real-exponent reindexing and cutoff localization of the current bad count, with exact prime-partner filtering and multiplicity-one ordered pairs.
- `ImbalancedChen/PowerErrorBudget.lean`: fixed sublinear power-logarithm errors and exact floor/ceiling losses are negligible in the genuine normalization.
- `ImbalancedChen/SieveSourceCoprimality.lean`: actual strict-cap sieve product, primitive congruence and rough-source coprimality, with explicit small-prime-partner correction.
- `ImbalancedChen/ActualSieveGate.lean`: the historical logarithmic auxiliary cutoff eventually clears the exact fifth-root sieve cap, discharging rough-source coprimality conditions.
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
- `ImbalancedChen/HalfProductPanFinite.lean`: exact arbitrary-cutoff decomposition of the actual congruence mass, coprime mass, bounding-sieve divisor sum and primitive discrepancy into smaller-prime moving-residue fibres; the prime-indicator coefficient is proved bounded by one.
- `ImbalancedChen/PanProductStrips.lean`: exact `A₁ < r ≤ A₂`, `Y₀ < r*q ≤ Y₁` product strips as differences of closed Pan prefixes, including the primitive outer coprimality gate, normalized endpoint `q ≤ Y/r`, bounded prime-indicator coefficient and upper-minus-lower prefix-error identity.
- `ImbalancedChen/PanProductResidueBudget.lean`: canonical reduction of the physical target to `N % d`, with selector-uniform prefix budgets and the exact two-prefix strip cost.
- `ImbalancedChen/PanProductLiuBridge.lean`: audited identification of the product-prefix error with the pinned Liu--Pan interval sum and pointwise control by its primitive-residue `MaxL`, including the two-endpoint strip bound.
- `ImbalancedChen/PanProductAggregateBudget.lean`: enlarges the actual coprime physical modulus set into both full nonnegative Liu--Pan cutoff aggregates and proves the two-endpoint logarithmic-saving bound for the literal product-strip error, while retaining all eight endpoint gates.
- `ImbalancedChen/PanProductGrid.lean`: constructs the required dynamic grid in exact `(r,m=r*q)` coordinates, identifies every cell with a strict-lower/closed-upper Pan strip, proves unique source-pair coverage and pairwise disjointness without dropping squares or ordered multiplicity, and exposes the selected-cell witness predicate and finite logarithmic cardinality budget needed for later error summation.
- `ImbalancedChen/PanProductGridRanges.lean`: transfers each selected cell's literal source witness to the exact dynamic-grid endpoints, proving `T/2-1 < Y₀`, `Y₁ < 2N`, and `A₂ < 2√N` with the full grid-width and integer-rounding losses visible; at the current cutoff it also proves that both product endpoints eventually clear every fixed Liu--Pan supplier threshold and satisfy both `A₂ ≤ Yᵢ^(2/3)` gates under the manuscript's licensed `κ₀` relation.
- `ImbalancedChen/MassLogIntegral.lean`: fixed-test continuity and exact logarithmic weight conversion, reusing the existing integral proof.
- `ImbalancedChen/HalfProductMassSplit.lean`: exact high/low prime rectangle and order-error envelope for the original source.
- `ImbalancedChen/UniformPrimeTail.lean`: uniform moving-endpoint and fixed-power consequences of the explicitly supplied real PNT.
- `ImbalancedChen/HalfProductMassError.lean`: negligible original-source approximation error, conditional only on that real PNT.
- `ImbalancedChen/HalfProductMassLimit.lean`: original cutoff-source mass limit from the explicit real PNT and literal fixed-test weighted-prime Mertens limit.
- `ImbalancedChen/RealHalfProductMassSuppliers.lean`: exact adapter to the pinned proved real PNT and weighted-prime Mertens theorems, yielding the current arbitrary-real manuscript-cutoff source mass limit without analytic premises.
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

## Verified product-modulus pooling

`ChenPooledQuotientAP.lean` proves that the full product modulus b*d recovers its allowed sieve divisor as gcd(b*d,P). With actual ordered-prime label uniqueness this gives exact multiplicity-one pooling within each original Upsilon 3–6 term, for arbitrary row-dependent divisor sets satisfying b*d <= Q. The secondary base-modulus error and both centre costs are retained separately; the existing fourth-divisor moment is also transferred to the proved squarefree pooled support. The four terms are not claimed jointly disjoint. The candidate passed the 76-module checkpoint above; no analytic AP bound is assumed or supplied.

## Verified active-row four-term assembly

`ChenQuotientBVFinite.lean` additionally pools the secondary base-modulus errors only over nonempty rows. This retains arbitrary unused rows, while the actual product cap forces each active multiplier below Q. All four original absolute remainder sums are bounded by 4[1+4(1+log(max(1,Q)))] times the primitive AP-error pool, plus the complete paid centre cost. No analytic error bound is assumed. This finite module passed the 77-module checkpoint above. Supplier-backed ordinary-BV consumers remain outside the owned core and have separate runtime verification.


## Verified quotient geometry, density transport and finite weighted mass

The following three owned-only modules passed the 80-module checkpoint above. The single geometry repair made natural successor positivity explicit; their mathematical statements and the verification gates were unchanged.

- `ImbalancedChen/ChenQuotientLevelGeometry.lean`: literal natural row level D_b = Q / b + 1, with d < D_b equivalent to b*d <= Q for b > 0; uniform moving-multiplier logarithmic profiles and eventual inclusion of every original Upsilon 3–6 multiplier in the global logarithmic square-root cap. The eventual threshold precedes the multiplier choice. Lower-parameter gates require an explicit fixed gap; no s >= 2 gate is asserted for the full sixth band.
- `ImbalancedChen/ChenQuotientDensityTransport.lean`: exact equality of the quotient and initial sieve prime products, reciprocal-totient densities, Euler products and local dimension products at the same strict real cutoff, retaining the constructor's coprimality gate. Support, total mass and remainders are not identified, and no new analytic normalization or dimension estimate is supplied.
- `ImbalancedChen/ChenQuotientMassFinite.lean`: finite bounded-weight replacement of the actual quotient masses AP(N,N,b) minus the centre-prime count, for arbitrary signed label-dependent coefficients bounded by a fixed C >= 0. Exact injective pooling gives C(4 E_Q + C_36), with E_Q the primitive AP-error pool and C_36 the full centre mass, without an outer-cardinality factor; the centre cost receives an unconditional polylogarithmic budget and eventual fixed-logarithmic-accuracy payment. The AP-error estimate remains explicit.

These are inputs to later sieve assembly with moving row levels and genuine weighted masses. They preserve all original bands and multiplicities. No foreign consumer enters the core root; no lower-sieve mean, evaluated weighted prime/pair main term, coefficient 1.8271, or complete Chen theorem is established by these additions.


## Verified prime-window corrections and moving-weight transport

The following three owned-only modules passed the 83-module checkpoint above. The harmonic endpoint repair made natural lambda types, negated-equality symmetry and the final reflexive inequality explicit. All mandatory proof gates remained unchanged; the successful push retry changed no code or workflow.

- `ImbalancedChen/ChenPrimeHarmonicFinite.lean`: exact finite correction from the original centre-masked prime window [A,U) with 1/(p-1) to the opposite half-open window (A,U] with 1/p. The centre-divisor mask, reciprocal shift and both possible endpoint atoms are paid explicitly; for N > 0, 2 <= A < U and |f| <= M with M >= 0, the total error is at most (2M log(N)/log(2) + 6M)/A. It supplies no analytic prime-sum limit.
- `ImbalancedChen/MovingWeightTransport.lean`: finite perturbation costs and transport under uniformly close coordinates on one fixed compact set, for a fixed continuous test and eventually bounded nonnegative carrier weights. The test may have either sign. Uniformity, compact membership and bounded total weight remain explicit; a fixed-profile limit is a separate premise when used to derive a moving-profile limit.
- `ImbalancedChen/ChenQuotientMovingWeight.lean`: a positively padded fixed interval contains both the actual quotient row parameter and its logarithmic profile uniformly over a fixed multiplier power range. The generic transport then applies without dropping prime or ordered-pair labels, with the nonnegative weighted-mass bound and any fixed-profile limit still explicit. No full-sixth-band s >= 2 gate is asserted.

Supplier-backed prime harmonic and moving-prime adapters remain outside the core root. These elementary interfaces do not evaluate an actual prime/pair main term, supply an upper/lower sieve, establish coefficient 1.8271, or complete the Chen theorem.


## Verified finite pair-harmonic geometry

`ImbalancedChen/ChenPairHarmonicFinite.lean` passed the 84-module checkpoint above. Its finite identities and bounds are covered by the complete root/module replay and 2043-declaration transitive axiom audit.

It identifies the literal sixth selector with its disjoint-band rectangle and the fifth selector with the strictly ordered part of the masked square. The fifth harmonic sum is exactly one half of the tensor square minus one half of its diagonal. Totient multiplicativity is used only for distinct prime labels; the artificial diagonal has denominator (p-1)^2. Separated-test factorization and exact logarithmic coordinates retain all centre masks and endpoints. For A >= 2 and a nonnegative diagonal test bound M, the full diagonal costs at most 8M/A and the half-square replacement error at most 4M/A.

These are finite identities for the harmonic main sums. They do not replace the original sifted Upsilon counts or prove a continuous-test prime-pair limit, an upper/lower sieve, coefficient 1.8271, or the full Chen theorem. Supplier-backed pair consumers remain separate from the owned root.


## Symmetric square-to-triangle integral candidate

`ImbalancedChen/SymmetricTriangleIntegral.lean` is the next owned-only addition, targeting an 85-module checkpoint and 86 root/module replay targets. Compilation, kernel replay and the transitive axiom audit are pending; the verified checkpoint remains 84 modules and 2043 declarations.

The candidate proves rectangular integration-order exchange for a continuous real kernel on a closed rectangle. For a continuous symmetric real kernel on a closed square, it proves that one half of the square integral equals the iterated lower-triangle integral. A more general version assumes integrability on the genuine square. All statements allow weak endpoint inequalities, signed kernels and nonzero diagonal values. The diagonal is null for Lebesgue product measure by the null-singleton property and Fubini; an integral identity is not assumed.

These analytic identities are separate from the finite prime-pair diagonal estimate. A manuscript application must supply continuity and symmetry of its full weighted integrand on the actual square, or continuity on the actual rectangle. This module does not supply a prime-pair limit, moving-kernel approximation, upper/lower sieve, coefficient 1.8271, or the full Chen theorem. No foreign consumer, existing proof body, dependency configuration or verification workflow changes in this addition.

## Arbitrary-real half-product mass coefficient candidate

`ImbalancedChen/RealHalfProductMass.lean` proves the exact split
`b/(1+b), 1/(1+b)` for every real `0 < b < 1`, both elementary prime-variable
walls, and the fixed-test integral `log(1/b)`. It also proves exact agreement
with the existing rational mass definitions, identifies the literal sum with
the standard strict-left/inclusive-right logarithmic prime interval, and exposes a weighted-prime
Mertens adapter whose premise ends at the integral rather than at the desired
bad-count theorem. The moving product-boundary source envelope and current
power-cutoff tail are handled by `RealHalfProductMassSplit`; the actual
PNT/Mertens suppliers are connected by `RealHalfProductMassSuppliers`, while
the additive-prime positive-upper-sieve transfer remains open. This candidate
alone does not complete the ordered bad-semiprime asymptotic.

## Arbitrary-real source mass-split candidate

`ImbalancedChen/RealHalfProductMassSplit.lean` proves the exact finite
high/low envelope for the literal arbitrary-real ordered source, including
the moving product boundary, strict power split, prime squares, square-root
endpoint and exact real cutoff ceiling. It instantiates the current
manuscript lower wall as `2*N^(1-κ)` and proves, for every fixed `κ > 0`, that
this wall plus the exact ceiling unit is `o(N/log N)`. With the repository's
explicit real-PNT witness it proves the full finite discrepancy at that
literal power cutoff is `o(N/log N)`, and with the standard weighted-prime
Mertens integral it derives the conditional source limit `log(1/b)`. The
historical logarithmic auxiliary cutoff remains available as a separately
named theorem. `RealHalfProductMassSuppliers` now discharges both analytic
premises from pinned proved theorems. The actual additive-prime upper-sieve
transfer remains open, so this is not yet the `RealB` bound or the
completed manuscript theorem.

## Arbitrary-real source to rational finite-sieve bridge candidate

`ImbalancedChen/RealHalfProductSieveBridge.lean` proves that the ordered bad
region and its literal finite source are antitone in the real exponent.  At a
positive-denominator rational exponent, that real source is definitionally the
existing natural-power `halfProductSource`.  Thus every rational minorant
`num/den ≤ b` bounds the arbitrary-real source at `b`, even after retaining
the exact `m < N ∧ Nat.Prime (N-m)` filter.

The bridge feeds this filtered count into the existing rational
`siftedHalfProductSource`, retaining the explicit small-prime-partner loss
`+z`.  Its optimized composition keeps the actual finite normalizer and the
unweighted primitive-residue discrepancy premise visible; the complete
`RealB` version also retains the exact cutoff loss `T+1`.  No density constant,
distribution estimate or final bad-count asymptotic is hidden in these
statements.  In particular, the existing generic finite Selberg bound has not
been identified with the manuscript's current physical positive weight and
does not by itself yield `K = 8452171/1250000`.

