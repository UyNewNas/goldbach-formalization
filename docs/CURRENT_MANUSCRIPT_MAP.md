# Current manuscript-to-Lean map

This checkpoint tracks the 10 October 2026 edition of *Imbalanced semiprime
representations of even integers* rather than the historical 8 October draft.

## Frozen source

- Manuscript repository: `UyNewNas/chen-imbalanced-semiprimes`
- Source commit: `ba6ec11d800eccc54406490631895e174de85766`
- Main body blob: `paper/source/manuscript-body.tex` at
  `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`
- Submitted PDF SHA-256 supplied for this run:
  `ef70ecef4b4c310449a43db1093859b5d3377e670d7c9dc9fa23619d7e54be9c`
- Constants: `K = 8452171/1250000`, `c = 49044063/25000000`

If the source commit changes, this map must be compared with the new theorem
statement before any later checkpoint is called current.

## Exact finite semantics

| Manuscript item | Lean interface | Status |
| --- | --- | --- |
| `eq:current-d12`, including `N-p > 1` | `Counting.D12` | Exact finite definition |
| `eq:current-db`, distinct additive primes | `Counting.Db`; `RationalPowers.RealDb`; `Db_eq_RealDb` | Exact for positive denominator |
| `eq:current-bb`, ordered bad factorization | `OrderedBad.badReceiver_iff_ordered_real_factors`; `CurrentMainTheorem.realBadReceiver_iff_realOrderedBadReceiver`; `RealB_eq_realOrderedBadPrimes_card` | Exact for rational and arbitrary real `b < 1`, including squares and strict endpoints |
| `sec:current-transfer`, finite ordered source and cutoff | `RealHalfProductSource.RealB_eq_realHalfProductSource_filter_card_add_small`; `realHalfProductPairs_card_eq` | Exact finite localization for arbitrary real `b < 1`; analytic pair-mass limit open |
| Rational minorant to the finite additive-prime sieve | `RealHalfProductSieveBridge.realHalfProductSource_primePartner_card_le_sifted_rat_add_cap`; `realHalfProductSource_primePartner_cast_le_optimized_of_rat_minorant`; `RealB_cast_le_optimized_of_rat_minorant` | Proved: for `num/den ≤ b`, the literal real source after `m < N ∧ Prime (N-m)` is bounded by the rational sifted source, retaining `+z` and `T+1`; the current physical-weight density/distribution estimates remain open |
| `eq:current-bad-mass`, `J_b = log (1/b)` | `RealHalfProductMass.realHalfProductMass_exponents`; `RealHalfProductMassSplit.manuscriptHalfProductCutoff`; `RealHalfProductMassSuppliers.tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers` | Exact arbitrary-real source envelope at the current `2 N^(1-κ₀)` lower wall; pinned proved PNT/Mertens suppliers are connected without analytic premises. The filtered additive-prime positive-sieve transfer remains open |
| `eq:current-exact-subtraction` | `D12_eq_Db_add_B`; `Db_cast_eq_D12_sub_B` | Proved finite identity |
| `eq:current-normalization` | `SingularSeries.singularNormalization` | Product convergence, positivity and growth proved |

The current manuscript excludes receiver one from `D_{1,2}`.  Therefore its
terminal transfer uses `D12`, not the historical `D12Omega` interface and not
the receiver-one absorption lemma.

## Current terminal constants and Corollary 1.2

`ImbalancedChen/CurrentNumericalTransfer.lean` proves:

- `current_gap_74816964`, `current_gap_74816865`, and `current_gap_09` by
  kernel-checked rational arithmetic and Mathlib's logarithm-series bound;
- one conditional eventual lower bound for each of the three current
  exponents; and
- `current_corollary_simultaneous_of_manuscript_bounds`, which chooses one
  natural threshold before all later even `N` and returns all three claimed
  inequalities simultaneously.

These results close the exact arithmetic and terminal quantifier assembly.
They do **not** close the analytic hypotheses supplied to that theorem.

## Current main-theorem statement

`ImbalancedChen/CurrentMainTheorem.lean` extends the exact finite partition to
every fixed real exponent through `RealBadReceiver`, `realBadPrimes`, and
`RealB`.  The identity `D12_eq_RealDb_add_RealB` counts each additive prime
once and makes no rationality assumption on `b`.  `B_eq_RealB` proves that at
every positive-denominator rational exponent this is exactly the pre-existing
integer-power count `B`, rather than a parallel convention.

`current_theorem_1_1_of_manuscript_bounds` then states the literal lower limit
through all even natural numbers, with `1/2 < b < 1` chosen first.  It uses an
`EReal` liminf so no artificial global boundedness assumption is added to the
normalized count.  Its two analytic estimates remain explicit hypotheses.

For the arbitrary-real range of Theorem 1.1,
`realBadReceiver_iff_realOrderedBadReceiver` identifies the complement with
the literal ordered region
`r ≤ q ∧ (q : ℝ) ^ b < (r : ℝ)`.  Its converse checks both orders of every
prime factorization; `realOrderedBadReceiver_factors_unique` retains prime
squares and proves that sorting adds no witness multiplicity.  Consequently
`RealB_eq_realOrderedBadPrimes_card` is the exact finite input expected by the
remaining ordered bad-semiprime mass estimate.

`ImbalancedChen/RealHalfProductSource.lean` now continues this bridge for an
arbitrary real exponent.  For every real cutoff `T` and `b < 1`,
`RealB_eq_realHalfProductSource_filter_card_add_small` partitions `RealB`
into the inclusive half-product source after the literal
`m < N ∧ Nat.Prime (N - m)` filter and the complementary receivers `m < T`.
The filter preserves the manuscript's strict upper endpoint even though the
ambient analytic source uses `m ≤ N`.  `realHalfProductPairs_card_eq` counts
the unique ordered pair, including prime squares, so this reindexing adds no
factor two and no witness multiplicity.

`ImbalancedChen/RealHalfProductMass.lean` additionally defines the literal
arbitrary-real split
`alpha = b/(1+b)`, `beta = 1/(1+b)`.  For every `0 < b < 1` it proves
`0 < alpha < 1/2`, `alpha < beta`, `alpha + beta = 1`, the low-prime wall
`q^b < r <= N^alpha -> q < N^beta`, and the high-prime wall
`N^alpha < r` together with `r*q <= N -> q^b < r`.  It also evaluates the
actual fixed-test integral on `(alpha,1/2]` as `log(1/b)` and converts an
explicit weighted-prime integral limit into this coefficient.  At rational
`b = num/den`, the exponents and literal weighted sum are proved equal to the
existing `HalfProductMassLimit` interfaces.

`ImbalancedChen/RealHalfProductMassSplit.lean` now projects the actual
arbitrary-real ordered-pair carrier onto its smaller prime and proves the exact
fibre sum.  It partitions that sum at `floor(N^alpha)`, pays the low part by
`pi(floor(N^alpha))*pi(floor(N^beta))`, and pays only `pi(sqrt N)^2` for the
high ordering loss.  The strict lower endpoint, inclusive square-root
endpoint and prime squares are preserved.  The current manuscript's literal
lower wall is formalized as `manuscriptHalfProductCutoff κ N = 2*N^(1-κ)`;
for every fixed `κ > 0`, its exact ceiling loss is proved `o(N/log N)`.
Using the repository's explicit real-PNT witness, the complete finite
difference at this power cutoff is proved `o(N/log N)` in epsilon-eventual
form.  Combining that result with the standard weighted-prime Mertens
integral yields the conditional full source limit `log(1/b)` for every fixed
`0 < b < 1`.  The older `logCutoff = N/(log N)^10` theorem is retained only
as an explicitly named historical auxiliary result, not as the displayed
cutoff of the current manuscript.

This closes finite reindexing, the real split algebra, the moving product
boundary and the normalized current power-cutoff error.  The new
`RealHalfProductMassSuppliers` adapter identifies the local prime interval
definitionally with the pinned weighted Mertens interval, instantiates the
pinned real PNT, and removes both analytic premises from the source-mass
limit.  It does not yet transport that source mass through the additive-prime
filter and the actual positive upper sieve.

`ImbalancedChen/RealHalfProductSieveBridge.lean` now proves the exact finite
transport that is available without claiming the manuscript's missing
analytic upper-weight theorem.  The ordered bad predicate and the real source
are antitone in the exponent.  At every positive-denominator rational
exponent, the arbitrary-real source is literally `halfProductSource`; hence a
rational minorant `num/den ≤ b` contains the real source at `b`, including
after the strict `m < N` and `Nat.Prime (N-m)` filter.  The resulting cardinal
is bounded by `siftedHalfProductSource + z`, and composing the existing finite
Selberg inequality leaves its primitive-residue discrepancy premise, exact
finite normalizer, `+z`, and cutoff loss `T+1` visible.  The convenience lemma
`RealB_le_B_of_rat_minorant` gives the corresponding whole-count monotonicity.

This bridge does not identify the repository's generic finite Selberg weight
with the manuscript's physical `rho_N`, and it does not produce the current
coefficient `K`.  The manuscript requires one and the same `rho_N` in its
pointwise nonnegative majorant, density bound and signed distribution theorem;
those three properties, followed by the licensed smooth outer approximation,
remain the actual filtered-source gap.

## Remaining proof obligations

1. Formalize the restricted moving-residue distribution estimate with the
   actual common interval and common additive phase.
2. Prove the current positive upper weight and its density, yielding the
   coefficient `K` for the same physical source.
3. Prove the complete eleven-term lower-weight mean and paired deletion,
   including all `Y11` endpoints and repeated-prime errors.
4. Connect the adopted 17,572-cell same-mask-v2 certificate and the `7/3`
   refinement to the analytic functions; the superseded `12/5` gain must not
   be added.
5. Close the ordered bad-semiprime asymptotic with mass
   `J_b = log (1/b)` and discharge the three explicit upper-bound hypotheses.
   The arbitrary-real finite ordered-source localization and unique pair count
   feeding this estimate are now proved.  Rational minorants now connect the
   real prime-partner filter to the existing finite rational sieve, retaining
   both finite corrections.  The exact real exponent split,
   moving-boundary source envelope, normalized cutoff error and conditional
   source mass limit are also proved.  The actual PNT/Mertens suppliers and
   the manuscript physical-weight density/distribution theorem and licensed
   smooth outer approximation are not.
6. Discharge the two explicit analytic hypotheses of
   `current_theorem_1_1_of_manuscript_bounds`.  The exact arbitrary-real-`b`
   partition and even-restricted liminf transfer are now formalized, but a
   conditional theorem or a zero-`sorry` finite core is not the complete
   manuscript proof.

The external `1.9728` lower coefficient belongs only to a withdrawn branch and
is not an input to the current theorem.

## External reuse audit (10 October 2026)

No checked repository currently supplies the complete arbitrary-real ordered
half-product mass theorem.  The closest exact reusable interface is
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`,
`MathlibNt/SieveTheory/Arithmetic/PrimeReciprocalLogScale.lean`:
`tendsto_primeReciprocalLogInterval` proves the genuine `Real.rpow` unweighted
interval mass `log (b / a)`.  The continuous weighted result needed here is
instead `tendsto_weightedPrimeReciprocalLogSum` in
`MathlibNt/SieveTheory/Arithmetic/MertensTheorem.lean`; its limit is the
literal integral of `f(x)/x`.  `RealHalfProductMass` now proves that the
repository's strict-left/inclusive-right high-prime sum is exactly this
standard interval shape at `a=b/(1+b)`, upper endpoint `1/2`, and
`f(u)=1/(1-u)`, and then evaluates its integral as `log(1/b)`.  Neither
external theorem supplies the moving product boundary, the half-product fibre
PNT step, the additive-prime filter, or the required uniform error.

The dependency pin matches this repository.  Its underlying PNT and Mertens
results come from
`UyNewNas/analytic-number-theory-lean@88ee563ba0021702ea370b13bae7c7e7fec59657`,
whose audit covers those declarations with the standard three axioms.
Directly importing the goldbach theorem would also pull its broad
`AnalyticNumberTheory`/sieve closure; importing both projects independently
risks duplicate roots.  Any reuse here must therefore be pinned, adapted and
re-audited transitively.  Pinned Mathlib and the checked zeta-23 source do not contain a
drop-in half-product theorem; no relevant open branch, PR, or issue supplied a
more complete result.

For the additive-prime upper-sieve step, a stronger reusable chain was found
in the same-pin repository
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`:

- `UpperRosserDensity.lean` proves the explicit `upperRosserWeight`, its
  pointwise upper certificate, strict level support and
  `abs_upperRosserWeight_le_one`;
- `LiLiuPanBoundedAggregate.lean` proves the unconditional bounded-coefficient
  coprime interval aggregate with logarithmic saving;
- `LiLiuGoldbachB9HighFirstDistribution.lean` supplies an almost identical
  divisor-count-to-Pan-error and Rosser-error assembly template; and
- `LiLiuGoldbachUpperDensitySix.lean` proves a generic dimension-one Rosser
  main-sum bound for an arbitrary `BoundingSieve` satisfying its displayed
  local-product condition.

This chain is a better next target than the repository's present
lambda-squared Selberg route: `|upperRosserWeight| ≤ 1` matches the unweighted
bounded-coefficient Pan aggregate and avoids demanding a `3^omega(d)` error
estimate.  It has not yet been imported or replayed in this target project.
The remaining adapter must still prove the half-product divisor-count identity,
coprimality-gate and endpoint corrections, multiplicity-one support, and the
exact local-product normalization with no extra factor two.  The older
`analytic-number-theory-lean` BV/Pan declarations have the wrong uniform
quantifier structure or are unproved `Prop` interfaces and are not accepted as
analytic suppliers; the checked zeta-23 sources contain no matching sieve/AP
distribution result.

### Half-product to Pan finite interface

`ImbalancedChen/HalfProductPanFinite.lean` supplies the exact missing first
adapter: the source predicate is transported through the unique ordered
factorization and grouped by the smaller prime `r`. The actual congruence mass
is therefore a sum of larger-prime counts satisfying `r*q ≡ N [MOD d]`, and
the actual primitive discrepancy is the sum of the corresponding fibre
discrepancies. No factor two is introduced and `r = q` remains present.

The checked upstream theorem
`liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving` in
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`
accepts one coefficient function `f` with `|f| ≤ 1` and sums its coprime
moving-residue interval errors over `d`. Its scale, interval endpoints and
logarithmic lower gate are explicit. The new prime-indicator theorem proves
the required coefficient bound at the finite-source level.

`ImbalancedChen/PanProductStrips.lean` now supplies the next exact adapter.
For `A₁ < r ≤ A₂` it identifies the literal strict-lower/closed-upper region
`Y₀ < r*q ≤ Y₁` with the difference of the closed prefixes at `Y₁` and `Y₀`.
It proves this for AP counts, coprime mass and discrepancy, normalizes each
moving fibre to `q ≤ Y/r`, and shows that a primitive target residue inserts
exactly the upstream `Coprime r d` gate while leaving the bounded coefficient
as the modulus-independent prime indicator. For an abstract prime-counting
main term, the strip error is proved equal to upper-prefix error minus
lower-prefix error, hence bounded by the sum of their absolute errors. These
are finite identities; they do not assert a Pan estimate.

`ImbalancedChen/PanProductResidueBudget.lean` and
`ImbalancedChen/PanProductLiuBridge.lean` now close the residue/interface part
of this adapter.  The physical target is reduced to `N mod d`, membership in
the supplier's canonical primitive family follows from the actual hypothesis
`Coprime d N`, and the literal prefix error is identified with the pinned
`liuMainPanCoprimeIntervalSum`.  Thus one strip is bounded pointwise by the
sum of the two endpoint `liuMainPanCoprimeIntervalMaxL` values.  No
coprimality with either moving product scale is assumed.

The exact prime-indicator specialization
`panProductPrimeIndicatorMaxL_boundedAggregate_log_saving` also imports the
unconditional logarithmic-saving aggregate and discharges its global
coefficient bound. Its scale hypotheses remain visible and must be supplied
twice, once at each product endpoint.

`ImbalancedChen/PanProductAggregateBudget.lean` now performs that two-endpoint
aggregation on the actual physical modulus set
`{d ∈ Icc 1 D | Coprime d N}`.  It proves this set lies in each endpoint's
full cutoff interval, enlarges the sum using literal `MaxL` nonnegativity, and
deduces a single logarithmic-saving bound for the absolute errors of the
strict-lower/closed-upper product strip.  No factor counting moduli or residue
classes is introduced, and coprimality remains with the fixed additive target.

`ImbalancedChen/PanProductGrid.lean` supplies the previously missing finite
coordinate system.  It sends a prime pair `(r,q)` to `(r,r*q)` and uses the
existing exact half-open multiplicative sides in those coordinates.  Each
cell is definitionally a `panProductStripPairs` with an open lower and closed
upper endpoint in both `r` and `r*q`.  Every actual source pair has a unique
selected cell, and distinct cells are disjoint at the pair level; prime
squares and ordered multiplicity are retained.  The selected union is only
an upper cover, not an equality with the curved source, because complete
strips also contain exterior points.  Projection to products must therefore
continue through `pairProductWeight` rather than erase pair multiplicity.

The same module now gives the simplification theorem
`mem_actualPanProductGridIndices`, the ambient-subset theorem
`actualPanProductGridIndices_subset`, and the finite summation budget
`actualPanProductGridIndices_card_le`.  Hence every selected index carries an
actual source-pair witness and the selected family has at most
`(floor (log N / log κ) + 1)^2` cells.  This is the dynamic Pan-grid budget;
it is not the separate 17,572-cell same-mask-v2 numerical certificate.

`ImbalancedChen/PanProductGridRanges.lean` supplies the first selected-cell
geometry needed by the Pan consumer.  For `1 < κ ≤ 2`, an actual source
witness in the cell proves the exact endpoint bounds
`T/2 - 1 < Y₀`, `Y₁ < 2N`, and `A₂ < 2 * sqrt N`, where the endpoints use
the same ceiling-minus-one convention as the strict-lower/closed-upper product
strip.  These bounds retain all rounding losses and do not claim that the full
cell lies in the curved source.  They also do not transfer the global modulus
cutoff to either product endpoint.

At the manuscript cutoff `T = 2*N^(1-κ₀)`, the same module now proves
`eventually_actualPanProductGridIndices_productEndpoints_ge`: for fixed
`0 < κ₀ < 1`, fixed `1 < κ ≤ 2`, and every fixed natural threshold `N₀`,
all selected cells eventually satisfy `N₀ ≤ Y₀` and `N₀ ≤ Y₁`
simultaneously.  This discharges exactly the two supplier-threshold hypotheses
of the Pan aggregate.  It does not by itself discharge any power, logarithmic,
or modulus-cutoff gate.

The manuscript's actual parameter condition
`κ₀ < κ/(4(1+κ))` with `κ > 0` is proved to imply `κ₀ < 1/4`.
Using this strict exponent gap, the module now also proves
`eventually_actualPanProductGridIndices_twoThirds_gates_of_manuscript`:
every selected cell eventually satisfies both
`A₂ ≤ Y₀^(2/3)` and `A₂ ≤ Y₁^(2/3)`.  The proof absorbs the full
`-1` product-endpoint rounding loss and the factor `2` in `A₂ < 2*sqrt N`;
it does not assume a fixed-proportion product endpoint.

The same source witness also gives the strict roughness inheritance
`(2*N^(1-κ₀))^(b/(1+b))/2 - 1 < A₁` for every selected product-coordinate
cell.  Combining this with the already proved fixed-logarithm estimate,
`logCutoff N ≤ N`, and `κ₀ < 1/4` yields
`eventually_actualPanProductGridIndices_log_gates_of_manuscript`: for the
supplier's fixed nonnegative real `B`, both exact endpoints satisfy
`log(Y₀)^(2B) ≤ A₁` and `log(Y₁)^(2B) ≤ A₁`, uniformly over the selected
family.  The real exponent is rounded to `ceil(2B)` only after the logarithmic
base is at least one; the grid's `ceil - 1` loss is retained throughout.

The 17,572 same-mask-v2 cells are **not** this half-product Pan grid.  They are
the separate fixed `(t,u)` cells in the eleven-term lower-weight numerical
certificate, where the `7/3` refinement improves the lower mean.  The Pan
geometry instead uses the now-defined dynamic `(r,m=r*q)` product-strip grid.
The next geometric adapter must prove, for its selected cells and separately
at `Y₀` and `Y₁`, the remaining upstream hypotheses
`D ≤ panModulusCutoff Y B`.  Once supplied, the new
aggregate adapter consumes those eight gates directly.  The existing
`(r,q)` rectangle grid gives useful global `4N` bounds, but mere containment
of a signed rectangle discrepancy in a larger product strip would not be a
valid transfer.  Gate loss must also be accounted for when the analytic main
term is compared with any ungated physical mass.

Dependency audit: `goldbach-lean` is pinned at
`09b97db5764ade1246bfb77206baa1b124760958`; it uses the identical Lean and
Mathlib pins and is the sole analytic-number-theory dependency.  Its inherited
`LeanArchitect` dependency is pinned at
`78dd66840d3efe8c824c699fc03381cec817c271`.  The separate
`analytic-number-theory-lean` package must not be added because both projects
export the `AnalyticNumberTheory` and `PrimeNumberTheoremAnd` module roots.

