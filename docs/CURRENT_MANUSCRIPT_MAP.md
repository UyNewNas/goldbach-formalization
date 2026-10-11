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

The full descending actual prime carrier is now proved equal to the rough
carrier `[w,z)` followed by the small carrier below `w`. Exact leaf
substitution preserves each rough leaf's selected history, sign and mass.
Its correction is nonnegative for odd first exits and nonpositive for even
first exits. Consequently the same fixed upper density satisfies
`V(w)*rough <= full`, and the same fixed lower density satisfies
`full <= V(w)*rough`. These are proved inequalities, not an assumed
factorization of signed densities.

`ActualLowerSmallRoughAttachment` supplies one actual lower physical rho,
using beta-minus on positive rough coefficients and beta-plus on negative
ones. It has a true all-integer minorant, squarefree target-coprime support,
unit coefficient bound and strict active small-factor level. Its actual
density loss is bounded by the actual absolute rough mass.
`ActualLowerNormalizedRhoError` chooses the precision before the common
target threshold and absorbs that loss at `eta*C_N/log N`.
`ActualLowerFirstExitDensityProjection` proves the same rho's density is
at least the full raw-policy density minus the reserve, and bundles this
with its all-integer minorant and unit bound. The upper counterpart is
proved in `ActualFirstExitDensityProjection`. Neither comparison yet
evaluates the manuscript's full causal-policy density.

`ActualRosserResidualDensity` transfers the ordinary compact theorem to
`(beta,u)` and then to actual residual levels `N^lambda/P` and cutoffs `y`.
Its one threshold is chosen before `N,P,y,lambda,cap`; positivity and fixed
compact membership are the explicit legal parameter conditions.
`ActualRosserPrefixDeletion` proves that a selected prime prefix above the
strict residual cutoff needs no further deletion: residual moduli are
coprime to its product, and the prime carrier, Rosser coefficients, Euler
product and densities are unchanged by explicitly excluding that prefix.

`ActualRosserInitialResidualSaving` identifies the canonical upper factor
on `1<s<=3` by uniqueness of two proved limits of the same actual density.
It proves a uniform `4/beta` limit and the signed difference for two actual
residual levels `N^lambda/P`. A positive saving still requires the new cap
to exceed the old cap. No prefix mass or certified integral is implicit.

`FirstExitDepthSplice` proves that changing the policy after a retained
rank changes the root polynomial by the sum of the new-minus-old
continuations over the same parent frontier. It preserves the admission
test at that rank. It therefore does not yet implement a change to that
rank's own cube test, as required by the lower fourth-prefix restoration.
`FirstExitValidSelection` gives both directions of
the selected-sublist/support correspondence.
`OrdinaryRosserFirstExitPolicy` identifies a full-prefix ordinary policy
with the actual Rosser coefficients and density at the same real level.
It also proves a globally parity-safe version, with inactive parity always
retained. The lower version pays the first-prime level condition explicitly
(`y<=R` on the actual carrier). This is a root ordinary-weight dictionary,
not yet the required history-dependent causal residual identity.

The next finite connection must prove that a valid nonempty prefix with
product `P` leaves an ordinary continuation at the real level `Q/P`, with
the exit parity flipped exactly when the prefix rank is odd. It must also
derive the actual frontier's mass, sign and remaining strict prime carrier.
The upper fourth-rank change acts after the retained fourth rank. The
upper fifth-rank own-cube change must instead enumerate candidates from
the common fourth-rank frontier and retain both old and new admission
indicators; otherwise restored old exits are lost. The lower fourth-rank
own-cube restoration similarly starts from rank-three candidates. These
are still unproved connections, ahead of the box integrals and certificates.

The preceding extension proves the same raw upper and lower Rosser density
ratios uniformly on every compact set of `(u,s)` with `u>0,s>1` and
`u>0,s>=2`, respectively. `ActualRosserCompactLimits` supplies one natural
threshold before both parameters and every covering cap. The limits are
the canonical Suzuki continuous factors; all coefficients retain the
literal natural-ceiling level and target-prime exclusions. The actual
finite box neighborhoods and compact all-depth error are both proved.
`ActualRosserCompactNormalization` supplies the corresponding uniform
limits after multiplication by `log N/C_N`, equal to
`(2*exp(-gamma)/u)` times the respective canonical factor. The cap may
depend on the target and parameter, with eventual simultaneous coverage.
The ordinary raw-density uniformity gap is therefore closed for these
factors. Global equivalence to any separately defined classical function,
the boxed policy/compiler, sharp signed density and main theorem are
separate obligations.

### Earlier fixed-parameter specializations

The earlier analytic extension proves the same raw upper Rosser density
limit for every fixed `u>0`, `beta>0`, `beta<=3*u`, along positive even
targets and for any eventually covering enumeration cap:

```text
actualSmallRosserPlusDensity N cap (N^u) (N^(3*u))
  / actualSmallEulerProduct N cap (N^u)
    -> 2*exp(gamma)/3;

actualSmallRosserPlusDensity N cap (N^u) (N^beta)
  / actualSmallEulerProduct N cap (N^u)
    -> 2*exp(gamma)*u/beta;

actualSmallRosserPlusDensity N cap (N^u) (N^beta)
  * log N / singularSeries N -> 4/beta.
```

The lower direction combines true finite prime-box contributions in one
positive boundary expansion, counting the base term one once. Strict
pair-removal geometry and measure-preserving Fubini identify every actual
odd-region integral with its pinned boundary mass and Suzuki source layer.
The proved continuous series then selects a finite prefix before the
actual N threshold. The upper direction uses the proved all-depth estimate
at the literal `ceil (N^(3*u))`, a target-uniform local product bound and
error absorption uniform in the carrier's adaptive odd depth. Both bounds
concern the same coefficient and Euler product, with no new analytic
premises. Their common threshold is uniform in every covering cap.

The exact coefficientwise cube reduction and the target-deleted Euler
ratio extend the result from residual three to `beta<=3*u`. This proves
the upper identity in manuscript `eq:current-raw-density` for every fixed
`1<s<=3`, `s=beta/u`, with the correct Mertens normalization. It does not
by itself prove compact-parameter uniformity or the lower-weight identity.
Those ordinary density results have since been extended as stated above.
The causal boxed compiler, current Chen mean, sharp bad-semiprime estimate
and final main theorem remain open.

| Manuscript item | Lean interface | Status |
| --- | --- | --- |
| `eq:current-d12`, including `N-p > 1` | `Counting.D12` | Exact finite definition |
| `eq:current-db`, distinct additive primes | `Counting.Db`; `RationalPowers.RealDb`; `Db_eq_RealDb` | Exact for positive denominator |
| `eq:current-bb`, ordered bad factorization | `OrderedBad.badReceiver_iff_ordered_real_factors`; `CurrentMainTheorem.realBadReceiver_iff_realOrderedBadReceiver`; `RealB_eq_realOrderedBadPrimes_card` | Exact for rational and arbitrary real `b < 1`, including squares and strict endpoints |
| `sec:current-transfer`, finite ordered source and cutoff | `RealHalfProductSource.RealB_eq_realHalfProductSource_filter_card_add_small`; `realHalfProductPairs_card_eq` | Exact finite localization for arbitrary real `b < 1`; analytic pair-mass limit open |
| Rational minorant to the finite additive-prime sieve | `RealHalfProductSieveBridge.realHalfProductSource_primePartner_card_le_sifted_rat_add_cap`; `realHalfProductSource_primePartner_cast_le_optimized_of_rat_minorant`; `RealB_cast_le_optimized_of_rat_minorant` | Proved: for `num/den ≤ b`, the literal real source after `m < N ∧ Prime (N-m)` is bounded by the rational sifted source, retaining `+z` and `T+1`; the current physical-weight density/distribution estimates remain open |
| `sec:current-positive-majorant`, odd-first-exit raw tree, sign-sensitive small/rough attachment and one physical `ρ_N` | `FirstExitTree.oddFirstExitRetainedPolynomial_eq_product_add_exits`; `RetainedModuli.oddFirstExitRetainedLeaves_sum_eq_retainedModuli_sum`; `RoughPrimeUniverse.roughPrimeRetainedLeaves_sum_eq_retainedModuli_sum`; `RoughPrimeUniverse.manuscriptRoughIndicator_le_oddFirstExitRetainedPolynomial`; `SignSensitiveAttachment.productTarget_le_signSensitiveAttachment`; `SmallRoughAttachment.smallRough_factorization_unique`; `SmallRoughAttachment.signSensitiveAttachment_eq_smallRough_physicalDivisorSum`; `SmallRoughAttachment.sum_smallRoughRho_mul`; `SmallRoughMainTerm.physicalDensitySum_smallRoughRho_eq_signSensitive`; `SmallRoughMainTerm.physicalCoprimeCorrection_smallRoughRho_eq_pairSum`; `SmallRoughMainTerm.physicalDistributionError_smallRoughRho_eq_pairSum`; `PhysicalUpperWeightBridge.siftedHalfProductSource_card_le_same_rho_main_add_errors` | Generic first-exit identity, source leaf-list `Nodup`, natural-modulus coefficient lookup and multiplicity-preserving modulus reindex proved; the rough universe is the strictly decreasing finite list of literal primes `p ∤ N`, `w ≤ p < z`, with exact real endpoints. The strict `p<w`/inclusive `w≤p` split gives cross-coprimality and unique small/rough products. The pre-existing pointwise `signSensitiveAttachment` is now literally the divisor sum of the same total physical `rho`; scalar and rho-weighted physical sums reindex without a fibre factor, and occupied coefficients retain the unit bound. The same physical rho's reciprocal-totient density is now exactly factored with the sign-dependent upper/lower small density, and both exact error terms are reindexed to the same carrier. The literal small weights and their fundamental-lemma density are now instantiated in the modules below. Absolute rough-mass control and the small-weight attachment reserve are now proved below. The actual causal boxed policy, sharp signed density bounds giving `K`, and signed distribution estimate remain open |
| `eq:current-bad-mass`, `J_b = log (1/b)` | `RealHalfProductMass.realHalfProductMass_exponents`; `RealHalfProductMassSplit.manuscriptHalfProductCutoff`; `RealHalfProductMassSuppliers.tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers` | Exact arbitrary-real source envelope at the current `2 N^(1-κ₀)` lower wall; pinned proved PNT/Mertens suppliers are connected without analytic premises. The filtered additive-prime positive-sieve transfer remains open |
| `eq:current-exact-subtraction` | `D12_eq_Db_add_B`; `Db_cast_eq_D12_sub_B` | Proved finite identity |
| `eq:current-normalization` | `SingularSeries.singularNormalization` | Product convergence, positivity and growth proved |
| `lem:current-full-weight`, current cutoffs and full last range | `CurrentChenPointwise.currentChenElevenWeight_le_four_indicator` | Literal eleven-term quotient counts, with `a=417/5000`, `h=19/125`, `d=59/250`; proved for every squarefree `n ≤ N`, `N ≥ 1`, without the historical lower receiver-size band |
| `lem:current-paired-injection`, same pair region on both terms | `CurrentChenPairedDeletion.chenY11Selected_le_chenY6Selected`; `currentChenPairedWeight_le_four_indicator` | Last-pair projection is injective on actual four-prime quotient tuples; the first pair is proved to be the unique smallest pair. Arbitrary same-region selection, including the current mask pullback, preserves the pointwise bound |
| `eq:current-weight-to-count`, squareful receivers and unit | `CurrentChenSummedBridge.currentChenPairedPrimeSum_le_four_D12_add_error`; `eventually_currentChenPairedPrimeSum_sub_normalized_error_le_four_D12` | Actual additive-prime sum, without witness multiplicity, bounded by `4 D12 + 246 N/(N^a-1) + 4`; the loss is negligible uniformly in the pair selector. The mean estimate of this actual weight remains open |

`FixedRoughCoefficients` proves that the retained prime selections and
support are independent of the local test function. Its fixed coefficient
majorizes the literal rough indicator on every integer. `ActualSmallRosser`
provides the literal target-prime-deleted lower and upper small weights,
their all-integer sandwich via `gcd(M, |n|)`, one-bounds and strict active
level. `ActualSmallRoughAttachment` then constructs one actual physical
coefficient with the full pointwise majorant, squarefree target-coprime
support and coefficient bound; the retention policy is still a parameter.
`ActualSmallRosserDensity` supplies the same weights' density from the
proved fundamental lemma, discharging the progression-density and uniform
dimension assumptions. `SmallRoughDensityError` propagates the explicit
small error to the same physical coefficient with the necessary absolute
rough-mass multiplier. `RoughAbsoluteDensity` now bounds that multiplier by
an exact finite Euler product and a proved uniform logarithmic interval
estimate. `RoughPowerParameters` specializes it to
`w=D^(epsilon^2)`, `z=D^r`, with the precise factor
`(r/epsilon^2)*(1+Krough/(epsilon^2*log D))`.
`ActualSmallRoughErrorAbsorption` proves that for every `r>0` and `eta>0`
there are `0<epsilon<1/8`, `epsilon^2<=r` and one `D0>=2` such that for all
`D>=D0`, even targets, finite caps and fixed rough policies,

`0 <= density(rho) - V * signedRoughDensity <= eta * V`.

Here `V` is the literal small-prime Euler product and `rho` is the same
physical coefficient already used in the pointwise majorant. The choice
of epsilon precedes the large threshold; a fixed-epsilon error is not
incorrectly called little-o. The bound is valid for truncated caps; using
the full-interval pointwise majorant separately still requires `z<=cap`.

`RosserEndpointBridge` also identifies the literal small coefficients and
densities with the natural-level Goldbach sieve at `Nat.ceil R`, retaining
strict tests at integral R. It does not replace that level by
`Nat.floor R + 1`. These results do not instantiate the current boxed
policy, prove the same-weight fixed-rank reverse limits, or establish the
sharp signed density constant.

`ActualSmallEulerNormalization` now proves the scale conversion from
`V(w)` to `C_N/log D`: the full small product is at most `B*C_N/log w`
for every positive even target, `w>=4` and cap covering `w`, with one
positive constant before all targets and caps. The proof uses the exact
finite Euler factorization, bounds the finite odd-prime product by one and
the below-cap target correction by the full correction, and supplies the
ordinary product bound from the pinned Mertens theorem at the inclusive
endpoint `ceil w - 1`. No target-prime tail limit is assumed.

`NormalizedSmallRosserError` directly absorbs the resulting
`epsilon^(-4)*exp(-1/epsilon)` cost while also requiring epsilon to be below
any earlier positive upper bound. It does not select a tolerance depending
on an already-chosen epsilon. `ActualNormalizedRhoError` applies these
proved suppliers to the same physical coefficient and establishes

`0 <= density(rho) - V*signedRoughDensity <= eta*C_N/log D`.

For fixed `nu>0` it then sets `D=N^nu`, selects the earlier tolerance as
`eta*nu`, and proves the target-scale version with one natural threshold:

`0 <= density(rho) - V*signedRoughDensity <= eta*C_N/log N`.

The real-D theorem needs only a cap covering `w` and may use a truncated
rough carrier. The target-scale theorem requires a cap covering the full
`z=N^(nu*r)`, allowing the existing complete-interval majorant to be used.
Both theorems choose epsilon and the threshold before the varying positive
even target, cap and retained policy. They concern the actual coefficient
built from the fixed raw retained support, not a yet-unproved identification
with the manuscript's finite boxed compiler. The signed rough main term,
causal policy, compiler and sharp K still require their separate proofs.

`UpperRosserCubeCarrier` proves that every prime factor of a nonzero upper
coefficient satisfies the strict first-prefix test `p^3<R`. It follows that
removing all other carrier primes leaves the entire arithmetic function and
every weighted divisor sum unchanged. `PrimeCubeCutoff` identifies that
filtered actual carrier with the cutoff `min(y,R^(1/3))`, including equality
at the excluded boundary. `ActualRosserCubeReduction` transfers these
identities to the actual upper coefficient, reciprocal-totient density and
divisor polynomial on every integer. These finite results allow truncated
enumeration caps and do not assert an asymptotic.

For `D>1` and `beta<=3*u`, the reduced cutoff is exactly `D^(beta/3)`.
When `beta>0` its logarithmic sieve coordinate is three. The actual upper
density divided by `V_N(D^u)` factors exactly into the reduced density
divided by `V_N(D^(beta/3))` and the ratio of the two Euler products.

`FullPowerEulerNormalization` supplies the full leading Euler constant for
each fixed positive real exponent, using the strict natural endpoint
`ceil(N^a)-1` in the proved Mertens theorem and the proved target-prime tail:

`V_N(N^a)*log N/C_N -> 2*exp(-gamma)/a`.

For any two fixed positive exponents it also gives
`V_N(N^a)/V_N(N^b) -> b/a`, along positive even targets. Here V is the full
prime product (`finiteSieveDensity N (ceil(N^a))`). Applying it to an actual
enumeration cap requires that cap to cover the cutoff; the earlier exact
finite product bridge supplies this identification. These statements are
fixed-exponent limits; the next module supplies their parameter uniformity.
At `D=N`, `a=beta/3` and `b=u`, the Euler factor in the cube reduction thus
has limit `3*u/beta`. The other factor's same-raw-weight limit at coordinate
three remains unproved. Neither the finite identity nor the Mertens limit
turns the available one-sided sieve estimates into equality with F(s).

`UniformPowerEulerNormalization` uses antitonicity in the exponent and
continuity of `2*exp(-gamma)/a` to prove locally uniform convergence on
`a>0`, then uniform convergence on each interval `[a0,a1]` with `a0>0`.
It does not assume that the finite prime products are continuous. The
actual-carrier version gives one `N0>=2` before every later even N, every
exponent in the interval, and every cap covering `N^a`. The moving-exponent
corollaries allow `alpha(N)->a>0` and an eventually covering cap depending
on N. This supplies the Euler normalization uniformity needed for compact
logarithmic cells; it does not supply the raw Rosser boundary-layer masses.

`ActualPrimeReciprocalMass` supplies the genuine single-prime cell mass:

`sum_(N^a<=p<N^b, prime p, p not dividing N) 1/(p-1) -> log(b/a)`

for every fixed `0<a<b`, along all natural targets tending to infinity.
Its enumeration cap is `ceil(N^b)` independently of the target N, so b may
exceed one. The exact change to the proved opposite-half-open Mertens
interval costs at most `2*log N/(N^a*log 2)+6/N^a`; the target-prime deletion,
denominator shift and both endpoint atoms are all paid before taking the
limit. Nonnegative layers permit finite-prefix lower bounds; no unproved
vanishing normalized tail is needed for that lower-bound route.

`ActualPrimeEulerSplit` partitions the same finite carrier at a boundary
prime q into primes below q, q itself and primes above q. The lower factor
is exactly `V_N(q)` with strict cutoff, for any enumeration cap.
`ActualRosserBoundaryExpansion` identifies the actual upper coefficient's
divisor density with the same subset density at `ceil R`, and proves the
exact expansion

`U_N(y,R)/V_N(y) = 1 + sum_q sum_s (nu(q)*prod_(p in s) nu(p))*V_N(q)/V_N(y)`.

Here `nu(p)=1/(p-1)` and s runs over the actual first-boundary sets above q.
All terms are proved nonnegative for even targets, so any actual subset
gives a lower bound. The carrier must be covered by cap and its primes
must lie strictly below R. No replacement coefficient or analytic density
estimate is used in this equality.

`ActualPrimeBoxMass` sums over genuine finite function tuples in the
target-deleted intervals `[N^(a_i),N^(b_i))`. Finite distributivity proves
the exact factorization and the mass limit `prod_i log(b_i/a_i)` for every
fixed finite positive-width box. Adjacent separation implies strict
decrease and distinct primes, allowing the same mass to be identified with
the actual reciprocal totient of the tuple product. Without separation,
that reciprocal-totient identification is not asserted.

`ActualPrimeBoxEulerLower` weights these actual tuples by `V_N(p_j)/V_N(N^u)`.
When `b_j<=u`, monotonicity gives a simultaneous lower bound by the ratio
at `N^(b_j)`. The proved ratio and tuple limits give one threshold, before
all later even targets and covering caps, for a lower bound
`(u/b_j)*prod_i log(b_i/a_i)-eta`. This supplier alone does not place a box
inside the Rosser boundary predicate; that geometric inclusion and its
injective summation must be supplied separately.

`ActualRosserTripleBox` supplies this inclusion for an actual three-prime
box. In decreasing coordinate order, adjacent separation and the gates
`b_0<=u`, `3*b_0<=beta`, and `beta<=a_0+a_1+3*a_2` put every tuple into the
literal boundary at `ceil(N^beta)`. The first cube test is strict because
the interval upper endpoint is excluded; the shell test is non-strict
because the lower endpoints are included. The map
`(p_0,p_1,p_2) -> (p_2,{p_0,p_1})` is proved injective on the box, so no
factorial or multiplicity is lost. With `u<=beta`, the actual raw density
therefore has the eventual lower bound

`U_N(N^u,N^beta)/V_N(N^u) >= 1+(u/b_2)*prod_i log(b_i/a_i)-eta`.

All prime-mass and Euler-ratio inputs to this theorem are supplied by
proved results. At `u=1/3`, `beta=1`, the explicit box with lower endpoints
`(3/10,27/100,17/100)` and upper endpoints `(8/25,29/100,19/100)` satisfies
every geometric gate. Its contribution is bounded below by
`(100/57)*log(16/15)*log(29/27)*log(19/17)-eta`. Exact logarithmic
inequalities and rational arithmetic, with `eta=1/10000`, yield

`exists N0>=2, forall even N>=N0, forall cap>=N^(1/3),`
`U_N(N^(1/3),N)/V_N(N^(1/3)) >= 1+1/2000`.

This theorem has no geometric or analytic premise left to supply. The next
modules extend the one-box result to finite families and a full first-layer
integral; the fixed-s limit F(s) remains open.

`ActualRosserTripleBoxFamily` proves coordinate separation makes the actual
tuple carriers disjoint, then injects their union into the boundary sum.
The constant term is one for the entire family. A finite maximum of the
one-box thresholds, with error `eta/(card I+1)` per box, proves the sum of
all box gains with a common threshold. Explicit `u>0` also covers an empty
family without a vacuous positive-level argument.

`LogPrimeBoxIntegral` evaluates the genuine volume integral of `prod_i 1/x_i`
over `prod_i [a_i,b_i)` as `prod_i log(b_i/a_i)` for `0<a_i<=b_i`.
Integrability, zero-dimensional boxes, degenerate intervals and constant
weights are included. `RosserTripleMesh` uses normalized coordinates
`x_i=log(p_i)/log(y)` in decreasing order, and the open region

`Omega3 = {0<x_2<x_1<x_0<1, 3<x_0+x_1+3*x_2}`.

Every coordinate exceeds `1/3`. Uniform half-open mesh cells inside
`[1/3,1]^3` are selected by separated adjacent intervals and a strict lower
shell condition. Every selected cell lies inside Omega3, and every point
of Omega3 eventually belongs to a selected cell. The proof preserves the
strict shell and all half-open endpoints; it does not assume that a
boundary exceptional set has measure zero.

`RosserTripleMeshIntegral` identifies the finite sum

`sum_cells (1/b_2)*prod_i log(b_i/a_i)`

with an actual integral of indicator-weighted densities. These integrands
converge at every point to the Omega3 indicator times
`1/(x_0*x_1*x_2^2)`. The fixed bound `81*indicator([1/3,1]^3)` supplies
dominated convergence, proving convergence to the real Lebesgue integral
`rosserTripleLayerIntegral`.

`ActualRosserTripleLayerLower` scales each mesh endpoint by a fixed `u>0`
and takes `beta=3*u`. This preserves all actual box gates; `u/(u*b_2)` and
the logarithmic ratios cancel exactly, leaving no extra scale factor.
First choose the mesh with error `eta/2`, then its prime-density threshold
with error `eta/2`. The result is

`exists N0>=2, forall even N>=N0, forall cap>=N^u,`
`U_N(N^u,N^(3*u))/V_N(N^u) >= 1+rosserTripleLayerIntegral-eta`.

The original `u=1/3, R=N` case is included. This proves the first continuous
boundary contribution. `RosserTripleLayerIdentity` further proves that
the actual three-dimensional integral equals

`integral_(0<q<1) q^(-2)*upperRosserBoundaryMass 1 3 q`
`= SuzukiFiniteContinuousLayers.suzukiLayer 1 2 3 3`.

The first equality uses measure-preserving extraction of the last coordinate
and Fubini with proved integrability. The remaining two coordinates keep
their order. In the open region the residual `3-x_0-x_1` is positive, and
the supplier's strict shell is exactly `3<x_0+x_1+3*q`. The second equality
uses the pinned proved source-layer identity at depth one and residual
three; no identity or integrability premise is left open. Higher odd ranks,
arbitrary finite-prefix lower limits, the full fixed-s equality and the
main theorem remain open.

### Exact Euler-ratio correction in the frozen manuscript

At `paper/source/manuscript-body.tex` lines 425--429, the displayed exact
ratio to `2 C_N product_(p<z)(1-1/p)` contains an incorrect target-prime
tail factor. If the first product includes every prime `p>=z`, the second
product over `p|N`, `p>=z` must use `(p-2)/(p-1)`, not `1-1/p`. Equivalently,
the displayed second product may be retained if the first product excludes
primes dividing `N`. This follows from

`(1-1/(p-1)^2)^(-1) * ((p-2)/(p-1)) = 1-1/p`.

For example, the excluded prime `p=5` contributes `3/4` in the second
product, whereas the displayed factor is `4/5`. The existing Lean theorem
`normalizedFiniteSieveDensity_eq_odd_div_tail` already has the correct
normalization through `centerPrimeTailCorrection`. The fixed-positive-power
tail limit is unaffected by this algebraic correction; the displayed exact
identity itself must not be used as written. The manuscript source was not
edited in this checkpoint.

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
   coefficient `K` for the same physical source. The fixed raw-tree
   coefficient, actual small-weight sandwich, small-weight density
   supplier and absolute rough-mass bound are proved. The same raw upper
   and lower density ratios now converge two-sidedly and uniformly on
   every legal compact set of `(u,s)`, to the canonical Suzuki factors.
   Upper residuals `s>1` have no finite upper restriction; lower residuals
   include `s=2`. Actual strict-margin prime-box families supply local
   thresholds and a finite subcover gives the required compact uniformity.
   All-depth analytic errors are controlled uniformly on each fixed
   residual interval. The explicit classical lower formula is identified
   on `[2,4]`; no new global classical-factor identity is inferred here.
   The causal boxed policy, its support exponent and the sharp signed
   density of the same physical weight still require proofs. The exact
   full-to-rough projection, actual lower physical attachment and both
   normalized attachment reserves are now proved for arbitrary permitted
   retention policies; they do not discharge those policy-specific tasks.
3. Prove the complete current eleven-term lower-weight mean after paired
   deletion. The literal pointwise inequality, full `Y11` endpoint, actual
   pair injection, repeated-prime error and unit removal are now proved;
   their actual signed mean still needs the analytic sieve estimates for
   the compiled policies, despite the now-constructed genuine lower rho.
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
   source mass limit are also proved, and the actual PNT/Mertens suppliers
   have been connected. The manuscript physical-weight density/distribution
   theorem and licensed smooth outer approximation remain open.
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
`ImbalancedChen/PanProductGridModulus.lean` now proves the remaining two
endpoint gates for every honest power-bounded physical layer: if
`0 ≤ theta < (1-κ₀)/2`, then uniformly over all selected cells,
`floor(N^theta) ≤ panModulusCutoff Y₀ B` and
`floor(N^theta) ≤ panModulusCutoff Y₁ B` eventually.  The proof uses a strict
intermediate product exponent, absorbs the fixed logarithmic loss in the
remaining power gap, and retains the exact `-1` endpoint rounding.  Its
Selberg corollary applies the result to the literal level
`enlargedSelbergLevel theta N ^ 2` via the previously proved finite floor
bound.

This does not license the false transfer of a global
`sqrt(N)/log(N)^B` cutoff to `Y ≍ N^(1-κ₀)`: the missing factor is a genuine
power `N^(κ₀/2)`.  The next analytic composition must therefore identify the
manuscript's actual physical modulus layer and prove that its exponent has
the displayed strict gap before applying the aggregate.  The existing
`(r,q)` rectangle grid gives useful global `4N` bounds, but mere containment
of a signed rectangle discrepancy in a larger product strip would not be a
valid transfer.  Gate loss must also be accounted for when the analytic main
term is compared with any ungated physical mass.

This power-bounded Pan path is now classified as an auxiliary weak route,
not the current-`K` proof spine.  For the existing Selberg level its
normalizer contributes `4/theta`, while the local cutoff requires
`theta < (1-κ₀)/2`; even at the limiting edge this is at least
`8/(1-κ₀) > 8`, whereas the manuscript needs
`K = 8452171/1250000`.  Moreover the manuscript's high-rank positive-weight
support reaches `theta* = 599/1000`.  The current-`K` proof must therefore
formalize the manuscript's same `ρ_N` pointwise majorant, density and signed
factorized local distribution, preserving the distinction between the
physical modulus cap and the auxiliary factorization support.

`ImbalancedChen/SignSensitiveAttachment.lean` and
`ImbalancedChen/PhysicalUpperWeightBridge.lean` now isolate the finite
same-weight interface required by this route.  The first module proves the
order reversal in the negative branch: multiplying the lower small-prime
divisor sum by a negative raw coefficient gives the required upper bound.
It also proves the coefficientwise absolute bound after the sign-dependent
attachment.  The second module proves finite Fubini for the literal shifted
half-product source and decomposes its weighted congruence sum into the
reciprocal-totient density, the exact coprime-source correction, and the
signed primitive-residue distribution error.  All three terms contain the
same function `rho`; no density or distribution conclusion is stored in a
structure or assumed by the identity.

The next proof step is therefore sharply delimited: instantiate this
interface with the manuscript's first-exit rough tree and the unique
small/rough prime decomposition, then prove the density estimate and signed
factorized distribution estimate for that exact constructed `rho_N`.  A
standard Rosser weight, the auxiliary weak Selberg route, or separate
coefficients for the three terms cannot discharge this obligation.

`ImbalancedChen/FirstExitTree.lean` now closes the first finite part of that
step. For an arbitrary finite ordered universe it defines the retained
alternating polynomial and the residual correction at each first rejected
selected prefix. `oddFirstExitPolicy` forces every even-rank prefix to be
retained. The exact theorem is

`retained polynomial = product (1-h(p)) + odd-first-exit correction`,

and the correction is nonnegative whenever `0 ≤ h(p) ≤ 1`. Specializing to
the literal predicate `(p : ℤ) ∣ n` identifies the Euler product with the
roughness indicator and proves the pointwise majorant for all integers,
including zero and negative integers. This is the raw tree identity at
`manuscript-body.tex` lines 377--391, not a replacement standard Rosser
weight.

At the abstract ordered-universe layer,
`mem_oddFirstExitRetainedLeaves_selectedProd_squarefree` proves every retained
prime product squarefree,
`mem_oddFirstExitRetainedLeaves_moebius_selectedProd` identifies its Möbius
value with selected-list parity, and
`mem_oddFirstExitRetainedLeaves_value_eq_moebius_mul_selected_prod` rewrites
the real leaf value as the Möbius coefficient times the local-weight product.
`oddFirstExitRetainedLeaves_unit_mem` explicitly keeps the empty branch
`d = 1`.

`ImbalancedChen/RoughPrimeUniverse.lean` now constructs the manuscript's
literal rough-prime carrier from `p ∤ N` and the real inequalities
`w ≤ p < z`, sorts it strictly decreasing, and derives `Nodup`, `SortedGT`,
exact membership and the original Finset after forgetting order. An explicit
enumeration cap witnesses finiteness, and `z ≤ cap` removes it from the
membership theorem without changing either real endpoint to a floor or
ceiling. The generic pointwise roughness majorant and Möbius leaf formula are
specialized to this concrete carrier.

`ImbalancedChen/RetainedModuli.lean` defines the natural support and integer
coefficient `lambda(d) = mu(d)` on that support, zero off support. It proves
`lambda(1) = 1`, squarefreeness of every supported modulus, uniqueness of the
retained leaf as a value for each supported modulus, and recovery of each
leaf value as the looked-up coefficient times the local-weight product over
`d.primeFactors`. The recursive source leaf list is proved `Nodup` by separating
the skip and select subtrees at their current prime. Combined with selected-
product injectivity, this proves the modulus list `Nodup` and yields the exact
multiplicity-preserving `oddFirstExitRetainedLeaves_sum_eq_retainedModuli_sum`.
The next bridge attaches the small-prime weights through the unique
small/rough decomposition. The boxed coefficients may inherit the majorant from their
coefficientwise domination of the raw tree; they must not be treated as a
new prefix-closed tree. The physical density and signed factorized local
distribution estimates remain subsequent analytic obligations.

The retained side is no longer hidden behind the recursive evaluator.
`FirstExitLeaf` records each terminal selected list, sign bit and accumulated
mass; `oddFirstExitRetainedPolynomial_eq_leaves_sum` proves exact equality
with the evaluator; and the two root membership invariants identify the mass
with the selected-label product and the sign bit with selected-list parity.
The additional root invariant
`mem_oddFirstExitRetainedLeaves_selected_reverse_sublist` records the precise
order convention: `selected` is accumulated backwards, and its reverse is a
sublist of the ordered universe. From an explicit `universe.Nodup` hypothesis,
`mem_oddFirstExitRetainedLeaves_selected_nodup` derives duplicate-freeness of
every retained selection. If all universe entries are prime,
`oddFirstExitRetainedLeaves_selectedProd_injOn` proves the selected-prime
product injective on actual retained leaves. The new squarefree, exact
`cardFactors`, Möbius-parity and real-value lemmas close the summand
identification, including the empty unit branch. The new recursive `Nodup`
proof and modulus `Finset.sum` theorem close the multiplicity-preserving raw
rough-side reindex.

The manuscript's raw rough universe is the strictly decreasing list of primes
`p ∤ N` with `w ≤ p < z`; the small side is `p < w`. Its `Nodup` now comes
from sorting the concrete finite prime set, not from a new number-theoretic
assumption.
Fine box labels may repeat even though the underlying prime universe cannot.
The product injection above applies to the raw prefix tree only: boxed support
need not be prefix-closed and inherits the majorant only through
coefficientwise domination.

Dependency audit: `goldbach-lean` is pinned at
`09b97db5764ade1246bfb77206baa1b124760958`; it uses the identical Lean and
Mathlib pins and is the sole analytic-number-theory dependency.  Its inherited
`LeanArchitect` dependency is pinned at
`78dd66840d3efe8c824c699fc03381cec817c271`.  The separate
`analytic-number-theory-lean` package must not be added because both projects
export the `AnalyticNumberTheory` and `PrimeNumberTheoremAnd` module roots.
