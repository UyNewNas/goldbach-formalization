# P2.9: precise next proof frontier after the geometric Family

This is a reuse and manuscript-scope record, not a compilation receipt.

## Already existing work to preserve

The sharp Gamma5 ordinary mass is not a blank theorem. At source baseline
`a929011ec95843553fc2e10b7291c8077e0952c0`,
`docs/source-only/20261102-resume-30s/s16_gamma5_and_costs/P2EnhancedBadGamma5CostTheta.lean`
contains `actual_bad_nonunit_upper`, `actual_bad_inclusive_upper` and
`original_badGamma5_cost_theta`. They use the actual alpha >= 2, the same Q/d,
positive finite marks, reciprocal quadrature and the global Buchstab cap.

The existing SeedConvertedMass route at
`docs/source-only/20261110-yellow-closure-10t/t07_h34_actual_counts/successor_base_seed/Part5OriginalH430SeedConvertedMass.lean`,
including `original_inclusive_converted_mass` and `seed_split`, connects
sharp costs to the original `actualJ2omega`. These proofs are reused.
The source at
`docs/source-only/20261125-p2-actual-small-payment/ImbalancedChen/Part5OriginalH430ActualSwitchedSmallPayment.lean`
pays the actual Gamma9--21 small complete products. Its Gamma5 term
remains literal; it is not a completed Gamma5 small-product payment.
The existing actual source rank and plateau also remain reuse inputs.

## The missing radial implication

The physical profile's complete-product gate permits
`M < exp(width) * N`. Thus a fixed positive width leaves an actual radial
interval beyond N. The fact that its logarithmic thickness divided by log N
tends to zero is not an ordinary-mass payment for that interval.

The new Family support only implies each slot is at least N^a / 2.
Above the existing `scaleThreshold a`, the old Euler-budget proof already
derives N^(a/2) <= N^a / 2. The auxiliary rough cutoff for the radial count
must therefore be N^beta with beta = a/2.

The intended constants are the original
`a = frozenLeafCutoffFloor` and `K = frozenSourceRankBound`.
They are fixed before width and scale, and must retain their original
fully qualified declarations.

## Existing radial proof to reuse

The baseline contains:

- `docs/source-only/20261112-resume/t07/classical-fixed-box/radial/Part5OriginalH430ClassicalRadialRoughMass.lean`;
- `docs/source-only/20261112-resume/t07/classical-fixed-box/radial/Part5OriginalH430ClassicalRadialTupleCount.lean`.

The first subtracts two actual rough counts at the same cutoff. Its present
cutoff is N^(1/96). The second's `rank_bound` already works for every natural
rank k, retaining order and repeated primes; only its subsequent finite sum
uses Fin 201 and a factor 20.

The source of the general product-fibre bound is
`ImbalancedChen/P5zMarkedPrimeFamilyMultiplicity.lean`.
The original `prime_divisor_floor` is in
`Part5OriginalH430ClassicalFixedClampGeometry`; its recorded
list-membership compatibility version should be selected explicitly if used.

For the actual beta, the endpoint and shell limits have the form

\[
\frac{\log N}{N}\,\#\{m:bN<m\le cN,\ P^-(m)\ge N^\beta\}
\longrightarrow
\frac{c-b}{\beta}\,\omega(1/\beta).
\]

The rank sum uses Fin (K+1), with marks multiplier one for a single geometric
ambient. The next payment target is

\[
\forall\varepsilon>0,\ \exists h\in(0,1/8],\
\forall^{\mathrm{eventually}}N,\quad
\frac{\log N}{N}\,\mathcal B_{\beta,K}(N;1-2h,1+2h)
\le\varepsilon.
\]

Taking width = log(1+h) places the profile's outer product support below
(1+h)N < (1+2h)N < 2N. Positivity of every integer prime coordinate lets
the original finite tuple enumerator cover the supported coordinates.
Zero rank is included in the bound; the geometric profile itself always
retains its two fresh slots, including when the old prefix and rough tail
are empty.

The source-only `P2FiniteMarkedGamma5RadialNaturalMass` now proves an exact
one-ambient dictionary: its finite natural-prime carrier has membership
iff the unchanged profile is nonzero on the prime tuple and the complete
product exceeds N. Its coordinate-value image is injective, and
`Finset.sum_image` preserves the exact profile-weighted sum, order and
repeated prime coordinates. This is source, not kernel acceptance.

The resulting full-natural-support sum is still not identified with the
whole original marked-history sum or J. That dictionary and the aggregate
fixed-weight/multiplicity payment remain separate obligations.

## Existing arbitrary fixed-band supply

The whole-file research variants at
`subfish-zhou/goldbach-lean@9d4c3a4010d42aedd9e7231bf94386019cfffccc`
contain a genuine unrestricted finite-band theorem. They are existing
mathematical work, but their production-source hashes differ from the
currently selected old providers in the compiler cache. They must not be
silently substituted or given object credit.

The narrower selected reuse candidate is the already validated
`MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniformFixedCompat`:

- source SHA256:
  `282ede7340f0069dc12479db826b6a4346ed458a1d37ed1ea926740183e07900`;
- object SHA256:
  `71575dea300b4d15714d5c92392589faed3542cc3ee13a51284dbb6e0eb9faa1`;
- its sole direct import is the old Buchstab Uniform provider;
- it supplies `LiLiuPrereqBuchstab.roughCount_buchstab_band_error_unrestricted`;
- its native closure has 29 old dependencies plus the compatibility module.

The P1 source/object facets were checked against its existing accepted
post-validation snapshot. This does not by itself establish a receiving
P2 import snapshot. No replacement of the three old providers, no new
proof of Buchstab, and no adoption of the two unrelated consumer
import-only overrides is required for this radial route.

The broader 1526-file P1 inventory matched the original **current source
selection**, not all research production-source hashes. In particular,
the three old Buchstab providers differ from the unrestricted research
overlays. The inventory and physical existence checks must not be
reported as complete production qualification.

## Manuscript classification and remaining scope

The fixed 1106 manuscript is
`chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`.
See `paper/release-20261106/en/argument.tex`,
`prop:current-positive-product`, especially its closing smooth outer
approximation paragraph. It fixes approximation precision before the
large-N limit and only then sends approximation error to zero. The
same rho is required at each fixed precision.

The radial step is a manuscript-internal omitted derivation with an
existing proof route. This audit does not identify a contradiction in
the manuscript. Proper-wall collars, the complete marked smooth
envelope to original J, the same-rho PP/VM estimate and the W1/W2 directed
debts remain separate. The native-Wu/H247 compatibility route is
discussed separately in `MANUSCRIPT_SEMANTIC_BOUNDARY.md`.

## Actual root-cell source dictionary

The new source-only `P2FiniteMarkedGamma5ActualRootCells` partitions the
original p sum itself by the existing RootCode n. It retains originalBand,
the dependent B p of LevelIndex positions, every levelMark and all repeated
products. The old codeLevel_rootCode identifies rootQ with cellQ on each
cell. Public identities use the original ordinaryBad, markedConverted and
markedTheta; no alternate mass or new J is introduced. The old inclusive
untested dictionary and weighted_fiber_sum retain thetaConversion and
all original multiplicities. This source identity has independent static
reviews but has not been compiled.

The code type is fixed with n before N. This reuses the existing finite
same-Q root grid; a new coordinate chain-rule project for rootQ is not
required. The old readyCatalog includes all Programs and is not substituted
for the actual selected history sum.

The remaining mainline comparison must realize the actual selected-history
read, branch and old-coordinate restrictions by one admitted smooth outer
family at each precision. Its full ordinary mass must be bounded by the
original sharp mass plus radial and other proper-boundary excesses, with
the same marks. ordinaryBad contains M<=N and naturalOuterMass contains
M>N; those expressions are different pieces of that comparison.
AbsoluteQueries supplies same-stage L1 simple-function approximation, not
the required smooth arithmetic realization. The older twenty-instance
classical Gamma9--21 fixed-clamp licence is not an all-U4 Gamma5 supplier.

The P1 native supplier binding receipt now verifies the existing 12-module
Buchstab extension and its actual imported object facets. It grants no
new manuscript theorem credit or cross-environment transfer credit.

## Further existing suppliers and the two J roles

`Part5OriginalH430NativeQueryPaths` at
`docs/source-only/20261102-resume-30o/h430_smooth_causal_boxes/Part5OriginalH430NativeQueryPaths.lean`
(blob 4fec5d35c7a2dcc8fda4a4561f1bc5bec7c91db3) already supplies the
original W1/W2 coefficient lists, native slot/rank maps and actual child
query atoms. Its Buchstab child-domain/atom theorems still require
StartMatches; they do not settle arbitrary moving-parent smooth realization.
The adjacent CellMeasurability source (blob
27b08709e935cf33f54db51eaeca4cc21c553b15) already proves cell measurability,
which is distinct from positive smooth arithmetic approximation.

The scalar J in SeedConvertedMass.base_after_converted is a seed-functional
comparison parameter below actualJ2omega. It is not automatically the
ordinary-mass limsup J in the positive-product proposition. Their needed
mass/normalizer identification must be proved, not inferred from the
shared letter. Existing seed-cost results should be reused without
changing that distinction.

The current P5zMultiplicity object is exactly bound by the previously
accepted member-repair-batch11 source, normal/kernel snapshots and public
export audit. Its old ca3f baseline selection is not the current producer.
No fibre theorem is re-proved. The old audit counts 12 public exports;
the later receiving-input inventory and selected exact thin relocation
are recorded below. No broader old-owner full-owned credit is inferred.

## Actual-history radial aggregation source increment

The source-only `P2FiniteMarkedGamma5ActualRadialAggregate`, in
`docs/source-only/20261125-p2-9-actual-radial-aggregate/`, now supplies the
finite positive aggregation of the natural radial mass over the original
U4 root-prime and dependent LevelIndex sums. The existing emitted-history
itinerary and fixed-shape/old-word coefficient bounds are reused unchanged.
Fixing the entire old word fixes its first root prime. No moving prime or
history position receives a separate epsilon payment.

The candidate proves the exact same-carrier profile split at M <= N and
M > N, and pays the latter after summing all fixed remaining depths
dep : Fin 431. Its shape, RootCode n and bounded-rank cardinal factors are
fixed before h and N. The final h and large-N threshold work uniformly for
all t and the original dependent position subsets B dep p. Both the root
and independent review read the original 554-line body; both also reviewed
the 84-line finite-depth increment. This is still source-only, with zero
compilation/kernel/endpoint credit.

These are raw marked profile sums with discrete history selection. Their
inner piece is not identified with original ordinaryBad or converted mass,
and the retained masks are not yet a globally smooth admitted family. The
original sharp-cost, thetaConversion and J interfaces remain necessary
integration boundaries. The T23 source chain and all selected original
owner postimages require a coherent qualified build; the old 764-node
history manifest alone does not cover that complete combined closure.

## Exact fibre reuse receiving boundary

The old P5z object/source remains matched to its original producer, but a
later actual-import inventory exposed 24,504 facets outside the currently
bound receiving scope (9,572 modules / 44,328 total facets). That is not a
proof defect in the elementary finite fibre theorem. The queued broad
full-owned supplement was cancelled before running.

The same existing two tuple definitions, helper and public proof now have
an exact thin source relocation in
`docs/source-only/20261125-p2-9-prime-product-fibre-core/`. Only the
TupleCount import changes. Public FQNs and proof bytes are preserved;
private module ownership changes and requires its own full-owned audit.
The new two-module validation job is
`job_f761e0d8b28e47369e915aa7d21f3347`; no passing result is inferred yet.
This route does not build or qualify the unrelated old native closure.


## Actual target-coprimality deletion and the next sharp inverse

The source-only `P2FiniteMarkedGamma5TargetExclusion`, in
`docs/source-only/20261125-p2-9-target-exclusion/`, now adapts the existing
`p5U7ActualBadRough_card_le_log` and log-power decay to the original fixed
cutoff beta and rank K. With unit marks and all repeated/ordered coordinates,
its complete-product exception is bounded after normalization by
`(2*multiplicity/log 2)*(log N)^2/N^beta`, hence tends to zero. The original
general arithmetic proof is reused unchanged; no new prime-factor counting
or Buchstab proof is introduced. This new consumer has static review only.
Its historical arithmetic supplier and receiving closure are not yet
qualified.

This deletion is needed because the actual `primeWindow N` fresh primes
must be coprime to N, while ambient labelled prime tuples have no such
restriction. It is not a geometric-wall payment. The old fixed-clamp
source's target=1 shortcut cannot provide the actual N-target dictionary.

The next pointwise inverse has been checked against the original four
source definitions. For two fresh primes coprime to N and a sorted prime
tail, the exact original raw gates imply the original badLabels and rough
cofactor membership. Its fresh lower and tail floor use a0; fresh upper is
strict a2, the fresh pair order is strict, the bad-square boundary includes
equality, tail order is non-strict and the complete product cap includes
equality. The empty and repeated-prime tail are retained. The tail does
not require coprimality with N. This is the precise inverse source bridge
still to be implemented and verified; it is not a claim that the entire
smooth profile equals the sharp source away from only the radial boundary.
