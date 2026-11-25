# P2.9 — original Gamma5 integer support and geometric Family

Manuscript: `chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`, release-20261106. Source baseline: `goldbach-formalization@a929011ec95843553fc2e10b7291c8077e0952c0`.

## Current verification status

**IN PROGRESS. Four light geometric modules have passed normal compilation, independent kernel replay and full-owned/transitive-axiom audit, with 69 owned declarations. The three accepted P1 radial thin modules add 42. NonradialSupport and UnitTailProduct add 6 and 2: nine accepted modules / 119 owned declarations in this increment. These counts include definitions and generated declarations, not 119 new mathematical theorems. Full P2.9 remains open.**

| Module | Current evidence |
|---|---|
| `P2FiniteMarkedGamma5IntegerSupport` | Accepted, 7 declarations; source `ecdb5e50b1f4dcb645767dfb7ecf8dd9d90f560f54c8d358c568f0610d5c0315` |
| `P2FiniteMarkedGamma5AllRankEulerBudget` | Updated owner accepted, 12 declarations; source `27aa18059ed29e5a053b6f0388983dfebb93f3784dad135106a1d6cdadc2b33b` |
| `P2Gamma5AdmissibleFamilyCore` | Accepted, 26 declarations; source `5d570928557a22f3c3867057079e57ece81d1f1b6c6437a5166b5ba816c6a1fe`; exact original 823-byte structure retained |
| `P2FiniteMarkedGamma5GeometricFamily` | Accepted, 24 declarations; source `5b2e5642196a7cab5e6f9572283c8b498d37c67f65e7d39e0c2221026cb33db2` |

Task `a40329930dfa4f9fa8a4fd41bd355296` exited 0 after 24.281 seconds
of actual runtime. Its 15-module compile closure reused 13 existing objects;
only Core and Family were newly compiled in that task. Both new targets
passed independent kernel replay and full-owned audit. Only
`Classical.choice`, `Quot.sound` and `propext` were observed.

The complete four-module acceptance is recorded in `ACCEPTANCE.json`,
`evidence-c/manifest.json` and `evidence-c/all.tar.gz`. The archive has
302,235 bytes and SHA256
`cec503ba0c82cc5f3577382fa4b7466d3d43c4f593daccff204539c96e02a29c`.
It includes exact sources, dependency/object bindings, complete owned
declarations/types, audit and replay records. It does not include .olean
objects. The separate `cache-transfer/` contains the original 12-object
physical-support closure for receiving verification on P1; export alone
does not establish P1 acceptance.

The preceding two-module `evidence-b/` remains historical evidence.
The existing Euler proofs are reused; its added API is only a public
zero-function forwarder. The failed Family attempts and exact minimal
scope/import repairs remain recorded. The exporter also records missing
old-attempt logs for some reused baseline modules; the accepted target
audit/replay records are present. Generic Winner9/page-coverage fields are
exporter context, not new obligations or a request to redo the 17,572 rows.

## Mathematical increment

For the unchanged original `finPhysicalProfile`, nonzero weight on a natural tuple implies every coordinate is positive. Every indexed coordinate divides the positive complete product; the existing original product gate therefore gives

\[
W(u)\ne0\implies
1\le u_i\le\left\lfloor e^{\mathrm{width}}N\right\rfloor_{\mathbb N}.
\]

This proves finite support on **all natural tuples**, retaining repeated entries and the empty old/tail block cases. The prime-support field is a subset of that support, without adding a primality filter to the smooth weight.

The Family module constructs the original `P5Z.AdmissibleAllRankIntegerGeometricFamily.Family K`, preserving the original structure declaration byte for byte. For each fixed `(k,r)`, `a>0`, fixed `0<width≤1`, arbitrary fixed `logQ : ℕ → ℝ`, and `k+2+r≤K`, its active-rank function equals the original profile at every scale above the existing threshold

\[
N_0(a)=\max(e,2^{2/a}).
\]

Other ranks and the finite initial set of smaller scales are zero. The structure uses `aStar=a`, `lower=1/2`, `upper=exp 1`. Existing smoothness, real support, and Euler estimates plus the new finite integer support discharge the fields. The natural derivative constant is chosen before the moving scale, endpoint function, split, word, and point; the logarithmic exponent is `B=0`. Width is fixed before that constant is chosen.

No Family, support conclusion, Euler budget or prime-product target is assumed as a new premise. This is a geometric construction for a fixed split, not a claim that all arithmetic histories, their collar costs or their PP estimates have been admitted.

## Reuse and provenance

The static closure is 15 project modules: 11 exact previously accepted sources, one existing owner needing revalidation after a public API addition, and three new modules. It imports no additional native research modules.

`docs/source-only/20261125-p2-9-geometric-family/` preserves the exact original structure, previous full owner, new owner postimage, original accepted Euler owner and the exact additive forwarding declaration. Its manifests distinguish static source preservation from Lean acceptance. Heavy consumers of the old Family owner must select the new postimage; their compatibility is not newly accepted here.

## Remaining P2.9 boundary

- Actual marked-history source admission and the original profile/coordinate dictionary require their full existing history dependencies to be qualified.
- Collar and ordinary-mass estimates, the original same-rho signed PP/VM estimate, and W1/W2 directed count debts remain distinct analytic responsibilities.
- The current native-Wu Binder still assumes 29 H247 comparisons and further integral inputs. These are sufficient conditions for that Binder route; the missing adaptation between native moving boxes and the manuscript's actual finite enhanced families prevents treating them as the sole equivalent manuscript target.

See `MANUSCRIPT_SEMANTIC_BOUNDARY.md` for exact definitions, quantifier ordering, and source references. It does not assert that the 29 comparisons are false or that the manuscript is false. Further work should supply count licences on the original finite marked families, with their actual Q, labels, gates, ceiling and Theta.

`REVIEW.md` records the independent static mathematical/interface review. No global board promotion or full-P2.9 completion follows from this increment.


## Subsequent manuscript-internal source work

The actual U4 source adapter is preserved in `docs/source-only/20261125-p2-9-actual-family/`, with its independent review in `ACTUAL_SOURCE_REVIEW.md`. It derives its source rank and reuses the old plateau. Its large arithmetic-history closure remains unqualified and its new proof credit is zero.

The radial collar candidates are preserved in `docs/source-only/20261125-p2-9-radial-collar/`. They use the actual original floor and rank, the existing unrestricted fixed-band compatibility supplier, and the original multiplicity bound. FrozenConstants, PrimeDivisorFloorCore and the repaired RoughMass now pass every normal/kernel/owned/stock gate. Their exact 42-declaration acceptance is recorded in `docs/verification/20261125-p2-9-radial/ACCEPTANCE.json`; the tuple/profile/natural consumers remain source-only. The exact natural-prime support/sum dictionary remains source-only. The already existing sharp Gamma5 cost and seed-conversion proofs are reuse inputs.

`NEXT_PROOF_FRONTIER.md` records the precise radial shell, manuscript double-limit order, provider selection and the distinction between a single-ambient payment and the complete marked-history/J chain. `SCOPE_REPAIR.json` records the failed first Family compile and the exact scope-only correction. Final Core/Family acceptance is separately established by the later successful task and evidence-c.

The exact original marked-mass root-cell partition is in
`docs/source-only/20261125-p2-9-actual-root-cells/`. It is source-only and
retains all actual p-dependent positions, marks and repeated products.
The existing native supplier's P1 binding receipt and exact FixedCompat
source are in `docs/verification/20261125-p2-9-native-supply/`; those are
reused supply, with zero new manuscript theorem credit.

## Actual U4 radial aggregation candidate

The separately reviewed 638-line source in
`docs/source-only/20261125-p2-9-actual-radial-aggregate/` retains the original
root primes, dependent history positions and positive marks. It proves,
in source, a uniform radial excess payment over the fixed 431 original
remaining-depth slots. Existing path uniqueness and positive coefficient
bounds are reused. Fixed shape, RootCode n and rank factors are absorbed
before selecting h and then taking N large.

Its exact identity splits the same marked profile sum into M <= N and
M > N parts. It does not identify the inner profile with original
ordinaryBad, remove thetaConversion, or supply the complete smooth/J/PP
licence. This increment is uncompiled and has zero formal or kernel credit.


## Actual target-divisor source deletion

The new source-only package `docs/source-only/20261125-p2-9-target-exclusion/`
reuses the existing rough-target cardinal bound and log-power decay at the
actual frozen cutoff and rank. It supplies an absolute unit-weight payment
for complete ordered-prime products not coprime to N, with repeated primes
and rank zero retained. Root and independent mathematical reviews pass;
normal compilation, kernel replay and its exact receiving-closure audit
remain pending. The actual selected-history aggregation, sharp inverse,
nonradial walls, global smooth realization and original J/PP licence remain
open. P2.9 is not marked complete.


## Original sharp inverse source

`docs/source-only/20261125-p2-9-sharp-source-inverse/` contains the new
108-line pointwise inverse. The exact original raw gates and literal
fresh-prime coprimality recover the original badLabels, roughNumbers and
canonical sorted tail. Empty and repeated-prime tails and every original
strict/inclusive endpoint are retained. Root and independent source reviews
pass; this module remains uncompiled and does not yet reindex the actual
marked sums.


## Accepted nonradial support and empty-tail product bound

The exact original inner profile is now proved to lie below the sum of
its sharp-geometry indicator and original nonproduct strip indicators.
`docs/source-only/20261125-p2-9-nonradial-support/` contains the accepted
6-declaration source and complete audit evidence. A transient disk-full
failure was resolved by audit-only reuse of the existing object, with no
source recompilation.

`docs/source-only/20261125-p2-9-unit-tail-product/` contains the accepted
2-declaration empty-tail physical product bound. It retains every old
coordinate and both fresh slots; the sole standard import repair adds
Pow.Real. Applying this bound to an actual history still requires the
original matched prefix and scale_and_alpha conditions.

The new source-only 346-line actual target-exclusion aggregation is in
`docs/source-only/20261125-p2-9-actual-target-exclusion/`. It pays the
complete-product noncoprime allowance with the original weights across
all 431 fixed depths, uniformly over allowed widths, using the existing
prefix coefficient bound. It is not yet compiled. Sharp finite counting,
arithmetic proper-wall payment, global smooth retained-history selection,
original J and same-rho PP remain open.


## Sharp counting and nonradial source bridges

The new source-only `SharpTupleCount` injects the joint carrier over all original bounded splits into the original pair/cofactor source. The old word recovers the old rank; the canonical cofactor list recovers the tail rank and ordered tail. Thus its `ordinaryBad` coefficient is exactly one. Empty/repeated tails and the original inclusive bad wall are retained.

The new source-only `NonunitQuotient` reuses the existing native `NonunitRoughUniform.uniform_upper`; its only native source postimage adds the already supplied FixedCompat import, preserving the original three proof texts. It supplies the actual cutoff bounds `(2/beta)*x/log N` and `(4/beta)/D`, including the empty-height branch and the transition endpoint. `OmittedPrimeWall` uses the ordered remaining tuple together with the omitted prime to obtain a genuinely injective finite count. `GateAffine` records the signed affine form for every original nonproduct gate and preserves the exceptional unit-tail cases.

These four packages have source/readback and mathematical review, **not compilation, kernel replay or full-owned acceptance**. The accepted count remains nine modules / 119 owned declarations. At that source checkpoint the actual inner and wall transports were still open; the later source result below now supplies their raw ordinary-mass comparison. Full selected-history smooth realization and original J/PP remain open. Current ProfileCollar/NaturalMass header-only postimages are explicitly selected in the registries; the previous headers remain historical evidence.


## Current ordinary-mass and selected-history source result

Nine additional source-only modules supply the arithmetic wall/empty-tail payments, exact original inner comparison, recovered actual scale, all-depth weighted proper payment, final ordinary-mass aggregation, and literal selected-path/seed dictionaries. Source readback, exact hashes and mathematical reviews are recorded in their packages and in `ORDINARY_MASS_AND_HISTORY_SOURCE_CHECKS.json`. They add **zero compiled/kernel/owned credit**; the accepted increment remains nine modules / 119 owned declarations.

The final source theorem is
`P2FiniteMarkedGamma5ActualProfileMassComparison.actual_selected_profile_le_original_plus_epsilon`.
For fixed original mesh n satisfying 1/(n+1) <= 11/384 and every epsilon > 0, it chooses one h in (0,1/8] before the large-N threshold. Uniformly afterward for t in [0,1/12] and every original dependent subset B dep p, it proves:

\[
\operatorname{norm}(N)\,
 \operatorname{allDepthSelectedProfileMass}(N,n,t,h,B)
\le
\operatorname{norm}(N)
 \sum_{\mathrm{dep}:\mathrm{Fin}\,431}
 \sum_{p\in\operatorname{originalBand}(N,U4)}
 \sum_{l\in B(\mathrm{dep},p)}
 \operatorname{levelMark}(l)\,
 \operatorname{ordinaryBad}(N,\operatorname{rootQ}(N,n,U4,t,p),
                             \operatorname{wordProduct}(l))
+\varepsilon.
\]

The base coefficient is exactly **one**. Each epsilon/3 allowance pays an entire all-depth radial, complete-product noncoprime, or proper-strip error. No moving prime or individual history position receives a separate epsilon payment. All original marks, old words, pair order, repeated prime entries and dependent positions remain.

The source is in `docs/source-only/20261125-p2-9-actual-profile-mass-comparison/`. Its exact suppliers are:

- `nonempty-tail-wall-count/`: original nonproduct gates, finite union and omitted-prime affine wall payment.
- `unit-tail-count/`: existing empty-tail product saving and product-fibre error estimate.
- `inner-comparison/`: fixed-word coefficient-one sharp comparison plus the two original positive error allowances.
- `actual-proper-payment/`: one shared actual-history scale witness and the original all-depth proper-strip payment.
- `actual-inner-comparison/`: exact root-cell rearrangements and original weighted inner comparison.

`selected-itinerary/` recovers original history membership from all literal edge tests and gives the exact original path weight. `selected-seed-terminal/` recovers the original seed filter and its same-coordinate native terminal atom, retaining specified-cell reads and the generation-zero scalar owner. Concrete Edge N paths are not, by this fact alone, an N-independent finite geometric family.

The real smooth-atlas suppliers are documented in `SELECTED_HISTORY_SMOOTH_REUSE.md`. They must be reused. The remaining source work is the fixed finite selected-prefix geometric dictionary, its global smooth realization with uniform all-orders budget, arithmetic payment for the extra selection collars, the original ordinary J identification, and the same-rho PP/W1/W2 receivers. The arbitrary B quantifier in the positive mass estimate is not a smooth realizability claim.

## Current compilation and source selection

`CURRENT_SOURCE_SELECTION.json` gives priority to the exact current TupleCount, ProfileCollar and NaturalMass postimages and lists the shared owner postimages. The second TupleCount normal attempt found only an unresolved Real cast in single_le_sum. Its minimal explicit type annotation is recorded separately; third task `job_99911fbda6b14d228ebc653cb2654cd7` has been submitted with unchanged verification gates and no acceptance claimed yet.

The existing P2 and P3 arithmetic objects were located without recompiling their original proofs. The accompanying read-only records separate object presence, source/producer binding and full-owned/kernel qualification. Full P2.9 remains open and no board count is changed.


## Real selected-prefix and atlas source checkpoint

Eight more modules (1,425 lines) now connect the fixed original path index,
actual parent/child geometry, an N-free real selected-prefix domain, and the
original smooth atlas. The index contains fixed step shapes and literal read
labels; the native-slot equivalence and fixed edge-weight product preserve
ordered coordinates and original multiplicities. Reverse induction recovers
the actual parent history before invoking each strict child test.

The original profile times the original atlas readout has a global smooth
extension and an all-orders Euler bound with one natural constant chosen before
the moving target, rank split and complete accepted-atom function. Updating the
existing geometric Family reuses its support and finite prime support. A
separate exact prime-coordinate dictionary proves that M<=2N gives every
coordinate <=N and hence the original logarithmic Cube for N>=2, without
removing the M>N outer region.

These are **source-only** results with root mathematical reviews. They add no
normal-build, kernel-replay or owned-declaration credit. The actual finite sum
dictionary, selection-boundary affine/collar payment, original global J and
matching PP/density inputs are still separate obligations. Existing labelled
integer outer-sieve receivers already handle the full carrier and are recorded
in `ORIGINAL_POSITIVE_PRODUCT_REUSE.md`.

The current source manifest now selects the historically accepted exact
NonunitRoughUniform import-order variant and the current Family/scalar/Euler
owner postimages. The older unqualified native candidate remains historical
evidence; its unchanged proofs are not rebuilt. Compiler reception and producer
records retain their actual scope. Full P2.9 remains open.
