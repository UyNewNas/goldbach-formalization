# Verification boundary

This project is not a proof of Goldbach's conjecture or of the attached manuscript's main analytic theorem.

## Same-weight upper density limit through residual three — 12 October

`FinitePiIntegral` proves measure-preserving coordinate extraction and
Fubini for finite real coordinate spaces. Its empty-dimensional integral
has mass one, and its second extraction uses almost-everywhere integrable
slices. `RosserOddTailRegion` proves the exact strict two-coordinate
recursion with residual `s-x0-x1` and inherited upper cutoff `x1`.
`RosserOddTailIntegral` proves compact-box integrability for every positive
terminal coordinate and identifies the genuine region integral with
`upperRosserBoundaryMassAux`. The empty tail retains `0<=s<3*q` without
an extra condition on its upper cutoff.

`RosserOddLayerIdentity` extracts the least coordinate and proves that the
actual odd-dimensional kernel integral is the boundary-mass integral with
factor `q^(-2)`. Outside `0<q<1` its slices vanish, including both endpoints.
For every rank and `3/2<=s<=4`, the proved provider identity gives the
Suzuki source index `2*k+1`. At `s=3` the zero-depth layer vanishes.

`ActualRosserAtThreeLower` connects the genuine finite-layer sums to the
proved JR source series. It chooses a finite prefix within `eta/2` of
`2*exp(gamma)/3`, removes the zero layer, and then chooses the actual
prime-box threshold with the other `eta/2`. Consequently, for every fixed
`u>0` and `eta>0`, one `N0>=2` works for all later even N and every cap
covering `N^u`, giving

```text
actualSmallRosserPlusDensity N cap (N^u) (N^(3*u))
  / actualSmallEulerProduct N cap (N^u) >= 2*exp(gamma)/3 - eta.
```

The finite prefix is selected before N, and the constant term one is
counted once. No estimate of the discarded nonnegative discrete tail and
no additional analytic premise is used.

`ActualRosserAtThreeUpper` applies the proved all-depth upper estimate at
`D=ceil(N^(3*u))`. Actual primes satisfy
`p<N^u<=(ceil(N^(3*u)))^(1/3)`, hence meet its strict natural ceiling
cutoff, even when the level is integral. The Goldbach local-product bound
provides one constant before the target; the source error is absorbed
uniformly in every odd adaptive depth. The actual main-sum and Euler
dictionaries preserve the same coefficients and cap. This gives the
matching cap-uniform upper threshold `2*exp(gamma)/3+eta`.

`ActualRosserAtThreeLimit` combines the two thresholds using `eta/2` and
takes their maximum before N and the covering cap. The ratio therefore
converges to `2*exp(gamma)/3` along positive even targets, for any cap
sequence that eventually covers `N^u`. The canonical ceiling cap is a
corollary. The proved Mertens normalization then gives

```text
actualSmallRosserPlusDensity N cap (N^u) (N^(3*u))
  * log N / singularSeries N -> 4/(3*u).
```

In particular, at `u=1/3, R=N` this constant is four.
`ActualRosserCubeLimit` uses the previously proved exact cube identity,
with reduced exponent `beta/3`, and the target-deleted Euler ratio
`V(N^(beta/3))/V(N^u) -> u/(beta/3)`. For fixed positive `u,beta` with
`beta<=3*u`, the same actual raw ratio tends to
`2*exp(gamma)*u/beta`, while the singular-series-normalized density tends
to `4/beta`. Thus the manuscript's upper raw-density identity is now
proved for every fixed `1<s<=3`. The formal result also has the literal
cube-identity extension to `0<s<=1`; it does not invoke a definition of
the classical sieve factor outside its usual domain.

These are fixed-parameter limits. Compact-parameter uniformity, the
upper raw-density identity for `s>3`, the lower-weight identity involving
`f(s)`, the causal boxed compiler, sharp K/certificate semantics,
restricted signed distribution, current Chen mean and Theorem 1.1 /
Corollary 1.2 remain open.

All eight new modules passed strict compilation and individual bundled
kernel replay. A single canonical environment importing all eight audited
all **77 distinct declarations**, including private and generated ones.
The per-module counts are 5, 19, 11, 8, 5, 5, 14 and 10 in the table order
below. Only `propext`, `Classical.choice` and `Quot.sound` occur
transitively; no declaration is unsafe or an unproved axiom. Earlier
kernel replays were reused only after matching source, compiled object,
binary, configuration, pin and log hashes. Independent
read-only reviews checked the recursive region and residual endpoints,
zero-dimensional volume, the almost-everywhere second Fubini extraction,
the source index, source-contract premises, cap/filter quantifiers and
both normalizations.

The full aggregate `lake build` passed with **9,677 jobs** (exit zero).
The eight sources, root, audit and pins were unchanged through verification
and build. Both actual supplier revisions match the manifest and their
tracked worktrees and indexes remained clean. Evidence is in
`.lake/main-theorem-verification-20261012/tail-integral/`:
`rosser-at-three-verification.json`, `rosser-at-three-declarations.json`,
`rosser-at-three-theorem-types.txt`, and `final-aggregate-build-status.json`.
This verifies the eight new modules, their joint transitive axiom audit
and the complete aggregate compilation. It does not claim complete-root
kernel replay or successful remote CI.

Reproduce this checkpoint with the pinned toolchain on PATH:

```sh
lake build
lake env leanchecker --verbose ImbalancedChen.FinitePiIntegral
lake env leanchecker --verbose ImbalancedChen.RosserOddTailRegion
lake env leanchecker --verbose ImbalancedChen.RosserOddTailIntegral
lake env leanchecker --verbose ImbalancedChen.RosserOddLayerIdentity
lake env leanchecker --verbose ImbalancedChen.ActualRosserAtThreeLower
lake env leanchecker --verbose ImbalancedChen.ActualRosserAtThreeUpper
lake env leanchecker --verbose ImbalancedChen.ActualRosserAtThreeLimit
lake env leanchecker --verbose ImbalancedChen.ActualRosserCubeLimit
lake env lean -DwarningAsError=true verification/RosserAtThreeAudit.lean
```

Frozen source SHA-256 values:

| Module | SHA-256 |
| --- | --- |
| `FinitePiIntegral` | `22c7e16d66361c4aec2913237c8b8866db59575d36c50416805094e351f5c54c` |
| `RosserOddTailRegion` | `4eeb475ca7edb37873d54bea4d95cdf9188f0d4a72ce7f35d7cb3f51c8d29501` |
| `RosserOddTailIntegral` | `4f2bfe4bcb92b9884f1f6bf1ba919cd117c794169ad9a8c659cb282a287e2d60` |
| `RosserOddLayerIdentity` | `150cdc0162e77d9110cb7f45e1fcf7db42da98a12633cdc6cdd06280f804ec5d` |
| `ActualRosserAtThreeLower` | `f1deb4194fbe76b30460d9895717365e20b32414108dc60aea5177d16ad0d78d` |
| `ActualRosserAtThreeUpper` | `707de374153818ed853f87fa86595243ac02931c396aa1367385cd292fc7d006` |
| `ActualRosserAtThreeLimit` | `da6d978db72fdb7f2d45468637a00987f1b2fdd104468199ee3f767702b8ed7f` |
| `ActualRosserCubeLimit` | `a2a2d04ca6fe2d1e53e311bdb880f945ce30e27a71203b8590c90aa498aef7a4` |

## Finite sums of odd-rank continuous lower contributions — 12 October

Nine new modules generalize the actual three-prime lower-contribution
argument to every fixed odd rank. `ActualRosserOddBox` proves every
alternating prefix gate, the active tail product and terminal crossing at
the same `ceil (N^beta)`. Its exact tail cardinality is `2*k`, and strict
order makes the boundary map injective within each rank. Empty tails and
empty box families are covered. `ActualRosserOddBoxFamily` sums separated
boxes before injecting into one actual boundary expansion, so the base
term one occurs once.

`RosserOddLogRegion` uses strict continuous prefix tests, proves the
total-tail-sum constraint from the geometric residual budget, embeds the
region in the provider's continuous region, and proves every coordinate
exceeds `s/3^(k+1)`. `LogPrimeBoxMesh` and `RosserOddMesh` provide disjoint
half-open inner grids and eventual coverage of every region point.
`RosserOddMeshIntegral` proves the actual mesh sums converge to the
Lebesgue integral using the compact box `[s/3^(k+1),1]^(2*k+1)` and the
dominator `(1/a)*(1/a)^(2*k+1)`, where `a=s/3^(k+1)>0`.

`ActualRosserOddLayerLower` scales those cells by `u>0` and proves the
lower contribution at `R=N^(s*u)` for each fixed `s>=1` with
`s/3^(k+1)<1`. The mesh is chosen before the target threshold. For every
`k>=1` this gives, at `s=3`,

```text
forall u > 0, forall eta > 0, exists N0 >= 2,
  forall even N >= N0, forall cap >= N^u,
    actualSmallRosserPlusDensity N cap (N^u) (N^(3*u))
      / actualSmallEulerProduct N cap (N^u)
        >= 1 + rosserOddLayerIntegral k 3 - eta.
```

`ActualRosserOddBoxUnion` further combines every box from a fixed finite
rank set in one boundary expansion. Boundary tails from two injective
tuples have equal cardinality only when their ranks agree. This makes the
rank images disjoint before summing and retains just one constant term.
The finite dependent set `K.sigma J` indexes all box thresholds and their
error allocation; empty rank sets and empty box families are included.

`ActualRosserOddFiniteLayers` takes the finite sum of the proved mesh
limits to choose one shared mesh index, then applies that joint box
theorem. For every finite set `K` of positive ranks, `u>0` and `eta>0`,
it proves one threshold before all later even N and covering caps with

```text
actualSmallRosserPlusDensity N cap (N^u) (N^(3*u))
  / actualSmallEulerProduct N cap (N^u)
    >= 1 + sum_{k in K} rosserOddLayerIntegral k 3 - eta.
```

The `u=1/3, R=N` specialization is also proved. All analytic inputs to
these finite-sum bounds are discharged; thresholds may depend on the
fixed finite rank set. The proof does not add separate fixed-layer lower
inequalities. The subsequent integral-identity checkpoint above identifies
the general layers and supplies the full lower direction at three. At
this earlier finite-sum checkpoint those steps were still open. The same-weight full density
limit, causal boxed compiler, sharp K/certificate semantics, restricted
signed distribution, current Chen mean and final main theorem remain open.

All nine modules passed strict compilation and individual bundled kernel
replay. A canonical environment importing all nine modules audited every
one of its **137 distinct declarations**, including private and generated
declarations, permitting only `propext`, `Classical.choice` and `Quot.sound`
transitively. The module counts are 14 odd-box, 4 box-family, 30 generic
mesh, 23 odd-region, 21 odd-mesh, 30 mesh-integral, 6 single-layer lower,
4 cross-rank box union and 5 finite-layer sum declarations.

The four earlier inventories contained 138 provenance records with one
repeated, automatically generated `rosserOddMeshLowerSum.eq_1`. The initial
union-count assertion failed and was retained as a failed evidence record.
The additional canonical audit resolved the actual owner as
`ActualRosserOddLayerLower`, recomputed transitive axioms in the joint
environment, and verified that its name set equals the earlier inventories'
unique union. The final declaration count comes from this canonical audit.
Individual kernel replays were reused only after exact source, object,
binary, configuration, pin and log hash checks.

Independent read-only reviews checked the literal ceiling endpoints,
actual boundary weights, same-rank injection, cross-rank disjointness,
single base term, genuine region integrals, compact domination, empty
families and the order of mesh/threshold/target/cap quantifiers. The pinned
mathlib and goldbach revisions and their tracked worktrees and indexes
were checked around verification. Evidence is recorded in
`.lake/main-theorem-verification-20261012/odd-box/` under
`odd-layers-verification.json`, `odd-layers-declarations.json` and
`odd-layers-theorem-types.txt`, with the canonical audit in its
`canonical-audit/` subdirectory. These are nine individual module replays
and a joint new-module axiom audit, not complete-root kernel replay.

The final aggregate `lake build` passed with **9,663 jobs** (exit zero).
All nine source hashes, the root, five audit sources and dependency pins
were unchanged across verification and the build. The actual mathlib and
goldbach tracked worktrees and indexes remained clean after the build.
The aggregate result is recorded in `final-aggregate-build-status.json`.
This local checkpoint does not claim successful remote CI.

Reproduce this checkpoint's module checks with the pinned toolchain on PATH:

```sh
lake build
lake env leanchecker --verbose ImbalancedChen.ActualRosserOddBox
lake env leanchecker --verbose ImbalancedChen.RosserOddLogRegion
lake env leanchecker --verbose ImbalancedChen.LogPrimeBoxMesh
lake env leanchecker --verbose ImbalancedChen.ActualRosserOddBoxFamily
lake env leanchecker --verbose ImbalancedChen.RosserOddMesh
lake env leanchecker --verbose ImbalancedChen.RosserOddMeshIntegral
lake env leanchecker --verbose ImbalancedChen.ActualRosserOddLayerLower
lake env leanchecker --verbose ImbalancedChen.ActualRosserOddBoxUnion
lake env leanchecker --verbose ImbalancedChen.ActualRosserOddFiniteLayers
lake env lean -DwarningAsError=true verification/OddLayersAudit.lean
```

Frozen source SHA-256 values:

| Module | SHA-256 |
| --- | --- |
| `ActualRosserOddBox` | `2beffd8af22239e3a5428713c614e8e37bcbb300b16c950ff254d2c9ba031888` |
| `RosserOddLogRegion` | `a261b313c8a3c3179c7d3bb1f4d73fbc59c76787c89f8086db415f0408ad3452` |
| `LogPrimeBoxMesh` | `87a74de7869ba717f40441baf074d47271444d8641fcea63d21a39bfc3f6be7d` |
| `ActualRosserOddBoxFamily` | `74b06cb2b72c109f8482c1cb3e40b8b1f2cfe2d2e5cfe5522f2c50460f7b9a3e` |
| `RosserOddMesh` | `d99f1ea021f4976eef94f8796260873870b4171a944b481477a9328aa22d2cbc` |
| `RosserOddMeshIntegral` | `daf9a51c5c0d803916947b0c77632588839b6a73e04e64f4514b03f0d4a5483e` |
| `ActualRosserOddLayerLower` | `c25a9b09b0d15319e3e75f0cf0a5ae3b3d33cacf572f34cb54704f0a5c4a4cfa` |
| `ActualRosserOddBoxUnion` | `676c703060700b25dc21d1ac1ca3933b8839181255fec1cf88c9c1aaf459115a` |
| `ActualRosserOddFiniteLayers` | `1bfa43451c53fbf272566a2d7f8dfe0360a94cba3e7db5e877daf3b905057c11` |

## Historical checkpoint with full remote replay

Commit `50c355b3260da1699447df805f0a58e74e4e465e` passed full build, exact replay of all 84 owned modules plus the root (85 targets), and the 2043-declaration standard-three-axiom audit in [PR run 37880137858](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37880137858) and [push run 37880133970](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37880133970). Both proof-gate sequences finished before optional cache handling; the PR merge tree matches the head tree. The new symmetric-triangle integral module is CI-pending toward an 85-module checkpoint and 86 replay targets. Its source presence does not extend the verified checkpoint or establish a new audited declaration count.

## Initial core

- Arithmetic definitions count each additive prime once.
- Finite good/bad count partition and subtraction.
- Exact rational endpoint comparisons and logarithmic transfer margins.

The endpoint comparisons take the displayed rational numbers as numbers; they do not prove that those numbers bound the analytic integrals.

## Concrete normalization

The new source proves convergence and strict positivity of the actual odd-prime Euler product and bounds the finite correction below by one. It derives growth of `C(N) N / (log N)^2`, then discharges the unit-absorption premise of the numerical transfer. These additions passed compilation, module replay, and the 177-declaration transitive axiom audit at commit `a6f206076b77e42a2bcd4d656031ea0751dd7c8a`. The resulting concrete transfer retains the actual Chen count lower estimate and bad-count upper estimate as explicit, unproved analytic inputs.

## Outstanding mathematical work

- Prove the analytic distribution and main-term estimates for the now-instantiated actual finite sieve.
- Keep compilation, module replay, and transitive axiom audits passing for each new analytic module.
- Prove the asymptotic bad-semiprime removal bound.
- Formalize the actual distribution and strengthened sieve interfaces, with all uniformity and order-of-limits hypotheses.
- Formalize the geometric and analytic meaning of the numerical certificates. Nine required author/independent/final-transfer replays have completed with matching mathematical fields, including the full extended run. This does not establish every analytic/table dependency in the package.
- Prove the separate Chen lower count and then deduce the final every-sufficiently-large-even-N conclusion.

The external-input exponent 0.74774 additionally requires the published 1.9728 Chen count; it is not an axiom in the verified core.

## Frontier interpretation

The proposed separate exponent 0.76407 improves the directly stated Li-Liu 0.9 theorem and 0.894 remark, if the draft is valid. It does not improve the manuscript's 0.749 deduction from accepted published inputs plus localization. The proposed external-input exponent 0.74774 improves that specific numerical deduction. No global priority or best-possible claim is made.

## CI contract

A green build means only the committed core compiled. CI also rechecks with leanchecker and audits transitive axioms under ImbalancedChen, allowing only propext, Classical.choice and Quot.sound. No custom analytic axioms, sorryAx or native_decide trust extensions are accepted.

## Verified checkpoint

Commit `a6f206076b77e42a2bcd4d656031ea0751dd7c8a` passed both push and PR checks. [PR run 37752040466](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37752040466) records build success, verbose replay of all eleven modules and the root, and 177 audited declarations within the standard three-axiom allowlist. The earlier full-Mathlib import run exceeded its kernel-replay time budget; focused imports resolved the observed bottleneck without removing a proof check. Lean/mathlib dependency artifacts remain explicitly pinned and trusted, rather than independently rebuilt from first principles.

## Verified localization checkpoint

Commit `26c128d85f45fd0ddd7719459d56fcb112fc582c` passed the full thirteen-module build, module replay, and 238-declaration axiom audit. [PR run 37754452855](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37754452855). The actual bad source is reindexed exactly, cut off using the literal real threshold and its natural ceiling, and its discarded contribution is proved negligible relative to the actual normalization. This pays only the small-receiver localization cost, not the retained-source sieve estimate.

## Verified sieve-source checkpoint

Commit `cf59a1fe88d8caf85b0a0a32549ec73b5e2c0078` passed the seventeen-module build, module replay, and 328-declaration axiom audit. [PR run 37756197691](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37756197691). The inclusive half-product source, unique ordered-pair count including squares, actual sieve product, source/modulus coprimality, and primitive shifted congruence are proved. The original logarithmic cutoff eventually clears the fifth-root cap, and fixed sublinear power-logarithm costs (including rounding) are negligible in the genuine normalization. These preparation theorems do not prove a level-sensitive upper sieve or the 6.786 analytic coefficient.

## Verified finite-sieve checkpoint

Commit `631466a7e36dc1c381813349a75decc345d8a24d` passed the eighteen-module build, module replay, and 369-declaration transitive axiom audit. [PR run 37758586617](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37758586617). The actual shifted source now instantiates mathlib’s `BoundingSieve`, retaining its inclusive endpoint, literal total mass, reciprocal-totient density, and exact congruence remainder. Upper-Möbius and lambda-square inequalities follow from proved mathlib theorems. The added level-truncation module is awaiting CI; neither its finite identities nor the model supply the outstanding analytic main-term/distribution estimates.

## Verified finite-level and Euler checkpoint

Commit `0ae2058371ec1b96da233fef42f882003e6d63a1` passed the twenty-module build, module replay, and 415-declaration transitive axiom audit. [PR run 37760141802](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37760141802). Input support at `L` yields exact lambda-square support at `L * L` and exact restrictions of the actual main/error sums. The finite Euler identity proves the prime-two normalization and the center-divisor correction, including its zero-center edge case. Allowed squarefree Selberg terms are explicitly products of `1 / (p - 2)`. No asymptotic approximation, optimized analytic coefficient, or distribution estimate follows merely from these finite identities.

## Verified center-tail and normalization checkpoint

Commit `a83fbaa87dc9adf211f844dccec4530642e8eb44` passed the twenty-two-module build, full project-module replay, and 511-declaration transitive axiom audit. [PR run 37764236666](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37764236666). At the actual fifth-root cap, the omitted center-prime correction differs from one by at most `62 / N^(1/5)` for `N ≥ 1024`. Strict-cap Euler-product exhaustion and this bound prove the actual density normalization tends to one along positive even centers. The ordinary prime Euler product is left explicit; no Mertens estimate or analytic sieve bound is inferred. The added finite dimension-comparison module is awaiting CI.

## Verified finite dimension comparison

Commit `b71e40a9b865d094e8a065273f8eb3261d5e3e62` passed the twenty-three-module build, full project-module replay, and 551-declaration transitive axiom audit. [PR run 37765367998](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37765367998). Exact density quotients retain half-open prime intervals and center-divisor exclusions. Removing center primes decreases the quotient uniformly, including the zero-center case. The logarithmic dimension estimate still requires an analytic supplier. The added curved-boundary discrepancy module is awaiting CI; it retains the full upper-envelope carrier and leaves all analytic rectangle and boundary-mass estimates open.

## Verified finite curved-boundary transfer

Commit `c51f61079a16959ffa488070996105147d9dd292` passed the twenty-four-module build, full project-module replay, and 583-declaration transitive axiom audit. [PR run 37767807142](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37767807142). The finite curved-boundary inequality retains the full envelope carrier, the actual coprime normalization, and the reciprocal-totient modulus sum. The new reciprocal-totient module proves an unconditional finite bound by `4 * (1 + log(max(1,D)))`, including the empty cap, and composes it with this source inequality. That module is awaiting CI. Rectangle distribution and quantitative boundary lattice-point estimates remain open.

## Verified reciprocal-totient boundary cost

Commit `9d3965f8bfa82012172deb837ac09f7d04e8ec3a` passed the twenty-five-module build, full project-module replay, and 608-declaration transitive axiom audit. [PR run 37772490738](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37772490738). The reciprocal-totient logarithmic bound is unconditional for every natural cap, and now supplies the actual boundary transfer's modulus cost. The new BoundaryGridBudget module proves the four integer-pair collar counts with separate endpoint costs, and preserves repeated products through exact fibre-cardinality mass on a full carrier. This new module awaits CI. Constructing the multiplicative grid, proving its collar containment and obtaining the actual rectangle distribution remain separate tasks.

## Crossing-cell containment candidate

BoundaryCellContainment proves local containment from genuine inside/outside witnesses in one positive multiplicative rectangle, uniformly for `0 ≤ b ≤ 1` and `0 ≤ δ ≤ 1`, with common collar width `3δ`. It also derives the smaller diagonal cap, handles exact natural restrictions of half-open cells using ceiling endpoints, and identifies the actual prime-pair predicate with the real curved region. Source review is complete; CI is pending. Global grid construction and actual cap selection are not assumed completed.

## Global boundary-mass candidate

BoundaryGlobalCaps derives the actual square-root and power coordinate caps from the inside witnesses, even when the crossing cells vary pointwise. With exact outward ceilings and `0 ≤ δ ≤ 1`, `0 ≤ T ≤ N`, `N ≥ 1`, `0 ≤ b ≤ 1`, it proves the finite pair count and full-support convolution mass are at most `12δN log(3N) + 216δN + 14N^(1/(1+b))`. This is a proved estimate under a genuine crossing-cell cover, not an assumed cardinality bound. Source review is complete; CI is pending. Construction/enumeration of the actual grid and the analytic rectangle-distribution supplier remain open.

## Verified global boundary geometry

Commit `1da81e3eb3f4ccb520b324e494a60ada53f0943b` passed the twenty-eight-module build, full project-module replay, and 670-declaration transitive axiom audit. [PR run 37776793972](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37776793972). The four-collar count, genuine cell-crossing containment and explicit global boundary mass bound above are now verified. The new MultiplicativeGridPartition module constructs exact ceiling-restricted half-open sides, proves unique ownership and full exterior coverage, and counts indexed rectangles as `(floor(log N / log κ) + 1)^2`. This new grid module awaits CI. The actual inside/intersecting prime-pair convolution envelopes and analytic rectangle distribution remain to be connected.

## Verified grid and actual envelope candidate

Commit `d0df6440e198d6d808e43b04927af4964ae69a7e` passed the twenty-nine-module build, full module replay and 710-declaration transitive axiom audit. [CI run 37777875119](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37777875119). The exact finite multiplicative partition and rectangle count are verified. ActualGridEnvelopes now constructs full prime rectangles, lower and upper convolution envelopes, the exact boundary difference, and its full-carrier mass bound using the verified crossing geometry. It retains exterior products and repeated-product multiplicity. This candidate awaits CI; the analytic rectangle-distribution theorem remains open.

## Verified actual prime-rectangle envelopes

Commit `8472a8eb910230e5c1f34fd756b01f33dbc6ec20` passed the thirty-module build, full project replay and 747-declaration transitive axiom audit. [PR run 37778918460](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37778918460). The actual inside/intersecting prime rectangles, their pointwise sandwich and boundary-fibre mass estimate are now verified. The analytic distribution of rectangle convolutions and its weighted sieve use remain outstanding.

## Logarithmic-mesh boundary candidate

BoundaryLogMesh proves the full actual boundary mass times the reciprocal-totient cost is eventually at most any positive epsilon times the genuine singular normalization, uniformly in `0 <= T <= N` and `D <= N`, for every fixed rational `0 < b < 1` and natural mesh exponent `k > 4`. It retains all exterior products and the complete sublinear rounding term. Source and independent review passed; CI is pending. This does not estimate rectangle discrepancies.

## Verified negligible boundary cost

Commit `55f0454f4660a15783b824a42b5f350e6e5cc21e` passed the thirty-one-module build, full replay and 772-declaration axiom audit. [PR run 37783303734](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37783303734). The actual logarithmic-mesh boundary cost is now verified negligible. Three additional finite adapters await CI: exact assembly into literal full-rectangle discrepancies; reduced-residue recentering around an arbitrary common main; and explicit polylogarithmic grid count. No analytic rectangle distribution is assumed proved.

## Verified finite adapters (8 October 2026)

Commit `dd71a02a2a63c79535d109d50d15fe6f1a502310` passes all three checks in run [37785412931](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37785412931): 34 modules and 824 audited declarations. BoundaryLogMesh, RectangleDiscrepancyAssembly, CoprimeRecentering and LogMeshGridCount now have actual CI verification. The full boundary cost tends to zero at the genuine normalization; rectangle discrepancies retain all exterior points and multiplicities.

The new SelectedGridRanges candidate proves exact ceiling-minus-one endpoints, full product cap `4N`, and eventual lower gates for every fixed real logarithmic exponent, uniformly over selected cells and grid ratios. It awaits CI. No rectangle distribution theorem is assumed or proved by this geometric module.

## Selected ranges verified; assembled reduction pending

Commit `65123d7dd1a36024bd5f4666e00041f031e67bbc` passed build, full kernel replay and the 855-declaration axiom audit in [run 37786702405](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37786702405). SelectedGridRanges is now verified. CurvedDiscrepancyReduction is the next independently reviewed candidate: it combines the actual rectangle sum and the proved negligible boundary at the literal logarithmic cutoff, with no analytic rectangle estimate as a premise. It awaits CI.

## Assembled curved reduction verified

Commit `ff9af51a937c6980e66d61ba2140a83adb561a82` passed all three checks in [run 37787861592](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37787861592), with 36 modules and 858 audited declarations. The remaining curved error is explicitly bounded by the sum of literal full-rectangle errors plus a proved epsilon-normalization boundary cost. PrimeRectanglePrefixes is the next independently reviewed finite candidate, providing exact upper-minus-lower prime-prefix identities and matching actual coprime mass. It awaits CI; the analytic distribution estimate remains separate.

The ResidueSelectorBudget candidate now supplies the finite maximum-selection step needed to preserve a sum-over-moduli bound under recentering. Its analytic estimate is explicitly conditional: no distribution bound is asserted by this finite module. PrimeRectanglePrefixes first CI found only proof elaboration failures in membership rearrangement and product sum rewriting; these are being corrected without changing statements. Both candidates await complete CI.

## Prime-prefix and selector adapters verified

Commit `94ac28d470dd911057aad75aa94be3f30eecebe8` passes all three checks in [run 37791411370](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37791411370): 38 modules and 918 audited declarations. PrimeRectanglePrefixes and ResidueSelectorBudget are now verified, including exact actual counts, coprime means, ordered-pair multiplicities and the factor-two selector-sum transfer. One specialization needed explicit intermediate source identities and a scoped elaboration budget; no statement, axiom whitelist or kernel check was weakened. The prime-convolution analytic supplier remains separate from these proved finite adapters.

RectanglePrefixBudget is the next independently reviewed finite composition: its explicit raw prefix input budgets give actual coprime-normalized full-rectangle error at cost `2Bhi + 2Blo`, including actual grid endpoints and the empty modulus interval. It awaits CI. This conditional finite transformation supplies no analytic prefix estimate. The documentation-only 38-module checkpoint `b78f3dfdc4a106463e4b48334b170cef4666f879` also passed all three checks in run 37792561374.

## Enlarged-ambient quantitative budget candidate

ScaledRectangleBudget independently proves that a fixed stronger logarithmic modulus exponent pays the change from N to 4N, including the exact natural floor. Its literal selected-cell count bound absorbs the factor four from two-prefix recentering and the enlarged numerator at cost 144 C N/log(N)^A. Choosing fixed input accuracy 2(k+1)+3 makes this numerical budget negligible in the genuine singular normalization. This is unconditional quantitative bookkeeping; it neither assumes nor proves the analytic prefix distribution theorem. Both this module and RectanglePrefixBudget await actual CI acceptance.

## Verified enlarged-ambient budget checkpoint

Commit `46cc4fe9ef9d6bd37e3472c1132673ceb97884c9` passed all three verification stages in [run 37799094466](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37799094466): 40 modules and 948 audited declarations. Both RectanglePrefixBudget and ScaledRectangleBudget are now verified. The only new build correction was an explicit real type on a natural-number nonnegativity fact; all statements and checking stages were preserved. The composed rectangle estimate still has explicit raw-prefix inputs, and the enlarged-ambient module supplies unconditional parameter/error bookkeeping. The separate prime-convolution analytic supplier and its literal consumer remain outside this verified core.

## Verified weighted-error transfer and arbitrary-accuracy boundary

Commit `1656c2b752847e00120c20770fcf3ad923b09416` passed compilation, full bundled kernel replay and the transitive axiom audit in [run 37805811208](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37805811208): 44 modules and 1008 declarations, all within the unchanged standard three-axiom allowlist.

WeightedSieveError proves the actual source progression cap and `|R(d)| <= 3N/phi(d)` for positive moduli at most N, then transfers the unweighted discrepancy sum to mathlib's literal lambda-square error. The distribution sum is restricted to moduli coprime to N; no estimate at a nonprimitive residue is silently imported. DivisorMomentBudget proves the required allowed-squarefree moment is at most `[4(1+log max(1,D))]^16`, without a divisor-moment assumption. WeightedSieveLogBudget consequently shows that weights bounded by `log(N)^J` and an actual unweighted error at precision `2A+16+4J` imply the explicit squared weighted-error bound `3*8^16*C*N^2/log(N)^(2A)`. The unweighted distribution estimate remains an explicit input of that last implication.

BoundaryArbitraryLog independently proves the actual envelope-gap geometric cost is at most `epsilon*N/log(N)^A`, with the fixed mesh exponent `k=A+3` chosen before the eventual threshold and all finite cutoff/modulus choices. It retains the unestimated full-rectangle discrepancy sum. Compilation exposed two minor elaboration/API mismatches, both corrected without changing any statement or checking stage. The external prime-convolution supplier, its consumer, optimized sieve main term and full manuscript remain separate outstanding work.

## Explicit finite Selberg optimization verified

Commit `935f380696fed24dfa12d44c8e465f1a401b43e6` passed compilation, complete bundled kernel replay and transitive axiom audit in [run 37811236920](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37811236920): 46 modules and 1035 declarations within the unchanged standard allowlist.

ActualSelbergCoefficients constructs the actual finite normalizer and standard coefficients, proves G >= 1, normalization at 1, exact level/divisor support, and the coefficient bound |w(d)| <= 1 by a positive finite injection. The actual reciprocal-totient sieve specialization removes the coefficient-size hypothesis from the existing J=0 error transfer. ActualSelbergMain proves the transformed coefficient identity by Mobius cancellation and then evaluates mathlib's genuine lambda-square main sum exactly as 1/G. Its optimized finite sieve inequality retains the actual lambda-square error. These proofs use the recognized pinned mathlib and this project's own modules. The normalizer's asymptotic estimate, analytic distribution input and complete manuscript theorem remain outstanding.

## Actual optimized count and enlarged-cap geometry verified

Commit `44d3b99086d559194245a3b871facb254603179d` passed all three checks in [run 37813639838](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37813639838), with 47 modules and 1038 declarations. ActualOptimizedSieveBound connects the genuine sifted count and source cardinality to the literal normalizer and the exact primitive discrepancy; the square-root error bound retains its explicit unweighted analytic hypothesis.

Commit `d8f564f5987170343f44971f8570018a624b380f` passed all three checks in [run 37817371436](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37817371436), with 49 modules and 1081 declarations. FullNormalizerCarrier proves the exact squarefree, centre-coprime full sum when the strict cap exceeds the coefficient cutoff, including zero and unit endpoints. EnlargedSelbergCap proves the floor-power level, its squared distribution-level bound, the actual source roughness gate, and negligible discarded count for z=L+1. The original bad count is unchanged. Two small elaboration errors were corrected with explicit singleton membership and additive monotonicity, without changing statements or checks.

The manuscript's original fixed fifth-root argument uses the linear upper sieve. The finite Selberg denominator at that same cap cannot silently be replaced by the unrestricted squarefree sum when L>z. The enlarged-cap construction avoids this carrier mismatch for an alternative route to the original coefficient 8, but no asymptotic coefficient is yet proved in the owned core. The refined K=6.786 route remains separately outstanding.


## Exact mass and singular-product bridges verified

Commit `dd5a7e95a2e1d37d8d1b03f378d09bcb84b8d7e0` passed all three stages in [run 37821907221](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37821907221): 52 modules and 1151 declarations, with the unchanged standard axiom allowlist. SingularProductIdentity transports actual HasProd convergence to the natural-index formula and proves the centre correction and exact factor two. HalfProductMassFibres converts the original source to a smaller-prime sum with the strict ceiling-minus-one boundary, includes prime squares, and bounds its actual real-cutoff loss. MassLogIntegral reuses the existing FTC evaluation and proves the fixed-test logarithmic conversion. Explicit type annotations and a pointwise denominator reduction repaired elaboration errors without weakening statements or checks.

The actual source mass asymptotic still requires analytic PNT and weighted-prime inputs to be connected and audited. Further high/low finite bounds and conditional PNT transfers are under CI development; neither their existence nor this checkpoint proves the refined constant K=6.786 or the full manuscript.


## Original-source mass transfer verified

Commit `6958f5007d1ce8bd1617979cf6d43294b218d727` passed compilation, full bundled kernel replay and the unchanged transitive axiom audit in [run 37823648102](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37823648102): 56 modules and 1212 declarations. HalfProductMassSplit proves the actual finite high/low envelope, preserving square pairs and strict boundaries. UniformPrimeTail extracts a common moving-endpoint threshold from an explicit real-PNT error witness. HalfProductMassError pays the prime rectangle, ordering and literal logarithmic-cutoff losses. HalfProductMassLimit proves the original source mass limit with coefficient log(den/num) from that PNT witness and the literal fixed-test reciprocal-prime Mertens limit. Neither input assumes a half-product count or the desired bad-count bound.

An omitted section-variable inclusion was corrected so every intended PNT transfer explicitly takes its PNT premise. The actual external PNT/Mertens producers and full-normalizer supplier still require their own consumer integration and validation. This checkpoint is not an unconditional proof of the manuscript or of its refined sieve coefficient.


## Actual eleven-term pointwise inequality verified

Commit `8d29cfb52fdf3b9bece7eb4dff7494c3f59f138a` passed compilation, complete bundled kernel replay and the unchanged transitive axiom audit in [run 37831691122](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37831691122): 64 modules and 1504 declarations. The seven added modules prove literal tuple supports and counts for all eleven terms, actual smallest-factor switching geometry, the ninth-term lower bound, and the complete fixed-exponent pointwise inequality on the original squarefree size band. The eleventh term retains its full fourth-prime range. The rough prime-square exception bound counts positive integers once and retains its exact finite denominator. No analytic mean lower bound is supplied by this checkpoint.

The next three candidate modules sum the actual weight over original coprime additive primes, pay a once-only union of small and nonsquarefree rough receivers, expand all eleven actual Upsilon terms, and retain the receiver-one correction. Their finite error is explicit; these additions require their own CI validation. The analytic lower supplier and refined K=6.786 remain outstanding.


## Actual summed Chen weight and its exact error verified

Commit `ff63156d20fef1367d64d83c25a6e4c5222810a2` passed compilation, bundled kernel replay and the unchanged transitive axiom audit in [run 37834153478](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37834153478): 68 modules and 1579 declarations. QuotientChenPositiveBound proves a uniform positive upper bound 246 without assuming squarefreeness or the lower size band. QuotientChenSummedBridge uses the actual prime carrier and an injective complement map, paying a union of exceptional receivers once with the literal ceiling and prime-square denominator. QuotientChenElevenSum expands all eleven actual Upsilon terms, retains full Y11, proves the original inclusive endpoint equivalence, and pays the receiver-one correction. ChenWeightErrorBudget proves the eventual size gate and absorption of the exact 984 N^(1-100/1149)+4 loss in the actual singular normalization. Its lower-mean and final good/bad transfers retain the two independent analytic estimates explicitly; they do not prove c=1.8271 or K=6.786.

The two CI repairs only made a finite-product cast explicit and corrected addition orientation. Statements, hypotheses, source carriers, and verification stages were unchanged.


## Genuine initial Chen prime source verified

Commit `14e30da801c06756503f98df6f319e333e3df1d6` passed all three unchanged verification stages in [run 37837185549](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37837185549): 69 modules and 1652 declarations. ChenInitialPrimeSource constructs a genuine BoundingSieve on the injective complement image of the original additive-prime carrier. Its actual cardinality, unit weights and local reciprocal-totient density are explicit. Upsilon1 and Upsilon2 equal its sifted sums with the strict real-cutoff ceiling, including receiver one. All divisibility fibres are literal inclusive prime AP counts with exact centre-prime and modulus-prime corrections, including moduli zero and one where the identities permit them. Five elaboration fixes did not change the mathematical statements. Analytic remainder estimates and the linear lower sieve are still separate producers.


## Initial-prime corrections verified

Commit `8244391cfeacc0cbb389ba24260cfe34c39935eb` passed compilation, bundled kernel replay and the unchanged transitive axiom audit in [run 37840265664](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37840265664): 70 modules and 1695 declarations. ChenInitialCorrectionBudget proves a logarithmic bound for actual prime-divisor counts, retains the signed modulus-prime atom and all centre-prime corrections, and pays their complete selected-modulus sum at arbitrary fixed logarithmic accuracy for D <= sqrt N. The three CI corrections only parenthesized the complete additive summands. Ordinary prime-AP distribution remains an explicit input in the core transfer; an actual supplier consumer is being checked separately on the unchanged approved external BV closure.

The next core-only candidate ChenLogLevelGeometry defines Q = floor(sqrt N / (log N)^B), D = Q+1 and proves the logarithmic limits and all numerical lower-Rosser gates at one common eventual threshold for fixed real B >= 0 and 0 < a < 1/4. It retains D-1 = Q and bounds Q, not D, by sqrt N. No sieve estimate or distribution conclusion is assumed or obtained in that numerical-geometry module.


## General real-power centre correction candidate

CenterEulerTail reuses the existing exact finite split at ceil(z). For N > 0 and z >= 4 it proves 1 <= tail(N,z) <= exp(2 log N / (z log 2)), and hence tail(N,N^a) and the strict-small/full correction ratio tend to one for every fixed a > 0 as the centre itself varies. The all-centre threshold is explicit in its quantifier order. This does not substitute a fixed-centre limit for the required uniform conclusion and does not assert the full sieve-density asymptotic.

Run 37845167459 caught one addition-orientation elaboration error in ChenLogLevelGeometry. Its repair replaces only that proof application with an explicitly oriented add_le_add; statements and gates are unchanged. Both new candidates await a successful complete CI run.


## Logarithmic level geometry and uniform centre tail verified

Commit `6d1a5b7513317e52a74b44236405b46063237763` passed all three unchanged stages in [run 37846923822](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37846923822): 72 modules and 1741 declarations, using only propext, Classical.choice and Quot.sound. Both candidates above are now verified. The two CenterEulerTail repairs made addition orientation and function composition explicit without changing any statement or definition. Initial analytic distribution and normalization consumers are being tested separately; the full eleven-term mean lower bound remains open.

## Actual quotient-prime source extension (verification pending)

The new `ChenQuotientPrimeSource` keeps original additive-prime labels and constructs their exact quotient receivers after selecting a divisor `b`. Every quotient divisibility fibre has product modulus `b*d`, not `lcm(b,d)`, and subtracts the genuine centre-prime contribution in that AP. The formulas include zero and unit moduli and do not require squarefree receivers. Exact finite Fubini identities give the original Upsilon 3–6 sums with the original prime bands and pair multiplicities. No generic `1/phi(d)` density is asserted for shared primes of `b` and `d`. This addition supplies no analytic upper/lower bound. Its new CI verification is pending.

## Actual quotient-prime source verified; finite remainder extension pending

Commit `99b55944dd9cc35011c50265dbfd2a35b0f12f19` passed full compilation, bundled kernel replay and the unchanged transitive axiom audit in [PR run 37863090429](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37863090429) and [push run 37863085648](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37863085648): 73 modules and 1795 declarations, using only propext, Classical.choice and Quot.sound. The quotient-source extension above is therefore verified. Its CI repairs only made natural-number positivity and filtered-set membership proofs explicit.

The new ChenQuotientSieveRemainders candidate constructs the actual quotient BoundingSieve and identifies each original Upsilon 3–6 sum with its genuine sifted counts. It proves strict-cutoff multiplier coprimality and the density ratio phi(b)/phi(b*d)=1/phi(d) for positive b and allowed d. For arbitrary comparison M the exact remainder is E(b*d)-E(b)/phi(d)+C(b)/phi(d)-C(b*d), with C the actual centre-prime AP count; the finite absolute-error transfer retains both positive correction costs. Centre-prime corrections do not vanish merely because gcd(b,N)=1. This module has independent mathematical review and exact finite regressions, but awaits CI compilation and kernel/axiom checks. No selected-multiplier analytic error bound or manuscript lower bound is asserted.

## Quotient sieve remainder interface verified; pooled correction candidate

Commit `655510e9f75b6f4a876b9c5c3fc6afc1b0cf9736` passed compilation, bundled replay and the unchanged axiom audit in [PR run 37864869571](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37864869571) and [push run 37864865543](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37864865543): 74 modules, 1829 declarations, only propext, Classical.choice and Quot.sound. The six repairs made simplification order, the real denominator cast and attached-sum identities explicit, preserving every statement. The finite quotient-remainder extension above is now verified.

The new ChenQuotientCentreBudget candidate proves finite centre incidence pooling. At a positive nonprime centre every exceptional receiver N-P is positive; selected divisor primes lie in its prime-factor set, and selected ordered pairs lie in the square of that set. Summing over centre primes gives two or three logarithms, without an outer-selector cardinality loss. For d>0 the complete cost C(b)/phi(d)+C(b*d) is at most 2 C(b). Hence all four actual terms have total correction cost at most 8/(log 2)^3 sqrt(N) log(N)^3 under the stated finite gates, and arbitrary fixed logarithmic accuracy follows uniformly over all row-dependent modulus families below sqrt(N). Nonprimality is derived from Even N and N>=4 in the eventual statement. This candidate has independent source review and exact arithmetic regressions; CI verification remains pending. Ordinary AP errors, the lower sieve and the full eleven-term mean are separate obligations.

## Pooled centre budget verified; product-modulus pooling candidate

Commit `af4eb77d48f9a13df138e566f5718a262face9ab` passed all unchanged gates in [PR run 37866504321](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37866504321) and [push run 37866499717](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37866499717): 75 modules and 1869 declarations, standard three axioms only. ChenQuotientCentreBudget passed without any proof repair. The unconditional pooled centre-cost estimate described above is now kernel-verified.

The new ChenPooledQuotientAP candidate proves exact labelled pooling using gcd recovery of the allowed small-prime divisor, then positivity/centre-coprimality of the full product and injectivity of the original selected prime or ordered pair. It bounds the primary product-modulus AP error by the single primitive global AP-error sum without an outer-cardinality factor, separately for each of the four original bands. Secondary base errors retain the reciprocal-totient logarithmic factor, and centre costs are explicit. Squarefreeness is proved for pooled moduli, not imposed on receivers. Compilation and kernel/axiom checks of this 26-declaration candidate remain pending.

## Product pooling verified; active-row assembly candidate

Commit `bfd027e1b07e66b83c805712fba4bcf006ad04f6` passed full build, kernel replay and transitive audit in [PR run 37867935386](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37867935386) and [push run 37867929999](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37867929999): 76 modules and 1895 declarations using only the standard three allowed axioms. Four proof-only fixes made Sigma component equalities, summand functions and addition orientation explicit.

The new owned-only ChenQuotientBVFinite candidate removes empty rows before bounding active multiplier ranges, then pools their secondary AP errors with the proved reciprocal-totient logarithmic factor. It defines the literal admissible four row families and the actual four absolute remainder sums, and proves their combined finite AP-pool-plus-centre-cost bound. Unused outer rows are handled by exact intersection identities before invoking the already verified centre budget; no extra global mask is imposed on the source. All original bands and unit absolute outer coefficients are retained. This nine-declaration finite module awaits CI; no ordinary BV theorem is imported into the owned core.


## Active-row assembly verified; quotient sieve-assembly inputs then pending

Commit `ea684bbe754d4cd19b08bdf3040d5cb9ede3aadf` passed the unchanged build, complete root/module replay and transitive axiom audit in [PR run 37869414153](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37869414153) and [push run 37869410790](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37869410790): 77 modules, 1915 declarations and only the standard three allowed axioms. ChenQuotientBVFinite is now verified. Its two proof repairs made a natural positivity conversion and a finite-sum equality transport explicit; statements, original row families and verification gates were unchanged. Genuine supplier-backed quotient-BV consumers remain outside this owned root.

At this 77-module checkpoint, the following three source additions were still awaiting full CI verification. The completed 80-module checkpoint below supersedes that pending status:

- ChenQuotientLevelGeometry defines the exact strict natural row level D_b = Q/b+1 and proves its full-product support equivalence for positive b, including unit and zero-cap edge cases. For every fixed real logarithmic exponent B and fixed beta < 1/2, its eventual logarithmic profile is uniform over positive b <= N^beta, with the threshold before b. A fixed positive sieve exponent a converts this to the actual row parameter. The four literal Upsilon 3–6 bands fit a common exponent 94847/236694 < 1/2 and hence the exact global BV cap eventually. A lower-parameter bound requires sigma < (1/2-beta)/a. The full sixth band is not shortened or assigned an invalid s >= 2 gate.
- ChenQuotientDensityTransport identifies only the actual prime product and reciprocal-totient density with the initial sieve at the same strict real cutoff. It preserves the explicit multiplier/product coprimality gate, excludes a prime equal to the cutoff, and transports Euler and local dimension products by exact equality. The mass, receiver support and remainder remain their genuine quotient objects. No analytic Mertens/dimension bound or moving-cutoff normalization is proved here.
- ChenQuotientMassFinite retains X_b = AP(N,N,b) - C_b, including the centre-prime correction for primitive multipliers. For signed label-dependent weights with C >= 0, |w| <= C and all selected b <= Q, its finite L1 error is bounded by C(4 E_Q + C_36), where E_Q is the primitive AP-error pool and C_36 is the complete four-term centre mass. Label injectivity is established before pooling, and cross-term overlap is paid by the factor four. The literal weighted actual mass minus its reciprocal-totient main coefficient is bounded by this L1 error. The centre mass alone is at most 4(log N/log 2)^3 under the stated eventual even-centre gates and is negligible at every fixed logarithmic accuracy after a fixed bounded coefficient.

All three modules import only the existing owned core and its already pinned Lean/mathlib dependency boundary. No foreign BV, normalization or lower-Rosser consumer is imported into the root. Their role is preparation for actual sieve assembly: uniform moving D_b, exact density transport, and finite weighted actual-mass replacement with its AP-error obligation still exposed. Applying a valid upper/lower sieve, controlling the moving coefficient, evaluating the weighted prime/pair main terms and proving the complete eleven-term lower mean remain separate steps. Neither coefficient 1.8271 nor the manuscript's main analytic theorem is claimed.


## Quotient geometry and finite mass verified; prime-window and moving-weight inputs then pending

Commit `beb8a4d03e5fb0148b17907b298c4f60d59895a9` passed unchanged full build, exact replay of all 80 owned modules plus the root, and the 1992-declaration standard-three-axiom audit in [PR run 37872524090](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37872524090) and [push run 37872519987](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37872519987). ChenQuotientLevelGeometry, ChenQuotientDensityTransport and ChenQuotientMassFinite are now verified. The sole repair replaced one omega positivity step with an explicit natural successor proof; no statement, hypothesis, source carrier or verification gate changed.

At this 80-module checkpoint, the following three source modules were still awaiting full CI verification. The completed 83-module checkpoint below supersedes that pending status:

- ChenPrimeHarmonicFinite relates the actual prime selector to its original centre-divisor mask, pays at most two atoms for the [A,U) versus (A,U] endpoint convention, and uses the proved reciprocal-square tail for the 1/(p-1) versus 1/p correction. For N > 0, 2 <= A < U, a nonnegative fixed bound M and |f| <= M on the closed endpoint window, its combined finite error is at most (2M log(N)/log(2) + 6M)/A. The varying centre mask is charged through prime-factor incidence; it is not dropped by a fixed-centre argument. No Mertens theorem or target harmonic limit is imported into this finite module.
- MovingWeightTransport bounds an error by a uniform summand bound times the total nonnegative carrier weight, rather than the number of labels. It turns compact uniform continuity of a fixed continuous test into a summable vanishing perturbation when both coordinates remain in the same fixed compact set and the total carrier mass is eventually bounded. The test can be signed. The mass bound, uniform coordinate approximation and any fixed-profile limit used for a final limit are explicit premises; an independent mass limit can supply the bounded-mass premise.
- ChenQuotientMovingWeight uses the verified uniform row geometry to place the actual parameter and logarithmic profile in a single fixed interval with positive padding. Its transport statements are uniform over positive multipliers in a fixed power range below the square-root exponent and retain every label. The nonnegative carrier-mass bound and analytic fixed-profile limit remain to be supplied for the intended prime or pair application. This module neither assumes the desired moving-profile conclusion nor grants a lower-positive sieve gate on the full sixth band.

These three elementary modules add no foreign consumer to the owned root and make no VariableEnvelope change. The genuine prime harmonic supplier adapter and the concrete moving-prime consumer stay separate and uncompiled here. A generic continuous-test pair limit, valid upper/lower-sieve assembly and the complete eleven-term coefficient remain additional mathematical and verification work. No coefficient 1.8271 or full Chen theorem is claimed.


## Prime-window corrections and moving-weight transport verified; finite pair geometry then pending

Commit `10431e573fa740649d0e213b760ded652456631a` passed full build, exact bundled replay of all 83 owned modules plus ImbalancedChen, and the 2024-declaration transitive axiom audit in [PR run 37876028643](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37876028643) and [push attempt 2 of run 37876023661](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37876023661), using only propext, Classical.choice and Quot.sound. Both complete logs have identical replay sets and axiom counts, and the PR merge tree matches the head tree. The harmonic repair added explicit natural filter binders, corrected negated-equality symmetry and closed the zero inequality. MovingWeightTransport and ChenQuotientMovingWeight were unchanged.

The first push attempt at that repaired head built and passed the axiom audit but skipped kernel replay after disk exhaustion during optional cache archiving; it was not full verification. The successful retry used the same source and workflow. Cache compression still warned about disk space in the successful jobs, so proof success is not a claim that a cache archive was saved. No mandatory proof gate was weakened or bypassed.

The new owned-only ChenPairHarmonicFinite candidate preserves the original Y5/Y6 selectors, their half-open endpoints, centre-coprimality masks and pair labels. Y6 is exactly the product of its two disjoint prime bands, whose common endpoint belongs to the second band and forces strict order. Y5 is the strictly ordered half of one masked square. For a signed symmetric kernel, its exact harmonic identity is one half of the tensor square minus one half of the diagonal. The off-diagonal denominator identity phi(pq)=(p-1)(q-1) is proved only for distinct primes; the artificial tensor diagonal uses (p-1)^2, never phi(p^2).

The candidate also proves separated-test factorization and exact log-product coordinates. Under A >= 2, M >= 0 and the displayed diagonal test bound on the selected finite carrier, the full diagonal is at most 8M/A in absolute value; its contribution to the half-square replacement is at most 4M/A. The reciprocal-square tail comes from the existing owned core. No infinite-series or prime-distribution estimate is assumed.

At this historical 83-module checkpoint, the finite pair module was still awaiting build, exact root/module replay and transitive axiom audit. The completed 84-module checkpoint below supersedes that pending status. It concerns finite harmonic main sums, not equalities replacing the original sifted Upsilon counts. Continuous-test pair limits, the actual sieve/main-term assembly, the coefficient 1.8271 and the full Chen theorem remain separate obligations. No foreign consumer or VariableEnvelope change is included in this core extension.


## Finite pair geometry verified; symmetric-triangle integral pending

Commit `50c355b3260da1699447df805f0a58e74e4e465e`, tree `854f7818ff685c8107f719e3e741fd4f3b0657ca`, passed full build, exact bundled replay of all 84 owned modules and ImbalancedChen, and the 2043-declaration transitive axiom audit in [PR run 37880137858](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37880137858) and [push run 37880133970](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37880133970). Only propext, Classical.choice and Quot.sound were used. The finite pair-harmonic module described above is included. Both complete logs have identical replay sets and axiom counts, and the PR merge tree matches the head tree. Optional cache saving was skipped by the capacity guard after all required proof gates and evidence steps had completed; no proof check was skipped.

The new SymmetricTriangleIntegral candidate has three declarations, depending only on the already pinned mathlib boundary. The rectangular theorem assumes a <= b, c <= d and continuity of the uncurried real kernel on [a,b] x [c,d], and exchanges the order of interval integration without a symmetry assumption. The square theorem assumes a <= b, continuity on [a,b]^2 and symmetry there, and identifies one half of the square integral with the iterated integral whose outer variable t runs from a to b and inner variable u runs from a to t. The more general core replaces continuity by integrability on the genuine (a,b] x (a,b] square.

For the restricted Lebesgue measure, every singleton is null. Fubini therefore removes the diagonal from the product square almost everywhere. Off the diagonal, symmetry splits the kernel into its lower-triangle indicator and its coordinate swap. Integrability justifies addition and swapping, and the interval-indicator identity gives the displayed triangular limits. This works for signed kernels and does not require K(x,x)=0, global continuity, nonnegativity, or a target integral equality among the hypotheses. Degenerate rectangles and squares are covered by the weak endpoint inequalities.

Independent source review found a missing close for the anonymous noncomputable section. The local repair adds only the bare end before the named namespace end; all three statements and proof bodies are unchanged. The repaired source has static source/API and exact-polynomial checks, but no local Lean compiler or Lake executable is available. All three runtime gates remain pending. Adding the source and its one root import targets 85 owned modules and 86 replay targets; no post-addition audited declaration count is asserted.

The Lebesgue-null diagonal here is distinct from the finite tensor diagonal with denominator (p-1)^2, whose arithmetic vanishing estimate belongs to ChenPairHarmonicFinite. For the intended Y5 application the full weighted integrand, including 1/(u*v), must satisfy the actual square's continuity and symmetry conditions; on u <= t the larger-coordinate profile can then be rewritten at t. The Y6 rectangle swap likewise needs continuity on the genuine rectangle. This module does not prove a prime-pair limit, uniform moving-kernel approximation, lower-positive sieve gate, evaluated coefficient 1.8271, or the full Chen theorem. Foreign supplier-backed consumers remain separate, and no VariableEnvelope change is included.


## Arbitrary-real half-product localization candidate

The frozen source for this checkpoint is the 10 October 2026 manuscript at
`ba6ec11d800eccc54406490631895e174de85766`, with
`paper/source/manuscript-body.tex` blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.  The new
`RealHalfProductSource` module reindexes the arbitrary-real bad count by its
receiver, partitions it at a literal real cutoff, and identifies the retained
part with the inclusive ordered half-product source after the exact
`m < N ∧ Nat.Prime (N-m)` filter.  Multiplication is proved bijective on the
ordered prime-pair carrier, including prime squares, so the bridge introduces
neither factor-witness multiplicity nor a factor two.  The new module source
SHA-256 is `0c3211cb72d8f27eb380f57fe5d751f8fc3179cb646c683c1449d450c71c55e7`.

Local verification with the pinned Lean `v4.33.0-rc1` and Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` passed the targeted module build,
the complete project build and bundled `leanchecker` replay of
`ImbalancedChen.RealHalfProductSource`.  Direct transitive checks of the five
key exported results report exactly `propext`, `Classical.choice` and
`Quot.sound`.  A local root `leanchecker ImbalancedChen` process was killed by
the container memory limit (exit 137), so no local root-replay success is
claimed.  The independent local VariableEnvelope workflow separately passed
all module builds, exact regressions, eight bundled kernel replays and the
358-declaration transitive audit.  The required root replay, full root audit
and both remote workflows remain pending on GitHub Actions for the submitted
commit.

This is only the exact finite input to the current ordered mass argument.  The
later `RealHalfProductMassSplit` checkpoint now instantiates
`T_N = 2 N^(1-κ₀)`, proves its normalized small-tail error and gives the
conditional half-product PNT/Mertens limit `J_b = log(1/b)`.  The external
reuse audit in
`docs/CURRENT_MANUSCRIPT_MAP.md` records the same-pin real-exponent
prime-reciprocal interval theorem that can supply the outer logarithmic mass;
its moving product-boundary and fibre-uniformity obligations remain open.

## Arbitrary-real half-product coefficient candidate

`RealHalfProductMass` now proves the exact arbitrary-real exponents
`alpha = b/(1+b)` and `beta = 1/(1+b)`, including
`0 < alpha < 1/2`, `alpha < beta`, `alpha + beta = 1` and
`beta/alpha = 1/b`.  The two elementary moving walls are proved directly for
real powers: below the split, strict badness forces `q < N^beta`; above the
split, the product bound forces `q^b < r`.  No primality or ordering is hidden
in the latter implication.

The same module evaluates the literal fixed-test integral on
`(alpha,1/2]` as `log(1/b)`.  An exact finite equality identifies the literal
high-prime sum with the repository-local standard logarithmic prime interval
(strict lower endpoint and inclusive natural square-root endpoint).  Its
Mertens adapter assumes convergence only to that independently proved integral and concludes the manuscript coefficient;
it does not assume a half-product cardinality or the desired bad-count bound.
Exact rational-specialization lemmas identify both exponents and the weighted
sum with the existing `HalfProductMassLimit` definitions, preserving reuse of
the already-checked finite and uniform-PNT machinery.

The module source SHA-256 is
`90c809c15ce26cd1f4785b5117e2d8a5dcfdc5720480bc690d198d95f33601f3`.
Local verification passed its direct compilation, the complete `lake build`,
bundled module `leanchecker`, and direct transitive audits of seven key
exports; only `propext`, `Classical.choice` and `Quot.sound` occur.  The
independent VariableEnvelope workflow also passed all 358 declarations.
Remote verification remains pending.  The result is conditional on the actual
weighted-prime Mertens supplier.  The real source envelope with its moving
product boundary, uniform PNT application and current power-cutoff tail are
handled by the later `RealHalfProductMassSplit` checkpoint.  The actual
analytic suppliers and additive-prime filter remain open, so this module
alone is not `J_b = log(1/b)` for the actual count.

## Arbitrary-real source mass-split candidate

`RealHalfProductMassSplit` now supplies the missing finite bridge from the
literal arbitrary-real half-product source to the high-prime prefix sum.  It
proves an exact smaller-prime fibre decomposition, assigns equality at
`N^(b/(1+b))` to the low range, bounds that range by the complementary prime
rectangle, and pays the high ordering loss by `pi(sqrt N)^2`.  Prime squares
remain in the source and the strict/inclusive endpoints are unchanged.  A
second exact partition pays an arbitrary real cutoff by only its natural
ceiling.

The module formalizes the current manuscript lower wall as
`manuscriptHalfProductCutoff κ N = 2*N^(1-κ)`.  For every fixed `κ > 0` it
proves the cutoff plus its exact ceiling unit is `o(N/log N)`.  Reusing the
existing explicit real-PNT witness then proves the entire rectangle, square
and ceiling discrepancy at that literal power cutoff is `o(N/log N)` in
epsilon-eventual form.  It separately proves that uniform PNT turns the
prime-prefix approximation into the literal fixed-test weighted prime sum.
Consequently
`tendsto_realHalfProductSource_manuscriptCutoff_mass_of_real_pnt_and_weighted_mertens`
gives the full arbitrary-real source limit `log(1/b)` from precisely two
visible upstream inputs: the real PNT witness and the standard weighted-prime
Mertens integral (plus the proved elementary condition `κ > 0`).  No source
cardinality or target bad-count bound appears in either premise.  The older
`logCutoff = N/(log N)^10` result is retained as a historical auxiliary and is
not identified with the current manuscript cutoff.

The module source SHA-256 is
`6516890accb0179098fca79f98791adeddad569a858fc69710b87a8d3b92a3ca`.
Local verification with the pinned Lean/Mathlib revisions passed the direct
module compilation, the complete 2,865-job `lake build`, bundled
`leanchecker` replay of `ImbalancedChen.RealHalfProductMassSplit`, and direct
transitive audits of the five current-cutoff exports; the latter report only
`propext`, `Classical.choice` and `Quot.sound`.  The independent Variable
Envelope workflow also passed its explicit builds, exact regressions, eight
bundled kernel replays and all 358 declaration audits.  Root replay/full root
audit and remote CI must still pass for the submitted commit.  This remains
short of the actual `RealB` upper bound: the additive-prime filter must still
be estimated with the same positive upper sieve, and the two analytic
suppliers must be imported or proved and transitively audited.

## Arbitrary-real/rational finite-sieve bridge candidate

`RealHalfProductSieveBridge` closes the exact finite mismatch between the
current arbitrary-real theorem statement and the repository's rational
finite-sieve implementation.  It proves antitonicity in the exponent,
literal equality of real and natural-power sources at `num/den`, containment
of the strict prime-partner filter under every rational minorant, and the
cardinality bound by the rational sifted source plus the explicit cap `z`.
It then composes this containment with the already proved optimized finite
Selberg inequality, keeping the primitive-residue discrepancy hypothesis and
finite normalizer unchanged.  The whole-count corollary retains both `z` and
the exact real cutoff loss `T+1`; `RealB_le_B_of_rat_minorant` records the
corresponding monotonic rational reduction.

This candidate supplies no current-`K` density theorem.  The manuscript still
requires the same physical coefficient in the pointwise nonnegative upper
weight, its density estimate, and the restricted signed distribution theorem,
as well as a licensed positive smooth outer approximation to the sharp bad
region.  The existing finite Selberg normalizer has not been equated to that
physical construction, so this is not the completed filtered `RealB` bound.

The module source SHA-256 is
`36f16ed6d0f7aa95227a7d3b3783186b3e9bb041255ee6ae24e1ac9e1f147a2e`.
Local verification with the pinned Lean/Mathlib revisions passed direct module
compilation, the complete 2,866-job `lake build`, bundled module `leanchecker`,
the complete nine-declaration transitive audit for the new module, and a
2,232-declaration audit of the imported `ImbalancedChen` root closure.  Both
audits permit only `propext`, `Classical.choice` and `Quot.sound`.  The
independent VariableEnvelope workflow also passed its builds, exact
regressions, eight bundled kernel replays and all 358 declaration audits.  A
bundled kernel replay of the complete root was attempted but was killed by the
local memory limit (exit 137), so root replay success is not claimed; remote
core and VariableEnvelope workflows remain required for the submitted commit.

## Finite half-product Pan expansion candidate

`ImbalancedChen/HalfProductPanFinite.lean` rewrites every product-filtered
half-product source count as an exact sum over its unique smaller prime.
Specialization gives exact smaller-prime expansions for the actual congruence
mass, coprime mass, `BoundingSieve` divisor sum and primitive discrepancy.
All formulas retain the arbitrary real cutoff, the closed product endpoint,
the strict power wall, the prime-square diagonal and multiplication
multiplicity one. The equivalent outer prime-indicator form has absolute
coefficient at most one.

This closes the finite divisor-count decomposition needed before applying a
bounded-coefficient Pan theorem. It does not yet turn each curved fibre into
fixed product strips or prove a distribution estimate. The sharp fibre has a
moving lower wall and strict power wall, so the next adapter must cover it by
the manuscript's licensed cells and express each product strip as a difference
of two Pan prefixes at their own scales.

The module source SHA-256 is
`f392c7642bd00e418c91000a3ed6ef7c4c30194808e974999d4a39699d2b62de`.
Local verification with Lean `v4.33.0-rc1` and Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` passed direct compilation, the
complete 2,867-job `lake build`, bundled module `leanchecker`, an
18-declaration module audit, a 2,250-declaration imported-root audit, and the
independent 358-declaration VariableEnvelope workflow. Both transitive audits
allowed only `propext`, `Classical.choice` and `Quot.sound`. The complete-root
bundled `leanchecker` was attempted and was killed by the local memory limit
(exit 137), so root replay success is not claimed; remote workflows remain
required for the submitted commit.

## Exact product-strip Pan-prefix candidate

`ImbalancedChen/PanProductStrips.lean` fixes the endpoint and coefficient
conventions for the product cells needed by the restricted Pan estimate. Its
literal finite strip has `A₁ < r ≤ A₂` and `Y₀ < r*q ≤ Y₁`; it is exactly the
upper closed product prefix minus the lower closed product prefix. The module
proves the resulting subtraction identities for AP counts, coprime mass and
primitive discrepancy without dropping prime squares or introducing an
ordering multiplicity.

Each prefix is decomposed into first-prime fibres, and the product wall is
proved equivalent to the external closed moving endpoint `q ≤ Y/r`. For a
primitive residue, non-coprime outer fibres are empty, giving precisely an
outer `Coprime r d` gate and a modulus-independent zero-one prime indicator;
the latter has absolute value at most one. Finally, relative to any displayed
prime-counting main term, the prefix error is the corresponding bounded
indicator sum of fibre errors and the strip error is exactly the difference
of its two prefix errors. Thus the triangle cost is exactly two prefix errors,
with no hidden endpoint or normalization correction.

After correcting the analytic main term to the supplier's real scale
`(Y : ℝ) / r`, the module source SHA-256 is
`eb97d23050e3ec624cde24ef779acc67d7ded44283dc60097edc2d715429863b`.

This module is a finite adapter only. It does not prove the Pan distribution
theorem or the geometric scale gates for the moving product cells.  The
17,572 same-mask-v2 cells are not Pan product cells: they are the separate
fixed `(t,u)` cells for the eleven-term lower-weight certificate and its
`7/3` refinement.  The correct next geometry is a dynamic `(r,m=r*q)` grid,
not a signed-discrepancy containment from the existing `(r,q)` rectangles.

## Pinned Liu--Pan primitive-residue bridge candidate

The project now pins
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`,
whose Mathlib revision is identical to the project pin.  The imported
supplier theorem is
`liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving`; its coefficient
bound, two-thirds upper gate, logarithmic lower gate, modulus cutoff and
endpoint-dependent right side remain explicit.

`ImbalancedChen/PanProductResidueBudget.lean` proves that reducing the fixed
target to `N mod d` leaves every prefix and strip AP count unchanged.  It
transports selector-uniform prefix budgets to the physical target and combines
two independent endpoint budgets with no residue-class or modulus-cardinality
factor.

`ImbalancedChen/PanProductLiuBridge.lean` then identifies the local fibre with
the supplier's `primesInAPBelow`, identifies the two canonical reduced-residue
families, and proves the full prefix error equal to
`liuMainPanCoprimeIntervalSum` with the modulus-independent prime indicator.
The target residue belongs to `unitResidues d` from `1 ≤ d` and
`Coprime d N`; no coprimality with `Y₀` or `Y₁` is used.  Consequently the
physical prefix error is bounded by the supplier's literal finite `MaxL`, and
one product strip is bounded by the sum of its upper- and lower-endpoint
`MaxL` values.

The exported theorem
`panProductPrimeIndicatorMaxL_boundedAggregate_log_saving` specializes the
pinned unconditional aggregate to this exact prime-indicator coefficient and
thereby discharges the global bound `|f| ≤ 1`. It deliberately preserves the
supplier's endpoint, two-thirds, logarithmic-lower and modulus-cutoff gates.

This is a genuine imported-theorem interface, not yet the aggregate
application.  A separate `(r,r*q)` product-strip grid must still supply, at
both endpoints, `N₀ ≤ Y`, `A₂ ≤ Y^(2/3)`,
`log(Y)^(2B) ≤ A₁`, and `D ≤ panModulusCutoff Y B`; the physical
coprime-modulus subset must then be enlarged to the full nonnegative `Icc`
aggregate.  The coprime gate's main-term loss also remains to be reconciled
with the ungated physical mass.

The residue-budget and pinned-bridge source SHA-256 values are respectively
`4b5dcf30d8aebee0779f6dc3e4f1188a6797f9cd5215f71737b8369a79a9fbaf`
and
`dd239cb5a36898abe49cdb23d60cc1e3e86dede36bd849c41013f18a99ee2d61`.
Local verification with Lean `v4.33.0-rc1`, Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` and goldbach-lean
`09b97db5764ade1246bfb77206baa1b124760958` passed direct bridge compilation,
the complete 4,426-job `lake build`, bundled `leanchecker` replays of all three
product-strip modules and the imported root, a 2,314-declaration audit of every
project module, and the independent 358-declaration VariableEnvelope workflow.
Both transitive audits allowed only `propext`, `Classical.choice` and
`Quot.sound`. Remote workflows remain required for the submitted commit.

## Physical product-strip aggregate candidate

Code commit [`97b4d96fcf28146036a09c302eff40f4710a3b25`](https://github.com/UyNewNas/goldbach-formalization/commit/97b4d96fcf28146036a09c302eff40f4710a3b25) adds `ImbalancedChen/PanProductAggregateBudget.lean`. Its exported theorem `panProductStrip_physical_boundedAggregate_log_saving` applies the pinned unconditional Liu--Pan theorem to both exact product-strip endpoints. The physical set `{d ∈ Icc 1 D | Coprime d N}` is proved to lie in each full cutoff interval, and literal `MaxL` nonnegativity justifies enlargement without a modulus-cardinality factor. The output bounds the sum of absolute strip errors with the two endpoint logarithmic-saving terms.

All endpoint obligations remain explicit: the common supplier threshold, order `Y₀ ≤ Y₁`, both two-thirds upper gates, both logarithmic lower gates and both modulus cutoffs. Thus this closes the finite aggregate adapter but not the dynamic `(r,r*q)` cell geometry, the coprime-gate main-term comparison, the physical positive upper-weight density, or the final ordered bad-semiprime estimate.

The manuscript source was rechecked at `master@ba6ec11d800eccc54406490631895e174de85766`; no version change was found. The source attachment hash remains `ef70ecef4b4c310449a43db1093859b5d3377e670d7c9dc9fa23619d7e54be9c`. The target pins remain Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` and goldbach-lean `09b97db5764ade1246bfb77206baa1b124760958`.

The new module source SHA-256 is `13b512d4c51a00b217ea72b3033ec50bd48d76c10812184a20d1bc838ef04140`.

This runner did not contain a Lean executable after workspace recovery, so no local compile, kernel replay or axiom audit is claimed for this checkpoint. The first core and VariableEnvelope runs for the code commit failed before creating workflow steps (`steps: null`) and were retried once; only an actual runner execution can count as remote verification.

## Dynamic Pan product-coordinate grid candidate

Commit [`1fc6dbc92739732edf890e47c1fe8eaa27817274`](https://github.com/UyNewNas/goldbach-formalization/commit/1fc6dbc92739732edf890e47c1fe8eaa27817274) adds `ImbalancedChen/PanProductGrid.lean`. It constructs the genuinely required multiplicative grid in `(r,m=r*q)` coordinates rather than transferring signed discrepancies from the older `(r,q)` rectangles. Each cell is definitionally an exact `panProductStripPairs` with `A₁<r≤A₂` and `Y₀<r*q≤Y₁`.

`panProductGrid_existsUnique_strip` proves unique ownership for every prime pair below the product cap, including `r=q`. `panProductGridStrip_disjoint` proves pair-level disjointness, and `halfProductPair_existsUnique_actualPanProductGridStrip` plus `halfProductPairs_subset_actualPanProductGridPairs` give unique selected-cell ownership and the finite upper cover for the actual source. No equality with the curved source is claimed: a full selected strip may contain exterior points, and later projection must use pair weights so that different ordered pairs with the same product do not lose multiplicity. The 17,572 same-mask-v2 certificate cells remain a separate eleven-term numerical object.

The module source SHA-256 is `d1390ccfd096821a87c8695e099754d7e9403c6632c2b18b0a641254e9a16d11`. The manuscript remains `master@ba6ec11d800eccc54406490631895e174de85766`; all constants and dependency pins are unchanged.

No local Lean executable was available, so compilation, kernel replay and axiom audit are not claimed. Exact-head core run 38082267062 and VariableEnvelope run 38082267051, including one failed-jobs retry each, ended before creating any workflow step (`steps: null`, no logs). They are infrastructure-start failures, not proof verification. The next mathematical step is to prove the endpoint scale gates on these selected `(r,r*q)` cells and then apply `panProductStrip_physical_boundedAggregate_log_saving` cellwise.

## Pinned PNT/Mertens source-mass supplier candidate

Code commit [`244badc1dfb1f5a0fb7c4e6f748bed8a8bd68108`](https://github.com/UyNewNas/goldbach-formalization/commit/244badc1dfb1f5a0fb7c4e6f748bed8a8bd68108) adds `ImbalancedChen/RealHalfProductMassSuppliers.lean`. It connects the exact current arbitrary-real source-mass chain to proved theorems in the already-pinned `goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958` dependency.

The local `realPrimeReciprocalLogIntervalSum` is proved definitionally equal to the supplier's `weightedPrimeReciprocalLogSum`: both use `Ioc`, prime filtering, the same logarithmic weight and `rpowFloor N a = floor(N^a)`. `realHalfProduct_primeCounting_asymptotic_real` specializes the supplier's real-variable PNT to the exact witness previously left as a premise. The kernel `1/(1-u)` is proved continuous on `[b/(1+b),1/2]`, so the pinned weighted Mertens theorem supplies the exact integral used by the existing coefficient proof.

The exported `tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers` has only the mathematical parameters `0<b<1` and `κ>0`; it has no PNT or Mertens premise. Its conclusion is the literal ordered half-product source at `manuscriptHalfProductCutoff κ N`, normalized by `N/log N`, tending to `log(1/b)`. Strict badness, prime ordering, the inclusive square-root endpoint and prime squares are inherited unchanged. This closes the analytic source mass, not the subsequent additive-prime filtering or positive upper-sieve estimate needed for `RealB`.

The new module source SHA-256 is `fd088cd1597ba6d2a47175c6bcb358387d5e1c5eebca116bcfdd53ea400884ad`. The manuscript remains `master@ba6ec11d800eccc54406490631895e174de85766`; constants and dependency pins are unchanged. The runner has no Lean executable, so this code is submitted for CI but compilation, kernel replay and transitive axiom audit are not claimed until an actual runner executes them.

## Dynamic Pan selected-cell budget candidate

Code commit [`921924ab1859dd227a3028c5c76d42aca351efde`](https://github.com/UyNewNas/goldbach-formalization/commit/921924ab1859dd227a3028c5c76d42aca351efde) strengthens `ImbalancedChen/PanProductGrid.lean` with the public interfaces required to sum cellwise Pan errors. `mem_actualPanProductGridIndices` records both ambient-grid membership and a literal half-product source-pair witness; `actualPanProductGridIndices_subset` proves no selected index escapes the finite grid; and `actualPanProductGridIndices_card_le` bounds the selected family by `(floor (log N / log κ) + 1)^2`.

This is a purely finite combinatorial reduction. It does not identify the dynamic family with the separate 17,572 same-mask-v2 cells, prove any endpoint gate, or apply the Liu--Pan distribution theorem. In particular, the two endpoint-dependent modulus-cutoff obligations remain explicit and cannot be obtained by downward monotonicity from a cutoff at the global scale `N`.

The updated module SHA-256 is `e37bb4d2aa855c86e1601566e9ea6649092ac625c434d8a30476208057fab743`. Static checks pass (`git diff --check` and no `sorry`, `admit`, custom `axiom`, `native_decide` or `unsafe` in the module). This runner has no Lean or Lake executable, so no local elaboration, build, kernel replay or transitive axiom audit is claimed. The manuscript remains `master@ba6ec11d800eccc54406490631895e174de85766` and the pinned versions are unchanged.

## Dynamic Pan endpoint-range candidate

Code commit [`97a780a37a41952f10f4de0c3fe91184a7e2813d`](https://github.com/UyNewNas/goldbach-formalization/commit/97a780a37a41952f10f4de0c3fe91184a7e2813d) adds `ImbalancedChen/PanProductGridRanges.lean` and imports it from the public root. For each selected dynamic `(r,r*q)` cell and `1 < κ ≤ 2`, `actualPanProductGridIndices_productLowerEndpoint_gt` proves `T/2 - 1 < Y₀`, `actualPanProductGridIndices_productUpperEndpoint_lt` proves `Y₁ < 2N`, and `actualPanProductGridIndices_firstUpperEndpoint_lt` proves `A₂ < 2*sqrt N`. The combined theorem `actualPanProductGridIndices_endpoint_ranges` exports all three bounds.

Every bound comes from the literal source witness used to select the cell. The lower product estimate pays the full multiplicative-width and ceiling-minus-one losses; the first-coordinate estimate uses the original ordering `r ≤ q`; and the upper product estimate retains the original closed cap `r*q ≤ N`. Prime squares and ordered-pair multiplicity remain unchanged. No statement clips the full product strip back to the curved source.

This closes only the first finite endpoint-range layer. It does not yet prove the Liu--Pan threshold, two-thirds or logarithmic lower gates, and it deliberately does not infer either endpoint's `D ≤ panModulusCutoff Y B` condition from a cutoff at global scale `N`. Those two cutoff obligations remain independent.

The new module SHA-256 is `dc19b118be3348a81503c236917400820f31af44bfbddea22d85b4f271fa79a0`. Static checks pass (`git diff --check` and no `sorry`, `admit`, custom `axiom`, `native_decide` or `unsafe`). An independent read-only review checked the source-level types, coercions, endpoint indices and inequality directions. This runner has no Lean or Lake executable, so no local elaboration, build, bundled kernel replay or transitive axiom audit is claimed. The manuscript remains `master@ba6ec11d800eccc54406490631895e174de85766`; all dependency pins and current constants are unchanged.

## Dynamic Pan supplier-threshold gate candidate

Code commit [`06357c231773d642aff6b759731fffd7d5315b3c`](https://github.com/UyNewNas/goldbach-formalization/commit/06357c231773d642aff6b759731fffd7d5315b3c) strengthens `ImbalancedChen/PanProductGridRanges.lean` with `eventually_actualPanProductGridIndices_productEndpoints_ge`.  For fixed manuscript parameter `0 < κ₀ < 1`, fixed grid ratio `1 < κ ≤ 2`, and every fixed natural threshold `N₀`, both exact product endpoints of every selected dynamic cell eventually satisfy `N₀ ≤ Y₀` and `N₀ ≤ Y₁`, uniformly over the selected family.

The proof uses the already established full-loss inequality `N^(1-κ₀)-1 < Y₀`, the divergence of the positive real power `N^(1-κ₀)`, and monotonicity of consecutive ceiling-minus-one grid endpoints.  It therefore discharges exactly the two common-threshold hypotheses of `panProductStrip_physical_boundedAggregate_log_saving`.  The two-thirds, logarithmic-lower, and endpoint-dependent modulus-cutoff hypotheses remain open and are not inferred from this result.

The updated module source SHA-256 is `507217636bf1b1c7b4d1a7473bda0764664ee95ddb07a29706c610a6db1bafce`.  Static checks pass (`git diff --check` and no `sorry`, `admit`, custom `axiom`, `native_decide` or `unsafe` in the module).  The runner contains no Lean or Lake executable, so no local elaboration, build, bundled kernel replay, or transitive axiom audit is claimed.  The manuscript remains `master@ba6ec11d800eccc54406490631895e174de85766`; the PDF hash and all Lean, Mathlib, and dependency pins are unchanged.

## Dynamic Pan two-thirds endpoint gates candidate

Code commit [`bde4741bbd71511383b06bb1db1d6c6448aebba8`](https://github.com/UyNewNas/goldbach-formalization/commit/bde4741bbd71511383b06bb1db1d6c6448aebba8) further strengthens `ImbalancedChen/PanProductGridRanges.lean`.  The helper `eventually_const_mul_rpow_le_rpow` proves that any fixed multiplicative constant is absorbed by a strict real-power exponent gap.  `manuscript_kappaZero_lt_quarter` formalizes the implication from the manuscript's actual condition `0 < κ` and `κ₀ < κ/(4(1+κ))` to `κ₀ < 1/4`.

With
`alpha = ((3/4) + (1-κ₀))/2` and `gamma = (2/3)*alpha`, the strict quarter gap gives `alpha < 1-κ₀` and `1/2 < gamma`.  The theorem `eventually_actualPanProductGridIndices_twoThirds_gates` uses these two gaps to pay, respectively, the exact `-1` in `N^(1-κ₀)-1 < Y₀` and the factor `2` in `A₂ < 2*sqrt N`.  Its manuscript wrapper exports, uniformly over every selected dynamic cell,
`A₂ ≤ Y₀^(2/3)` and `A₂ ≤ Y₁^(2/3)`.  The second gate follows only from consecutive endpoint monotonicity.  No modulus-cutoff condition is inferred.

The updated module source SHA-256 is `d6a76d62281093c340d3d01ab36b8a65010f8b0acb32468c36a116b12f281860`.  Static checks pass (`git diff --check` and no forbidden proof escape in the module), and an independent read-only review checked the exponent arithmetic, manuscript parameter mapping, strict endpoint loss, `Real.rpow` directions, casts, and the two exact endpoint indices.  The runner contains no Lean or Lake executable, so no local elaboration, build, bundled kernel replay, or transitive axiom audit is claimed.  The manuscript source remains `master@ba6ec11d800eccc54406490631895e174de85766`; the PDF hash and all dependency pins remain unchanged.

## Dynamic Pan logarithmic endpoint gates candidate

Code commit [`3f240087a371b0d09f8b4e26cf956ee508903502`](https://github.com/UyNewNas/goldbach-formalization/commit/3f240087a371b0d09f8b4e26cf956ee508903502) further strengthens `ImbalancedChen/PanProductGridRanges.lean`.  `actualPanProductGridIndices_firstLowerEndpoint_gt` transports the source's strict `q^b < r` roughness inequality to the first exact open grid endpoint, paying both the full grid-width factor and the `ceil - 1` rounding loss.

For `β = b/(1+b)`, the theorem `eventually_actualPanProductGridIndices_log_gates` reuses the proved bound `log(4N)^A ≤ logCutoff(N)^(β/2)/2 - 1`.  The inequalities `logCutoff N ≤ N` and `κ₀ < 1/4 < 1/2` place that quantity below the actual manuscript cutoff power `(2*N^(1-κ₀))^β/2 - 1`, which the new strict endpoint theorem places below `A₁`.  Product-endpoint positivity and `Y₀ ≤ Y₁ < 2N < 4N` then give both exact supplier gates `log(Y₀)^(2B) ≤ A₁` and `log(Y₁)^(2B) ≤ A₁`, uniformly over all selected dynamic cells.  The manuscript wrapper derives the quarter gap from the actual licensed condition `κ₀ < κ/(4(1+κ))`.

The updated module source SHA-256 is `88b2c972243ba1e33e89a08b6759c16512620751b7c25206dfa4d767bf79466a`.  Static checks pass (`git diff --check` and no `sorry`, `admit`, custom `axiom`, `native_decide` or `unsafe` in the module).  An independent read-only audit checked the strict roughness transfer, the two coordinate indices, real-power monotonicity, ceiling step, filter uniformity and exact endpoint bounds.  This runner has no Lean or Lake executable, so no local elaboration, build, bundled kernel replay or transitive axiom audit is claimed.  Checkpoint head `25be8488e6ab1fad00bce0a6d644c9f0ad5d9c0d` core [run 38104132595](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38104132595) and VariableEnvelope [run 38104132598](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38104132598), including one failed-jobs retry each, failed before creating workflow steps (`steps: null`, no logs); they are infrastructure-start failures and do not count as proof verification.  The only remaining endpoint gates for the pinned two-endpoint Pan aggregate are the two independent conditions `D ≤ panModulusCutoff Y₀ B` and `D ≤ panModulusCutoff Y₁ B`; they are not inferred from a global-scale cutoff.

## Dynamic Pan honest modulus-gate candidate

Code and documentation commit
[`56519975ad32d9b3616b33974b16756882106a4f`](https://github.com/UyNewNas/goldbach-formalization/commit/56519975ad32d9b3616b33974b16756882106a4f)
adds `ImbalancedChen/PanProductGridModulus.lean` and closes both endpoint cutoff gates
for a deliberately smaller physical modulus layer.  For fixed
`0 < κ₀ < 1`, `0 ≤ theta < (1-κ₀)/2`, `1 < gridκ ≤ 2`, and the supplier's
fixed `B ≥ 0`,
`eventually_actualPanProductGridIndices_floor_rpow_modulus_gates` proves,
uniformly over every selected dynamic product cell,
`floor(N^theta) ≤ panModulusCutoff Y₀ B` and
`floor(N^theta) ≤ panModulusCutoff Y₁ B`.  The corollary
`eventually_actualPanProductGridIndices_enlargedSelberg_modulus_gates`
applies the same result to the literal squared natural Selberg level.

The strict inequality on `theta` is mathematically necessary for this
argument.  Since the smallest endpoint is only of order `N^(1-κ₀)`, a
global layer of order `sqrt(N)/log(N)^B` is larger than the local Pan cutoff
by a power `N^(κ₀/2)`; adding logarithms cannot repair it.  The new result
therefore does not claim that the manuscript's still-unidentified physical
positive-weight modulus level already satisfies the hypothesis.  That layer,
its effect on the current coefficient `K`, the coprime-gate main mass, and
the cellwise-to-global positive upper-sieve composition remain open.

The existing `enlargedSelbergLevel` specialization is only an auxiliary weak
route.  Its normalizer produces coefficient `4/theta`; imposing
`theta < (1-κ₀)/2` makes its best limiting coefficient at least
`8/(1-κ₀) > 8`, so it cannot recover the manuscript's current
`K = 8452171/1250000`.  The current-K route must instead formalize the
manuscript's same positive weight `ρ_N`, its density, and its signed
factorized local distribution at the actual local product scale.  In
particular, the high-rank support reaching `theta* = 599/1000` cannot be
covered wholesale by this absolute Pan aggregate.

Module source SHA-256:
`0e340bf79e581e5c46d324a83ad470036ff07f3cbd9fdb37dc4fe3f950e66fdd`.
Static source checks pass (`git diff --check` and no forbidden proof escape).
The runner contains no Lean or Lake executable, so no local elaboration,
build, bundled kernel replay or transitive axiom audit is claimed.  Exact
code-head VariableEnvelope [run 38107471726](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38107471726)
and core [run 38107471723](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38107471723),
including one failed-jobs retry each, ended before any workflow step was
created (`steps: null`, no logs or artifacts).  They are infrastructure-start
failures and are not proof verification.

## Same-physical-weight finite bridge candidate

`ImbalancedChen/SignSensitiveAttachment.lean` formalizes the finite ordered
algebra in the manuscript's physical upper-weight construction.  It proves
that an upper small-prime divisor sum must be attached to every nonnegative
raw coefficient and a lower small-prime divisor sum to every negative raw
coefficient; the negative multiplication reverses the inequality.  The
resulting pair coefficient remains absolutely bounded by one when both
factors are.  These statements do not assume a density estimate,
distribution theorem, or the desired pointwise majorant as a structure
field.

`ImbalancedChen/PhysicalUpperWeightBridge.lean` connects any one explicitly
given finite coefficient `rho` to the literal shifted half-product source.
It proves the exact Fubini identity and then splits the same weighted
congruence sum into (i) total source cardinality times the
reciprocal-totient density, (ii) the exact coprime-source correction, and
(iii) the signed primitive-residue distribution error.  A pointwise divisor
majorant therefore bounds the actual sifted source by those three visible
terms with the identical `rho` throughout.

This closes only the finite sign-sensitive attachment and same-weight
assembly interface. `FirstExitTree` now proves the generic odd-first-exit
identity and integer rough majorant, but the actual causal retained policy,
unique small/rough product reindexing into `rho_N`, physical density estimate
that yields `K = 8452171/1250000`, and signed local factorized distribution
estimate are not proved by these modules. Compilation, kernel
replay and transitive axiom audit remain pending on a runner containing the
pinned Lean toolchain.  Source SHA-256 values are
`c189987e7e66b2eaf2a03563c3be8ee275c250916533977723efb2c9dbe13dc6`
for `SignSensitiveAttachment.lean` and
`7c179a6733bd163f5b8e8410a718effa609baa8a10b64b266caa36bf656e77a3`
for `PhysicalUpperWeightBridge.lean`.

## Finite odd-first-exit tree candidate

`ImbalancedChen/FirstExitTree.lean` formalizes the exact finite
product-plus-first-exit identity from the current manuscript. Its recursive
retained polynomial scans a finite ordered label list, flips the coefficient
sign whenever a label is selected, and stops a selected branch precisely at
its first rejection. `oddFirstExitPolicy` totalizes the even-rank decision to
`true`, preventing the invalid even-exit counterexample.

`firstExitRetainedPolynomial_eq_product_add_correction` proves the signed
identity before imposing parity. The root specialization
`oddFirstExitRetainedPolynomial_eq_product_add_exits` has a complete Euler
product plus the odd-first-exit correction. The correction is nonnegative for
local weights in `[0,1]`, yielding
`product_le_oddFirstExitRetainedPolynomial`.

The integer specialization uses literal divisibility in `ℤ`.
`finiteIntegerRoughIndicator_eq_indicator` proves that the Euler product is
exactly the indicator of having no divisor from the finite universe, and
`integerRoughIndicator_le_oddFirstExitRetainedPolynomial` proves the
pointwise majorant for every integer, including zero and negative integers.
No prime, ordering or positivity premise on the integer is silently added.

The manuscript source is fixed at
`master@ba6ec11d800eccc54406490631895e174de85766`, with the displayed identity
in `paper/source/manuscript-body.tex` lines 377--391 (blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`). Static checks pass
(`git diff --check` and no `sorry`, `admit`, custom `axiom`, `native_decide`
or `unsafe` in the module). This runner has no Lean or Lake executable, so no
local elaboration, build, bundled kernel replay or transitive axiom audit is
claimed.

Code commit
[`6937c92d3d85a8081158f31308bd3850ee3077be`](https://github.com/UyNewNas/goldbach-formalization/commit/6937c92d3d85a8081158f31308bd3850ee3077be)
introduced the public-root import and the initial identity module. Its source
SHA-256 was
`b97d463290a6c549ede5438de7f227b9ce5b34267017f3e929c894247d2b55fe`.

The actual causal retained-set instantiation, unique small/rough decomposition,
and the density and signed factorized distribution estimates for the exact
constructed `rho_N` remain open. Consequently neither the current coefficient
`K = 8452171/1250000` nor Theorem 1.1 is proved by this checkpoint.

The module now additionally exposes `FirstExitLeaf` as a data-only terminal
branch carrier and proves:

- `firstExitRetainedPolynomial_eq_leaves_sum`, the exact equality between the
  recursive evaluator and the explicit finite retained-leaf sum;
- `mem_oddFirstExitRetainedLeaves_mass_eq_selected_prod`, identifying every
  stored leaf mass with the product over its selected labels;
- `mem_oddFirstExitRetainedLeaves_positive_eq_evenListLength`, identifying
  every stored sign with selected-list parity;
- `mem_oddFirstExitRetainedLeaves_selected_reverse_sublist`, proving the exact
  carrier/order invariant: reversing the accumulated selected list gives a
  sublist of the original ordered universe;
- `mem_oddFirstExitRetainedLeaves_selected_nodup`, deriving duplicate-freeness
  of every selection from duplicate-freeness of the ordered universe;
- `oddFirstExitRetainedLeaves_selected_eq_of_prod_eq` and
  `oddFirstExitRetainedLeaves_selectedProd_injOn`, proving that, in a
  duplicate-free prime universe, the selected natural product determines the
  selected list and the entire retained leaf;
- `list_prod_squarefree_of_nodup_primes`,
  `mem_oddFirstExitRetainedLeaves_primeFactors_selectedProd`,
  `cardFactors_list_prod_eq_length_of_primes`, and
  `moebius_list_prod_eq_negOnePow_length`, proving the squarefree product,
  exact prime-factor carrier, factor count and Möbius parity formula for a
  duplicate-free prime list;
- `mem_oddFirstExitRetainedLeaves_selectedProd_squarefree`,
  `mem_oddFirstExitRetainedLeaves_moebius_selectedProd`, and
  `mem_oddFirstExitRetainedLeaves_value_eq_moebius_mul_selected_prod`,
  specializing those facts to actual retained leaves and identifying the
  real branch coefficient with `(moebius d : ℝ)` times the local-weight
  product;
- `oddFirstExitRetainedLeaves_unit_mem`, explicitly retaining the empty
  branch, unit modulus `d = 1` and coefficient one even for an empty universe;
- `firstExitRetainedLeaves_nodup` and
  `oddFirstExitRetainedLeaves_nodup`, proving the literal recursive leaf list
  duplicate-free before any conversion to a Finset;
- `oddFirstExitRetainedLeaves_sum_eq_product_add_exits`, the manuscript
  product-plus-exit identity with the retained side displayed as a literal
  branch sum.

These statements close the evaluator-to-branch-sum interface, make the reverse
accumulator convention explicit, close prime-product uniqueness and identify
the raw branch sign with the Möbius value at the abstract ordered-universe
layer.

`ImbalancedChen/RetainedModuli.lean` now adds the natural-number support of
selected products and the literal integer coefficient
`oddFirstExitRetainedCoefficient`: `mu(d)` on retained support and zero
outside. It proves support membership by a retained-leaf witness, preserves
the unit modulus with coefficient one, gives a unique retained leaf as a
value for each supported modulus under the existing prime-universe hypotheses,
proves every supported modulus squarefree, and recovers every leaf value as
the looked-up coefficient times the local-weight product over
`d.primeFactors`. The source leaf list is proved `Nodup` recursively; combining
that fact with selected-product injectivity proves the modulus list `Nodup`,
and `oddFirstExitRetainedLeaves_sum_eq_retainedModuli_sum` then replaces the
literal leaf `List.sum` by the support `Finset.sum` without losing multiplicity.

`ImbalancedChen/RoughPrimeUniverse.lean` constructs the finite carrier of
literal primes `p ∤ N` satisfying the real half-open inequalities
`w ≤ p < z`, sorts it strictly decreasing, and proves exact membership,
derived `Nodup`, `SortedGT`, pairwise strict decrease and recovery of the
original Finset. Finiteness uses an explicit natural enumeration cap; when
`z ≤ cap`, membership is equivalent to the uncapped manuscript predicate,
with no unproved floor/ceiling replacement. The squarefree,
Möbius/coefficient leaf identities, exact modulus-sum reindex and integer
pointwise roughness majorant are specialized to this concrete universe.

The remaining finite obligations are the actual causal retained policy and
unique small/rough attachment. The analytic density and signed-distribution
estimates remain later obligations.

The extended module source SHA-256 for this candidate is
`6ab5eeb136969f76afc8fcc83dfa211985e0b7ffe85e89dab0702f381ad42a6b`.

The new source SHA-256 values are
`ec5df61712426350f0a93f36501ce2f2ca4bf49c9ee13c611920342e67386274`
for `RetainedModuli.lean` and
`3d716d89548e2e453e96c598481db2f62ae1c76e7f092a960e490a4b70688e58`
for `RoughPrimeUniverse.lean`.

## Exact retained-modulus reindex checkpoint

This checkpoint closes the multiplicity issue in the odd-first-exit branch
sum rather than merely replacing a list by a set.  The recursive theorem
`firstExitRetainedLeaves_nodup` separates the skip and select subtrees using
the current label: every selected-subtree leaf contains it, while every
skip-subtree leaf omits it.  Its odd-policy specialization gives
`oddFirstExitRetainedLeaves_nodup`.  Combining that theorem with the already
proved selected-prime-product injectivity yields
`oddFirstExitRetainedLeaves_selectedProd_map_nodup`.

`oddFirstExitRetainedLeaves_sum_eq_retainedModuli_sum` can therefore invoke
the pinned Mathlib theorem `List.sum_toFinset` without collapsing duplicate
moduli: the actual retained-leaf `List.sum` is exactly the natural support
`Finset.sum`, with the literal Möbius coefficient and the local-weight product
over `d.primeFactors`.  The concrete decreasing real half-open rough-prime
carrier is discharged by
`roughPrimeRetainedLeaves_sum_eq_retainedModuli_sum`.  These are kernel terms;
no external enumeration, Python `PASS`, or saved numerical endpoint is used
as their proof.

The fixed Lean 4.33.0-rc1 toolchain additionally exposed missing selective
imports and parser changes in the current PR stack.  The relevant modules now
import the required real/ring instances explicitly, avoid identifiers that
are reserved in this toolchain, and `SignSensitiveAttachment.lean` imports
the exact finite-ring and `norm_num` interfaces it uses.  Its current source
SHA-256 is
`d34b8483983bf4243479bee70cd4bcd07fbf286abafe982021ca4625a3ab63bc`.

Local verification on the pinned dependency graph completed as follows:

- direct elaboration and explicit Lake builds passed for `FirstExitTree`,
  `RetainedModuli`, `RoughPrimeUniverse`, and `SignSensitiveAttachment`;
- the complete `lake build` passed all 4436 jobs, including the root module
  and the downstream `PhysicalUpperWeightBridge`;
- bundled Lean 4.33.0-rc1 `leanchecker` replay passed separately for those
  four modules and `PhysicalUpperWeightBridge`;
- Lean's transitive `#print axioms` collector reports only `propext`,
  `Classical.choice`, and `Quot.sound` for the new leaf-`Nodup`, mapped-modulus
  `Nodup`, abstract and concrete reindex theorems, and the repaired
  sign-sensitive attachment theorem.

A single-process bundled replay of the entire root import closure was also
attempted locally but exceeded the available memory; it is not counted as a
passed root replay.  The exact delivery commit must still pass the repository
CI root replay and full-root declaration audit before this checkpoint can be
called remotely verified.  The preceding exact PR head's core and variable-
envelope workflows both failed before creating any job step or log, so those
infrastructure-start failures likewise do not count as proof checks.

The manuscript source was rechecked and remains exactly
`master@ba6ec11d800eccc54406490631895e174de85766` (tree
`2b5af758d1b4a4799a120d4ea108679cc02f2e11`); no statement or parameter
comparison was required.  At that checkpoint the remaining finite gap was
the actual causal retention policy together with the unique small/rough
product attachment into one physical `rho_N`.

## Strict small/rough product attachment checkpoint

`ImbalancedChen/SmallRoughAttachment.lean` closes the abstract unique-product
part of that gap.  `SmallPrimeSupportedAt w a` uses the strict boundary
`p < w`, while `RoughPrimeSupportedAt w b` uses the inclusive boundary
`w ≤ p`.  `smallPrimeSupportedAt_coprime_roughPrimeSupportedAt` proves that
these supports are cross-coprime directly from their literal prime-factor
finsets.  `smallRough_factorization_unique` then proves
`a*b = c*d -> (a,b)=(c,d)` for supported factors, including arbitrary prime
powers and unit factors; squarefreeness is not smuggled in.

`smallRoughRho` is a total natural-number coefficient defined by the finite
product fibre.  On every occupied modulus `smallRoughRho_mul` collapses that
fibre to the unique sign-sensitive pair coefficient, and
`smallRoughRho_eq_zero_of_not_mem` proves it vanishes off the displayed
physical support.  The exact theorem
`smallRoughPairDivisorSum_eq_physicalDivisorSum` reindexes the complete
pair-indexed divisor expression to `PhysicalUpperWeightBridge`'s one
`physicalDivisorSum`; no multiplicity factor is introduced.
`smallRoughPairDivisorSum_eq_signSensitiveAttachment` expands the upper or
lower small-prime sum selected by each rough coefficient's sign, and
`signSensitiveAttachment_eq_smallRough_physicalDivisorSum` composes the two
identities.  Thus the pointwise majorant's existing expression is literally
the divisor sum of the same `rho`, rather than merely an isomorphic pair
model.  `sum_smallRoughModuli` and `sum_smallRoughRho_mul` additionally
reindex generic scalar and rho-weighted physical sums without a fibre factor.
The separate theorems `smallRough_mul_dvd_iff` and
`abs_smallRoughRho_mul_le_one` retain the literal divisibility semantics and
the unit coefficient bound.

Local verification under the pinned Lean 4.33.0-rc1 and Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` passed direct elaboration, the
complete 4,437-job `lake build`, bundled `leanchecker` replay of
`ImbalancedChen.SmallRoughAttachment`, and direct transitive audits of all
twelve new theorems.  The audit reports only `propext`, `Classical.choice`,
and `Quot.sound`.  The delivered source SHA-256 is
`8f69bb4f62110e54aeb69c371d4767253d8520d9d904e3dc97e578beaedfccba`.
The independent VariableEnvelope runner was also invoked, but the local stale
base checkout contains a reference snapshot whose bytes do not match its own
manifest, so that runner stopped at provenance before any VE build or replay;
it is not counted as passed.  Exact delivery-head CI remains required.

External reuse was checked at pinned `goldbach-lean`
`09b97db5764ade1246bfb77206baa1b124760958`.  Its
`goldbachOrderedPair_mul_injective` is directly reusable for an ordered pair
of rough primes times a divisor of its concrete strict-small product, while
Mathlib provides the `Nat.Coprime` cancellation and `Finset.sum_image`
interfaces used here.  The present theorem is intentionally more generic on
the rough side (any nonzero composite with all prime factors `w ≤ p`) and
therefore proves the short cutoff argument locally rather than importing a
research-only carrier theorem with narrower labels.

This checkpoint does not instantiate the manuscript's actual small Rosser
weights or the causal retained policy, and it proves no density or
distribution estimate.  The current-`K` density calculation, signed
factorized distribution estimate, complete eleven-term mean lower bound and
final ordered-bad transfer therefore remain open; Theorem 1.1 and
Corollary 1.2 are not claimed.



## Exact same-rho main-term checkpoint (11 October 2026)

`ImbalancedChen/SmallRoughMainTerm.lean` closes the finite main-term algebra for the literal physical coefficient `smallRoughRho`.  The reciprocal-totient density is reindexed without multiplicity to the displayed small/rough pair carrier and factored by totient multiplicativity.  Nonnegative rough coefficients select the upper small-weight density; negative coefficients select the lower density, preserving the sign reversal required by the pointwise majorant.  The exact coprime-source correction and signed primitive-residue distribution error are reindexed to the same pair carrier.

No density or distribution estimate is assumed.  The module was directly elaborated under Lean 4.33.0-rc1 and Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; its generated object passed bundled `leanchecker`, and all four theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`.  Source SHA-256 is `3a3cdd6bc284237634da7744167e280c9ee56dc33555899ed98cc88e7e691b08`.  A complete clean-checkout CI build remains required before remote verification success is claimed.  The actual causal retained policy, actual lower/upper Rosser-weight instantiation, their sharp density bounds yielding current `K`, and the restricted moving-residue distribution theorem remain open.

## Current Chen pointwise and paired-count checkpoint (11 October 2026)

The active target is the complete current Theorem 1.1 and Corollary 1.2,
using manuscript commit `ba6ec11d800eccc54406490631895e174de85766`.
The historical `chenFixedElevenWeight` uses different exponents and a lower
receiver-size band, so it cannot supply the current constant by itself.

Three new modules close the corresponding finite gap:

- `CurrentChenPointwise` proves the full eleven-term inequality at
  `a=417/5000`, `h=19/125`, `d=59/250`. In the ninth branch the actual three
  prime factors give `N < H D C^2 <= n*p3`, removing the old lower-size-band
  assumption. The final theorem needs only `N >= 1`, squarefreeness and
  `n <= N`, and includes receiver one.
- `CurrentChenPairedDeletion` uses the same predicate on `Y6` pairs and the
  last pair of full `Y11` tuples. The first pair is proved to be the unique
  smallest pair of the receiver, so last-pair projection is an injection.
  Thus `Y11(E) <= Y6(E)` and the current paired weight inherits the exact
  pointwise inequality. The arbitrary predicate is a selection of actual
  tuples, not an assumed certificate estimate.
- `CurrentChenSummedBridge` sums over the actual coprime additive primes.
  On arbitrary squareful receivers it does not use the squarefree injection:
  `Y11(E) <= Y11(full)` first cancels the positive correction. Bounding only
  the remaining positive terms gives 246. Nonrough receivers are
  nonpositive, and the exceptional rough squareful receivers inject into
  the previously proved large-prime-square set. The result is
  `sum W_E <= 4 D12 + 246 N/(N^a-1) + 4`. For `N^a >= 2` the loss is at most
  `492 N^(1-a) + 4`, which is proved negligible in the actual
  `singularNormalization`, uniformly over the selected pair region.
  This smaller one-sided error budget is compatible with the manuscript's
  coarser absolute-value budget; it does not improve the main coefficient.

All three new modules passed direct Lean 4.33.0-rc1 elaboration with
`warningAsError=true` and individual bundled `leanchecker` replay.
`verification/CurrentChenAudit.lean` inventories declarations using defining
module metadata, including private and automatically generated declarations;
all **94 declarations** passed its transitive audit, with only `propext`,
`Classical.choice`, and `Quot.sound` allowed. The 14 existing local dependency
modules were rebuilt with the same pinned compiler; the external Mathlib
cache uses the pinned `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` revision.
This is a scoped local checkpoint, not a new full-root CI checkpoint.

Reproduce the scoped checks with the pinned toolchain on PATH:

```sh
lake build ImbalancedChen.CurrentChenSummedBridge
lake env leanchecker --verbose ImbalancedChen.CurrentChenPointwise
lake env leanchecker --verbose ImbalancedChen.CurrentChenPairedDeletion
lake env leanchecker --verbose ImbalancedChen.CurrentChenSummedBridge
lake env lean -DwarningAsError=true verification/CurrentChenAudit.lean
```

Source SHA-256 values:

| Module | SHA-256 |
| --- | --- |
| `CurrentChenPointwise` | `17ade795542a81bac8b659b7d24b96ab76cba45e5f3850db5fe0bc04d47a9ee8` |
| `CurrentChenPairedDeletion` | `6101bf1057504895d2413bf814249deabdd12a3e53a0b21067a68df03dee4794` |
| `CurrentChenSummedBridge` | `e7897e67a0a51db8e2d0dc410a1240dea62774f5b94782bc30ddf9055a7be832` |

The current signed lower mean has not been proved. The actual causal
retained policy and small Rosser weights, the same-rho sharp density and
restricted moving-residue distribution estimates, the analytic meaning of
the 17,572-cell certificate, and final bad-semiprime bounds remain open.
Theorem 1.1 and Corollary 1.2 still have their explicit analytic premises;
no new theorem in this checkpoint claims to discharge them.
Next concrete dependency: instantiate the small-prime weights from the
pinned dependency's `MathlibNt/SieveTheory/LiLiuPrereqWFSmallRosser.lean`.
Use the product of the actual primes `p < w`, `p ∤ N`, and reindex the
proved Rosser divisor sums through `gcd(M, |n|)` to include `n = 0`.
Connect these actual lower/upper weights, their strict support and unit
coefficient bound to `SignSensitiveAttachment`; do not leave its small-side
pointwise assumptions as new unexplained hypotheses. The dependency's
fundamental-lemma density supplier then needs a separate semantic and
transitive-axiom review before it is used toward the current `K`.

## Full aggregate build of the Chen checkpoint (12 October 2026)

The local aggregate at commit `e86c73b5cf4f8ed86b3040a095424fdad10723fe`
completed `lake build` with exit code zero and `Build completed successfully
(4441 jobs).` The toolchain, Lake configuration and manifest hashes were
unchanged. The isolated evidence is in the ignored directory
`.lake/main-theorem-verification-20261012/` (`incremental-full-build.log` and
`incremental-full-build-status.json`). This supersedes the earlier local
aggregate-build wait, not the outstanding analytic proof obligations. It
does not assert remote CI success or include later modules that were not
yet imported by that aggregate.

## Actual small weights and fixed physical coefficient (12 October 2026)

Five modules close the previously abstract small-weight input and connect
its proved density to the same physical coefficient:

- `FixedRoughCoefficients` proves that the selected lists and natural
  modulus support of the retained tree are independent of local weights
  and incoming masses. The fixed `h=1` carrier and Mobius coefficient work
  for all test integers. The exact divisor-sum identity, squarefreeness,
  coprimality to the target and coefficient one-bound are proved.
- `ActualSmallRosser` takes the literal lower and upper Rosser weights on
  the product of primes `p<w`, `p` not dividing `N`. A gcd reindex supplies
  their sandwich for all integers, including zero and negative arguments.
  The displayed support is the sieve product's divisors. Its members are
  squarefree and target-coprime; nonzero coefficients satisfy `d<L` and
  have absolute value at most one. Zero coefficients above the level are
  not incorrectly asserted to be active.
- `ActualSmallRosserDensity` proves a uniform density sandwich for exactly
  those coefficients at `L=D^epsilon`, `w=D^(epsilon^2)`. It supplies all
  multiplicativity, prime-density and dimension-one premises from proved
  results for the progression density. Its constants and threshold precede
  the varying even target and finite carrier. The relative error is
  `C*(exp(-1/epsilon) + exp(sqrt(K_dim)-1/epsilon)*
  (epsilon*log D)^(-1/3))`. Here `K_dim` is the dimension constant, not the
  manuscript's numerical upper coefficient. For fixed epsilon the first
  term does not tend to zero with D.
- `SmallRoughDensityError` proves that the sign-sensitive density increase
  lies between zero and `delta * sum(|c(d)|/phi(d))`. It preserves the
  absolute rough mass rather than replacing it by the signed main term.
- `ActualSmallRoughAttachment` constructs one integer-independent rho from
  those actual small weights and the fixed raw rough coefficient. Its
  pointwise majorant, nonnegativity at every integer, squarefree and
  target-coprime support, one-bound and strict active small-factor level
  are proved. The proved small-density supplier controls this same rho's
  density error, with its absolute rough-mass multiplier explicit.

All five sources passed direct elaboration with `warningAsError=true`.
Their final frozen objects each passed bundled `leanchecker`. The defining-
module environment inventory audited all **90 declarations** (16 fixed
rough, 39 actual small, 4 error, 16 small density and 15 attachment), including
private and automatically generated declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur transitively. After importing all
five modules in the public root, `lake build` passed with exit zero and
**4,803 jobs**. Source, audit, root and dependency-pin hashes were unchanged
through the final checks. Evidence is in the ignored
`.lake/main-theorem-verification-20261012/final-source/` directory. This is
full aggregate compilation and five module kernel replays, not a claim of
complete-root kernel replay or remote CI success.

The retained policy is still an arbitrary odd-first-exit policy: this does
not instantiate the current causal boxed policy or prove its support
exponent. No sharp current-K density, restricted distribution estimate,
current signed lower mean, certificate-to-integral interpretation or final
bad-semiprime bound is claimed. Theorem 1.1 and Corollary 1.2 remain open.

The following checkpoint supplies the finite absolute rough-mass Euler
bound and literal raw-Rosser coefficient dictionary. The fixed provider
`SmallRosser.upperWeight_eq_producer` uses `Nat.ceil R`; some real-level
endpoint theorems instead use `Nat.floor R + 1`. These are not the same
weight when R is an integer. The B8/B10 Goldbach carrier and its exact
`nu(d)=1/phi(d)` can supply a dictionary to the natural-level interface
without changing coefficients. Existing single-sided F/f bounds must not
be subtracted to assert the eighth-layer density saving; the required
same-weight fixed-rank reverse limits and target-prime deletion uniformity
remain to be proved.

Reproduce this checkpoint with the pinned toolchain on PATH:

```sh
lake build
lake env leanchecker --verbose ImbalancedChen.FixedRoughCoefficients
lake env leanchecker --verbose ImbalancedChen.ActualSmallRosser
lake env leanchecker --verbose ImbalancedChen.SmallRoughDensityError
lake env leanchecker --verbose ImbalancedChen.ActualSmallRosserDensity
lake env leanchecker --verbose ImbalancedChen.ActualSmallRoughAttachment
lake env lean -DwarningAsError=true verification/ActualSmallRoughAudit.lean
```

Source SHA-256 values:

| Module | SHA-256 |
| --- | --- |
| `FixedRoughCoefficients` | `24bc451c0234f867cb85539b0d93d37e02c68e6f8d0bf6cf82f081e75e3d892b` |
| `ActualSmallRosser` | `0dbcd4e45ededb9edfb601d8249cc554b3e53291985c09557ed2a9f5d4fb2cdf` |
| `SmallRoughDensityError` | `95854fdf8ac0e0b47368e71fb6a1fae20178bee004c384b80103f9abe45d40ab` |
| `ActualSmallRosserDensity` | `9cfe1beef1a9ef09b88abf3c5593edebafc882e95639c50579cf4dc77b4d5ac8` |
| `ActualSmallRoughAttachment` | `a7b17e728cb6ffe70e3b60c72f1a5d6febd38b12bf208f808a13b748a2da2625` |

## Actual rough mass, strict endpoints and error absorption (12 October 2026)

Five modules extend the actual physical coefficient checkpoint:

- `RosserEndpointBridge` identifies the actual prime carrier, lower and
  upper coefficients, reciprocal-totient densities and Euler product with
  the pinned Goldbach bounding sieve at `Nat.ceil R`. The carrier cap must
  cover the cutoff; integer strict endpoints are preserved exactly.
- `RoughAbsoluteDensity` proves that every retained modulus divides the
  actual rough-prime product, evaluates the full divisor sum by an Euler
  product, and derives one logarithmic interval bound for the absolute
  retained mass. Its analytic constant is uniform in the even target,
  cap, real interval and retention policy. The interval `1<w<=z`, including
  `w=z` and `w<2`, is covered. A truncated cap only decreases this bound.
- `RoughPowerParameters` proves positivity of the actual small Euler
  product and specializes the rough bound to `w=D^(epsilon^2)`, `z=D^r`.
- `SmallRosserErrorLimit` proves the fixed-epsilon limit of the actual
  error, retaining the floor `C*exp(-1/epsilon)`. Exponential decay beats
  the required reciprocal-square cost when epsilon is chosen first.
- `ActualSmallRoughErrorAbsorption` supplies epsilon and one threshold for
  any `r>0` and `eta>0`, uniformly in every later even target, cap and rough
  policy. For the same actual physical rho it proves
  `0 <= density(rho)-V*signedRoughDensity <= eta*V`, with
  `V=actualSmallEulerProduct N cap (D^(epsilon^2))`. The rough-mass bound
  and scalar asymptotic are proved inputs, not terminal hypotheses.

All five sources passed strict direct compilation and individual bundled
kernel replay. The defining-module environment inventory audited all
**42 declarations** (9 endpoint, 9 rough mass, 12 power parameters,
11 scalar limits and 1 actual absorption), including private and generated
declarations. Only `propext`, `Classical.choice` and `Quot.sound` occur
transitively. The final aggregate `lake build` passed with **9,634 jobs**.
The five sources, public root, audit and dependency pins were unchanged
through verification; actual dependency revisions match the manifest.
Evidence is in `.lake/main-theorem-verification-20261012/rough-density/`:
`rough-density-verification.json`, `rough-density-declarations.json`,
`rough-density-theorem-types.txt`, and `final-aggregate-build-status.json`.
This is full aggregate compilation and five module kernel replays, not
complete-root kernel replay or a remote CI claim. No final normalized
sharp K or main analytic theorem is asserted by these modules.

The scale conversion supplied in the following checkpoint needs a cap
covering `w` and a nonzero target:
`V(w) << C_N/log w` contributes a further `epsilon^(-2)`. Absorption at the
manuscript's scale therefore requires a direct choice handling
`epsilon^(-4)*exp(-1/epsilon)`, not a circular post-selection assignment
`eta=delta*epsilon^2`. The exact Euler-ratio correction in the frozen
manuscript is documented in `CURRENT_MANUSCRIPT_MAP.md`; the existing Lean
finite normalization already has the correct factor.

Remaining obligations include the current causal boxed policy and support
exponent, same-raw-weight fixed-rank reverse density limits, sharp signed
rough density, restricted signed distribution, actual current Chen mean,
certificate-to-integral interpretation and final bad-semiprime estimate.
Theorem 1.1 and Corollary 1.2 remain incomplete.

Reproduce the new checkpoint with the pinned toolchain on PATH:

```sh
lake build
lake env leanchecker --verbose ImbalancedChen.RosserEndpointBridge
lake env leanchecker --verbose ImbalancedChen.RoughAbsoluteDensity
lake env leanchecker --verbose ImbalancedChen.RoughPowerParameters
lake env leanchecker --verbose ImbalancedChen.SmallRosserErrorLimit
lake env leanchecker --verbose ImbalancedChen.ActualSmallRoughErrorAbsorption
lake env lean -DwarningAsError=true verification/RoughDensityAudit.lean
```

Frozen source SHA-256 values:

| Module | SHA-256 |
| --- | --- |
| `RosserEndpointBridge` | `eb3f17d88b430e3884f4767139f35999c3b10d921649e65b21fc058a67ac2a22` |
| `RoughAbsoluteDensity` | `1a69ad42b618d8569f1bafcd546257a5b134ebb96d671bbd74adc0beca561d34` |
| `RoughPowerParameters` | `d7df16e77e1d66fe7b0a961c260312679da10e93b1baf1c6d77b0987171b4b64` |
| `SmallRosserErrorLimit` | `36774b9722bcad99ec4a90d86f1191618930d743b5649c5bfe51a66e31f9654e` |
| `ActualSmallRoughErrorAbsorption` | `3b5bec690d259a6116b0ccfd647a375476baf09b631544afdc5707900dce4ca0` |

## Uniform attachment reserve at the manuscript scale (12 October 2026)

Three modules close the small-weight attachment error at `C_N/log N`:

- `ActualSmallEulerNormalization` identifies the actual small product with
  the strict natural sieve product at `ceil w`, then uses the inclusive
  Mertens product at `ceil w - 1`. Finite Euler factorization, the odd-prime
  product bound and the target-correction comparison prove
  `V_N(w) <= B*C_N/log w` with one positive B for every positive even N,
  `w>=4`, and cap covering w. No target-tail convergence is assumed, the
  prime-two factor is retained, and integer endpoints are covered.
- `NormalizedSmallRosserError` uses `t^4*exp(-t) -> 0` to choose epsilon
  directly with `0<epsilon<min(1/8,epsilonMax)` and `epsilon^2<=r`, absorbing
  both reciprocal-square losses. Its fixed-epsilon scalar limit retains
  the positive exponential floor; it is not a fixed-epsilon little-o claim.
- `ActualNormalizedRhoError` supplies epsilon and one real threshold with
  `0 <= density(rho)-V*signedRoughDensity <= eta*C_N/log D`, uniformly in
  every later positive even target, cap covering w and retention policy.
  Its second theorem sets `D=N^nu`, chooses tolerance `eta*nu` before epsilon,
  and produces one natural threshold for the exact `eta*C_N/log N` reserve.
  This target-scale version requires a cap covering `z=N^(nu*r)`.

The same fixed raw retained coefficient and actual small Rosser weights
occur throughout. The D-scale theorem may still truncate the rough carrier;
only the full-cap target-scale version has the cap condition for the
existing complete-interval majorant. Neither theorem identifies this raw
construction with the manuscript's boxed compiler or bounds the signed
rough main density. The causal policy, box compiler, sharp K, restricted
signed distribution, current Chen mean, integral certificates and final
bad-semiprime estimate remain outstanding. Theorem 1.1 and Corollary 1.2
are not complete.

All three modules passed strict direct compilation and individual bundled
kernel replay. The defining-module environment inventory audited all
**47 declarations**: 19 Euler normalization, 10 scalar absorption and 18
actual error declarations, including private and generated declarations.
Only `propext`, `Classical.choice` and `Quot.sound` occur transitively.
The final aggregate `lake build` passed with **9,637 jobs**. The three
sources, public root, audit and pins had identical hashes before and after
verification, and actual dependency revisions match the manifest.
Evidence is in `.lake/main-theorem-verification-20261012/normalized-rho/`:
`normalized-rho-verification.json`, `normalized-rho-declarations.json`,
`normalized-rho-theorem-types.txt`, and `final-aggregate-build-status.json`.
This covers three new module kernel replays and full aggregate compilation;
it is not complete-root kernel replay or a claim of remote CI success.

Reproduce this checkpoint with the pinned toolchain on PATH:

```sh
lake build
lake env leanchecker --verbose ImbalancedChen.ActualSmallEulerNormalization
lake env leanchecker --verbose ImbalancedChen.NormalizedSmallRosserError
lake env leanchecker --verbose ImbalancedChen.ActualNormalizedRhoError
lake env lean -DwarningAsError=true verification/NormalizedRhoAudit.lean
```

Frozen source SHA-256 values:

| Module | SHA-256 |
| --- | --- |
| `ActualSmallEulerNormalization` | `10733388e3a16ceddc1a58387c6fb60a8c261fc46f97666575670251bc523b63` |
| `NormalizedSmallRosserError` | `18b7f3cb38d9b1e534106a173c482e20525352248aec5a8b802fc551804e7be4` |
| `ActualNormalizedRhoError` | `ac6936d7ae3d493d36b3cf5f84c24d9e45cfb21a366bfad13cb09222481558c5` |

The fixed-s raw density remains a separate analytic gap. The pinned
`upperRosserSetDensityRatio_eq_one_add_sum_relativeBoundaryDepths` gives
an exact finite exit-layer decomposition, while the available all-depth
upper and lower theorems give only their respective one-sided bounds.
The scaled-prefix-tail bridge still takes its comparison as a hypothesis,
and a bound on `tail*V` must not be read as a bound on `tail`.
The following checkpoint isolates the exact strict first-cube carrier
`p^3<R` of the raw upper weight. Subsequent reverse limits must link
`R=N^beta`, `y=N^u` at positive fixed or compact exponent parameters and
control deletion of primes dividing N. An equality limit uniform in N
independently of the prime carrier is false: if N contains every carrier
prime, the actual density ratio is one.

## Strict cube reduction and full power Euler constants (12 October 2026)

Four modules advance the same-weight density problem:

- `UpperRosserCubeCarrier` derives `p^3<R` from the first odd-prefix test
  for every prime in an active upper coefficient. Restricting the finite
  prime carrier to that strict cubic region leaves every coefficient and
  every weighted divisor sum unchanged, without assumptions on the test
  function or a positive lower bound on R.
- `PrimeCubeCutoff` identifies the filtered actual prime carrier with
  `min(y,R^(1/3))` for `R>=0`. It retains the target-prime exclusions,
  enumeration cap, and excluded boundary `p^3=R`. For `D>1` and
  `beta<=3*u`, this is `D^(beta/3)`; positive beta gives logarithmic
  coordinate three.
- `ActualRosserCubeReduction` proves exact equality of the actual upper
  coefficient, reciprocal-totient density and divisor polynomial at both
  cutoffs, for every integer test argument. The normalized identity keeps
  the Euler-product ratio as a separate factor. These finite identities
  remain valid for truncated caps and are not density asymptotics.
- `FullPowerEulerNormalization` proves the full leading constant
  `V_N(N^a)*log N/C_N -> 2*exp(-gamma)/a` along positive even targets for
  every fixed `a>0`, and the ratio `V_N(N^a)/V_N(N^b) -> b/a` for fixed
  `a,b>0`. The Mertens product is evaluated at `ceil(N^a)-1`; the actual
  odd-prime product and target-prime tail supply the remaining factors.
  No desired density limit or prime theorem is a terminal hypothesis.

The power-limit theorems use the full product
`finiteSieveDensity N (ceil(N^a))`. Using the actual finite-cap interface
requires a cap covering each cutoff. These four modules alone do not give
uniformity over a compact set of varying exponents; the next checkpoint
supplies it. At `D=N`, the cube-reduction Euler
ratio now has limit `3*u/beta`; the remaining same-raw-weight density at
coordinate three is still open. An upper sieve bound alone does not prove
that its limit is `2*exp(gamma)/3`. Theorem 1.1 and Corollary 1.2 remain
incomplete, including the causal policy/compiler, sharp signed density,
restricted signed distribution, current Chen mean, integral-certificate
semantics and final bad-semiprime estimate.

All four modules passed strict direct compilation and individual bundled
kernel replay. The defining-module environment inventory audited all
**79 declarations**: 8 cube-carrier, 14 cutoff, 16 actual-reduction and 41
full-power-normalization declarations, including private and generated
declarations. Only `propext`, `Classical.choice` and `Quot.sound` occur
transitively. The final aggregate `lake build` passed with **9,641 jobs**.
All four sources, root, audit and pins were unchanged through verification;
actual dependency revisions match the manifest. Evidence is in
`.lake/main-theorem-verification-20261012/rosser-cube/`:
`rosser-cube-verification.json`, `rosser-cube-declarations.json`,
`rosser-cube-theorem-types.txt`, and `final-aggregate-build-status.json`.
This is four new module kernel replays and full aggregate compilation, not
complete-root kernel replay or remote CI success.

Reproduce this checkpoint with the pinned toolchain on PATH:

```sh
lake build
lake env leanchecker --verbose ImbalancedChen.UpperRosserCubeCarrier
lake env leanchecker --verbose ImbalancedChen.PrimeCubeCutoff
lake env leanchecker --verbose ImbalancedChen.ActualRosserCubeReduction
lake env leanchecker --verbose ImbalancedChen.FullPowerEulerNormalization
lake env lean -DwarningAsError=true verification/RosserCubeAudit.lean
```

Frozen source SHA-256 values:

| Module | SHA-256 |
| --- | --- |
| `UpperRosserCubeCarrier` | `a10e233e5e5b944c0dad801ee624a1c389f4b23eab41e31c84d62bc5e2d50b66` |
| `PrimeCubeCutoff` | `8ff53f694ee8de699b2cc240d4b4bf574ca0e1ac68c0b490710c195a4c0d07f7` |
| `ActualRosserCubeReduction` | `a16059f33af6864fe99965d647e96b63a2c3a9100758766452ab0599adcec720` |
| `FullPowerEulerNormalization` | `32f6fba88d1e9bcb40bd2865013187c24d25cd06d72e2b6dacc367a863150371` |

## Uniform powers and actual reciprocal-prime cells (12 October 2026)

Two further modules supply analytic inputs for compact logarithmic cells:

- `UniformPowerEulerNormalization` proves locally uniform convergence of
  `V_N(N^a)*log N/C_N` to `2*exp(-gamma)/a` on `a>0`, then uniform convergence
  on every `[a0,a1]` with `a0>0`, along positive even targets. It uses
  monotonicity in the exponent, the proved pointwise limits and compactness;
  the finite Euler products are not assumed continuous. The actual-cap
  corollary chooses one `N0>=2` before N, the exponent and the cap, with only
  the covering condition `N^a<=cap`. Moving exponents `alpha(N)->a>0` and
  eventually covering caps are included in two path-limit corollaries.
- `ActualPrimeReciprocalMass` proves the actual single-prime mass
  `sum_(N^a<=p<N^b, prime p, p not dividing N) 1/(p-1) -> log(b/a)` for fixed
  `0<a<b`, with no upper bound on b and no parity restriction on N. Its
  canonical cap is `ceil(N^b)`, independent of the target N. Separate exact
  finite bridges pay target-prime removal, denominator replacement and
  opposite half-open endpoints by
  `2*log N/(N^a*log 2)+6/N^a`. The remaining interval limit comes from the
  pinned proved Mertens supplier; the explicit error tends to zero.

These are genuine suppliers, not hypotheses naming the desired limits.
They do not yet prove multi-prime cell masses, the weighted fixed-rank
Rosser boundary integrals, or a same-weight limit equal to F(s). The finite
nonnegative boundary-layer expansion suggests proving arbitrary finite
prefix lower limits and then letting the prefix grow, without claiming
that the normalized discrete tail vanishes. The causal compiler, sharp K,
distribution, current Chen mean and final main theorem remain incomplete.

Both sources passed strict direct compilation and individual bundled
kernel replay. The defining-module environment inventory audited all
**23 declarations**: 8 uniform-normalization and 15 actual-prime-mass
declarations, including private and generated declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur transitively. The final aggregate
`lake build`, including all six new modules from these two checkpoints,
passed with **9,643 jobs**. All six source hashes and the final root, audit
and dependency pins were unchanged through this verification; actual
dependency revisions match the manifest.

Evidence is in `.lake/main-theorem-verification-20261012/power-prime-mass/`:
`power-prime-mass-verification.json`, `power-prime-mass-declarations.json`,
`power-prime-mass-theorem-types.txt`, and `final-aggregate-build-status.json`.
Together the two checkpoints cover six new module kernel replays and
79 + 23 = 102 audited declarations, plus full aggregate compilation. This
does not claim complete-root kernel replay or successful remote CI.

The next checkpoint supplies the actual-carrier bridge using the pinned
exact set-density boundary identity. An alternative public API is
`mainSum_upperRosserWeight_eq_sieveProduct_add_suzukiActualT` and its
odd-depth expansion. The generic expansion already cancels the apparent
extra Euler denominator.
The local dictionary identifies the lower-prime Euler product with
the actual strict product at the boundary prime q. This expresses each
boundary contribution as a product of `1/(p-1)` factors times
`V_N(q)/V_N(y)`, ready for the two suppliers above. The continuous
finite-prefix integral lower bound remains separate from this bridge.

Reproduce the two-module checkpoint with the pinned toolchain on PATH:

```sh
lake build
lake env leanchecker --verbose ImbalancedChen.UniformPowerEulerNormalization
lake env leanchecker --verbose ImbalancedChen.ActualPrimeReciprocalMass
lake env lean -DwarningAsError=true verification/PowerPrimeMassAudit.lean
```

Frozen source SHA-256 values:

| Module | SHA-256 |
| --- | --- |
| `UniformPowerEulerNormalization` | `8888d8d4df618d3504c6fbf08f1b6a132bba16b2a378e68906d2f17240d76475` |
| `ActualPrimeReciprocalMass` | `f2cb90c3751d4bbc1208e9f1694f820befa948bddf1c396ca564c10ccd1e1108` |

## Actual Rosser boundary boxes and a positive density gain (12 October 2026)

Five modules connect the prime-mass suppliers to the same raw upper Rosser
coefficient, rather than an independently chosen comparison weight:

- `ActualPrimeEulerSplit` splits the actual finite Euler product at a prime
  q into strict lower, singleton and strict upper factors. It rewrites the
  boundary denominator as `V_N(q)/V_N(y)` and proves positivity of every
  factor for even targets. The finite identities allow arbitrary caps.
- `ActualRosserBoundaryExpansion` identifies the actual divisor density
  with the pinned subset density at `ceil R`, then proves its exact
  normalized expansion as one plus nonnegative actual boundary terms.
  It requires a covering cap and every carrier prime strictly below R;
  it does not assume any density asymptotic. Selected actual subcarriers
  give lower bounds with the same coefficients.
- `ActualPrimeBoxMass` defines genuine finite tuples of target-coprime
  primes in `[N^(a_i),N^(b_i))`, proves exact mass factorization, and derives
  the limit `prod_i log(b_i/a_i)` for fixed `0<a_i<b_i`. Adjacent separated
  intervals give strictly decreasing, distinct coordinates and identify
  this mass with the reciprocal totient of the tuple product. That last
  identity is not asserted for overlapping intervals.
- `ActualPrimeBoxEulerLower` proves Euler-product monotonicity and an
  eventual lower bound for these tuples weighted by `V_N(p_j)/V_N(N^u)`:
  `(u/b_j)*prod_i log(b_i/a_i)-eta`, when `b_j<=u`. The common threshold
  precedes every later even target and every covering cap. Geometric
  eligibility for a Rosser boundary is a separate obligation.
- `ActualRosserTripleBox` discharges that obligation for three-prime boxes
  satisfying adjacent separation, `b_0<=u`, `3*b_0<=beta`,
  `beta<=a_0+a_1+3*a_2`, and `u<=beta`. It proves the strict first cube
  test, inclusive shell test at `ceil(N^beta)`, and injection of a tuple
  into `(p_2,{p_0,p_1})`. Thus the actual normalized density is eventually
  at least `1+(u/b_2)*prod_i log(b_i/a_i)-eta`, without duplicate counting.

The final module supplies all these geometric conditions for
`u=1/3`, `beta=1`, and the box

`[.30,.32) x [.27,.29) x [.17,.19)`

in logarithmic prime coordinates. Its gain is
`(100/57)*log(16/15)*log(29/27)*log(19/17)`, proved at least `25/31407`.
Choosing `eta=1/10000` proves, with no remaining analytic or geometric
premises:

```text
exists N0 >= 2, forall even N >= N0, forall cap >= N^(1/3),
  actualSmallRosserPlusDensity N cap (N^(1/3)) N
    / actualSmallEulerProduct N cap (N^(1/3)) >= 1 + 1/2000.
```

This is a positive contribution from one actual box. It does not prove
the sharp `F(3)=2*exp(gamma)/3` limit, a continuous boundary-layer integral,
or the manuscript's numerical constants. Disjoint box families, higher
odd ranks and finite-prefix integral lower limits remain open, along with
the boxed policy/compiler, signed distribution, sharp K, current Chen mean
and the final Theorem 1.1/Corollary 1.2. Independent read-only review checked
the same-coefficient identity, quantifier order, Euler-ratio orientation,
strict endpoints, injection and exact numerical gain at the frozen hashes.

All five modules passed strict compilation and individual bundled kernel
replay. The environment-based inventory audited all **67 declarations**:
18 Euler-split, 6 boundary-expansion, 17 box-mass, 10 Euler-weighted-box and
16 triple-box declarations, including private and generated declarations.
Only `propext`, `Classical.choice` and `Quot.sound` occur transitively.
The first four replays were reused only after checking their source,
compiled object, checker binary and log hashes; the fifth was replayed
after its final numeric theorem was frozen. Actual dependency revisions
match the manifest, and both the worktree and index of the actual mathlib
and goldbach supplier checkouts were clean before and after the audit.

The final aggregate `lake build` passed with **9,648 jobs**. All five
sources, the root, audit and dependency pins were unchanged through
verification; both supplier checkouts also remained tracked-clean after
the build. Evidence is in
`.lake/main-theorem-verification-20261012/boundary-box/`:
`boundary-box-verification.json`, `boundary-box-declarations.json`,
`boundary-box-theorem-types.txt`, and `final-aggregate-build-status.json`.
The verification scope is five new module kernel replays, their full
declaration inventory, and aggregate compilation. It is not complete-root
kernel replay or evidence of successful remote CI.

Reproduce the five-module proof checks with the pinned toolchain on PATH:

```sh
lake build
lake env leanchecker --verbose ImbalancedChen.ActualPrimeEulerSplit
lake env leanchecker --verbose ImbalancedChen.ActualRosserBoundaryExpansion
lake env leanchecker --verbose ImbalancedChen.ActualPrimeBoxMass
lake env leanchecker --verbose ImbalancedChen.ActualPrimeBoxEulerLower
lake env leanchecker --verbose ImbalancedChen.ActualRosserTripleBox
lake env lean -DwarningAsError=true verification/BoundaryBoxAudit.lean
```

Frozen source SHA-256 values:

| Module | SHA-256 |
| --- | --- |
| `ActualPrimeEulerSplit` | `d9194dfe21942b277cb3f5fc246ec448472bbc75b14cc30f6cacd9ca22dd74b9` |
| `ActualRosserBoundaryExpansion` | `be0f26dc2405d3ae48d82cf70a72b31105014b8915c2098a1abdf279cdfa6768` |
| `ActualPrimeBoxMass` | `3d17cfda8af10561829b23f7370b7a9481a4856dd7f78be05ebac3926bf1204f` |
| `ActualPrimeBoxEulerLower` | `adc0657ea574d58a0364423062c556119a06380b6edcdb31d6175ca3f99083cb` |
| `ActualRosserTripleBox` | `0fe4d963634c41442fa62f736543c70944f3f8eb0843e08f800ebebc0b02dea5` |

## Finite box families and the continuous three-prime layer (12 October 2026)

The first actual box now extends to the complete continuous three-prime
boundary region. The proof combines true finite sums before taking limits:

- `ActualRosserTripleBoxFamily` proves coordinate-separated boxes have
  disjoint actual prime-tuple carriers. Their union injects into one
  boundary sum via the strictly decreasing tuple's range. Thus the base
  term one occurs once for the family. The eventual theorem allocates
  `eta/(card I+1)` to each box and takes a finite maximum of thresholds;
  it also covers the empty family with an explicit positive outer exponent.
- `LogPrimeBoxIntegral` proves integrability and the genuine Lebesgue
  product-box formula `integral prod_i (1/x_i) = prod_i log(b_i/a_i)` on
  `prod_i [a_i,b_i)`, for `0<a_i<=b_i`. It includes arbitrary constant
  multipliers, degenerate intervals and the zero-dimensional unit box.
- `RosserTripleMesh` constructs finite half-open inner meshes of
  `Omega3={0<x_2<x_1<x_0<1, 3<x_0+x_1+3*x_2}`. Each coordinate exceeds
  `1/3`; every selected cell lies inside the region, distinct cells have
  a separating coordinate, and every region point eventually belongs to
  a selected cell. Strict shell and ordering gaps provide this coverage
  at every point, without assuming a boundary-null-set result.
- `RosserTripleMeshIntegral` proves the selected-cell lower sum
  `sum (1/b_2)*prod_i log(b_i/a_i)` equals an integral of a finite sum of
  indicator-weighted densities. The integrands converge everywhere to
  the Omega3 indicator times `1/(x_0*x_1*x_2^2)`, and are dominated by
  `81*indicator([1/3,1]^3)`. Dominated convergence therefore gives the
  actual set integral `rosserTripleLayerIntegral`, rather than defining
  that integral to be the limit.
- `RosserTripleLayerIdentity` extracts the final coordinate through a
  measure-preserving equivalence, preserves the order of the other two,
  and applies Fubini to the proved integrable region indicator. The slice
  is exactly `q^(-2)*upperRosserBoundaryMass 1 3 q` for positive q, and
  vanishes outside `(0,1)`. The strict shell matches pointwise; the residual
  nonnegativity condition follows from both larger coordinates being less
  than one. The pinned proved source identity then identifies the entire
  integral with `SuzukiFiniteContinuousLayers.suzukiLayer 1 2 3 3`.
- `ActualRosserTripleLayerLower` scales all mesh endpoints by any fixed
  `u>0`, uses `beta=3*u`, and proves every actual-prime box gate and the
  exact cancellation of u in its logarithmic mass and endpoint ratio.
  The continuous limit first chooses a mesh with error `eta/2`; the finite
  family then chooses an N threshold with error `eta/2`. The threshold
  precedes every later even N and every cap covering `N^u`.

Consequently, for every fixed `u>0` and `eta>0`, the same raw upper Rosser
density satisfies

```text
exists N0 >= 2, forall even N >= N0, forall cap >= N^u,
  actualSmallRosserPlusDensity N cap (N^u) (N^(3*u))
    / actualSmallEulerProduct N cap (N^u)
      >= 1 + rosserTripleLayerIntegral - eta.
```

The original `u=1/3, R=N` case is a corollary. The integral is exactly Suzuki
source layer three, with no extra scale, permutation or Jacobian factor.
This proof discharges the
prime-mass, Euler-ratio, mesh-limit and covering-cap inputs to the displayed
first-layer lower bound. It is still not the full fixed-s density limit or
Theorem 1.1/Corollary 1.2. Higher odd ranks and arbitrary finite prefixes,
the causal boxed compiler, sharp K and certificate semantics, restricted
signed distribution, current Chen mean and final bad-semiprime estimate
remain to be proved.

Independent read-only review checked cross-box injectivity and the single
base term, error allocation and threshold order, half-open ownership and
strict inner coverage, actual product-volume integration, the measure-
preserving coordinate order, both Fubini steps, the exact shell, and the
final Suzuki corollaries at their frozen source hashes.

All six modules passed strict compilation and individual bundled kernel
replay. The environment inventory audited all **108 declarations**,
including private and generated declarations: 12 product-box integral,
34 mesh geometry, 12 actual box-family, 34 mesh-integral, 11 layer-identity
and 5 final actual-density declarations. Only `propext`, `Classical.choice`
and `Quot.sound` occur transitively. Four early kernel replays were reused
after checking their source, compiled object, binary, configuration, pin
and log hashes; the identity and final actual-density modules were replayed
after their final versions were frozen. The actual mathlib and goldbach
supplier revisions match the manifest, and their tracked worktrees and
indexes remained clean before and after the audit.

The final aggregate `lake build` passed with **9,654 jobs**. The six source
hashes, root, audit and pins were unchanged through verification; both
supplier checkouts also remained tracked-clean after the build. Evidence
is in `.lake/main-theorem-verification-20261012/box-family/`:
`triple-layer-verification.json`, `triple-layer-declarations.json`,
`triple-layer-theorem-types.txt`, and `final-aggregate-build-status.json`.
This records six new module kernel replays and full aggregate compilation,
not complete-root kernel replay or successful remote CI.

Reproduce the six-module proof checks with the pinned toolchain on PATH:

```sh
lake build
lake env leanchecker --verbose ImbalancedChen.ActualRosserTripleBoxFamily
lake env leanchecker --verbose ImbalancedChen.LogPrimeBoxIntegral
lake env leanchecker --verbose ImbalancedChen.RosserTripleMesh
lake env leanchecker --verbose ImbalancedChen.RosserTripleMeshIntegral
lake env leanchecker --verbose ImbalancedChen.RosserTripleLayerIdentity
lake env leanchecker --verbose ImbalancedChen.ActualRosserTripleLayerLower
lake env lean -DwarningAsError=true verification/TripleLayerAudit.lean
```

Frozen source SHA-256 values:

| Module | SHA-256 |
| --- | --- |
| `ActualRosserTripleBoxFamily` | `ca020750d0f3a39268943d097ac077099b63d86137404070f55107b8f0d18488` |
| `LogPrimeBoxIntegral` | `0880865d5d9770c11d4d61be2d7b8c477d3a1586cac4a42a139e769f4ad23f28` |
| `RosserTripleMesh` | `b3d6dcc66c1f5cc34898badaa5a2a4d5c0d2118647fc097e79974444dfc83752` |
| `RosserTripleMeshIntegral` | `d604a69c3e9ecec37b8e32c64fd5b960f3efddf70ff3954623a58afae2dcd1a3` |
| `RosserTripleLayerIdentity` | `a04f4b7c28a24e586207d5d8af2ca3bea1f31792886f4ed99a6f472c4338e1c0` |
| `ActualRosserTripleLayerLower` | `810df71dae891618530951b1c1fb77859c0e5e7c48c72c336b7275be3f605d37` |
