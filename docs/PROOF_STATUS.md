# Verification boundary

This project is not a proof of Goldbach's conjecture or of the attached manuscript's main analytic theorem.

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
