# Verification boundary

This project is not a proof of Goldbach's conjecture or of the attached manuscript's main analytic theorem.

## Latest verified checkpoint

Commit `beb8a4d03e5fb0148b17907b298c4f60d59895a9` passed full build, bundled replay of all 80 owned modules and the root, and the 1992-declaration transitive axiom audit in [PR run 37872524090](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37872524090), with only `propext`, `Classical.choice` and `Quot.sound`. The three new owned prime-window and moving-weight modules described below are CI-pending additions toward an 83-module checkpoint. Their source presence does not extend the verified checkpoint.

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


## Quotient geometry and finite mass verified; prime-window and moving-weight inputs pending

Commit `beb8a4d03e5fb0148b17907b298c4f60d59895a9` passed unchanged full build, exact replay of all 80 owned modules plus the root, and the 1992-declaration standard-three-axiom audit in [PR run 37872524090](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37872524090) and [push run 37872519987](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37872519987). ChenQuotientLevelGeometry, ChenQuotientDensityTransport and ChenQuotientMassFinite are now verified. The sole repair replaced one omega positivity step with an explicit natural successor proof; no statement, hypothesis, source carrier or verification gate changed.

The next three owned source modules remain pending full CI verification:

- ChenPrimeHarmonicFinite relates the actual prime selector to its original centre-divisor mask, pays at most two atoms for the [A,U) versus (A,U] endpoint convention, and uses the proved reciprocal-square tail for the 1/(p-1) versus 1/p correction. For N > 0, 2 <= A < U, a nonnegative fixed bound M and |f| <= M on the closed endpoint window, its combined finite error is at most (2M log(N)/log(2) + 6M)/A. The varying centre mask is charged through prime-factor incidence; it is not dropped by a fixed-centre argument. No Mertens theorem or target harmonic limit is imported into this finite module.
- MovingWeightTransport bounds an error by a uniform summand bound times the total nonnegative carrier weight, rather than the number of labels. It turns compact uniform continuity of a fixed continuous test into a summable vanishing perturbation when both coordinates remain in the same fixed compact set and the total carrier mass is eventually bounded. The test can be signed. The mass bound, uniform coordinate approximation and any fixed-profile limit used for a final limit are explicit premises; an independent mass limit can supply the bounded-mass premise.
- ChenQuotientMovingWeight uses the verified uniform row geometry to place the actual parameter and logarithmic profile in a single fixed interval with positive padding. Its transport statements are uniform over positive multipliers in a fixed power range below the square-root exponent and retain every label. The nonnegative carrier-mass bound and analytic fixed-profile limit remain to be supplied for the intended prime or pair application. This module neither assumes the desired moving-profile conclusion nor grants a lower-positive sieve gate on the full sixth band.

These three elementary modules add no foreign consumer to the owned root and make no VariableEnvelope change. The genuine prime harmonic supplier adapter and the concrete moving-prime consumer stay separate and uncompiled here. A generic continuous-test pair limit, valid upper/lower-sieve assembly and the complete eleven-term coefficient remain additional mathematical and verification work. No coefficient 1.8271 or full Chen theorem is claimed.
