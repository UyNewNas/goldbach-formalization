# P3.6 — cutoff balance and complete joint low-rank log assembly

Base commit: `2d4e1355be2c5f4ae663c8ab7a7fada95b6d0ccc`.
Base tree: `1ac4de6711f674922c7a87e3197cc3dc72d6f620`.
Branch: `chatgpt/p3-joint-log-assembly-20261103`.
Packet: `docs/source-only/20261103-p3-joint-log-assembly/`.

**SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED. Full P3.6 remains yellow.**
Four new proof modules supply the scalar balance, actual joint-row arbitrary-log estimate, complete grid/mother summation and original physical low-rank source endpoint. No Lean/Lake/compiler, kernel replay, transitive-axiom audit, repository numerical producer, repository proof guard, Codex task, connected-computer operation, child agent or explicit CI dispatch was run. The included scalar regression is not a proof checker. No independent reviewer is claimed. Earlier packets, production imports, main branch, dependencies, toolchain, manuscript, constants, full87 work and external tracker are unchanged. The new branch requests skip-CI; there is no PR, merge, release or paper publication.

## What is now supplied at source level

The preceding dyadic packet bounded a complete joint Cartesian row by `2D*(Low + E*Phi)` with no selectorMass or headMultiplicity, but left its cutoff and logarithmic costs explicit. This packet supplies the parameter choices, derives the required common threshold from the existing power/log limits, and performs both grid-index sums and the full literal mother occurrence LIST. Its final low-rank nonempty-lane bound no longer contains selectorMass, headMultiplicity, an outside-pair count, a head-block count, a free cutoff or an unprovided analytic estimate.

The qualification matters: the coefficient class is still the original upper rough-MODULUS-rank-at-most-two coefficient. An outer Gamma mother can have any of its original permitted lengths. The empty-word lane and the high-rank coefficient remain explicit and unpaid. This is not full hUniformPP or positive-Theta closure.

## Fixed orders and scalar budget

Use `a` for the requested LOCAL ROW logarithmic accuracy, `J` for a fixed joint moment order and `ell=log x`, with `ell>=1`. Define

`H = cutOrder a J = a+J+4`,
`S = primeOrder a J = a+J+2H+3`,
`b0 = ceil(log(ell^H)/log 2)`.

The inherited cutoff lemma gives `ell^H <= 2^b0 <= 2*ell^H`. The analytic cutoff is chosen from the complete local scale x, not a residual quotient or the physical coefficient level. Its order is fixed before x, N or any arithmetic data.

Let `g=2+abs(log 2)`. With the original complete scales `M*V=x`, `M,V>=1`, the actual beta logarithm obeys `1+log(2V)<=g*ell`. For `J>=cs.length+2` and `J>=(cs.length+3)^2-1`, the previous explicit joint energy is bounded by

`E <= 2*g^J*height*sqrt(x)*ell^J`.

The actual small-conductor budget includes the cutoff SQUARE and two reciprocal-totient logarithms. Requesting prime accuracy S gives

`Low <= 32*C*g^J*height*x/ell^(a+1)`.

The existing positive factor floors `x^(34/1135)<=M,V` and the actual modulus gap `Q<=x^(9/20)` imply, at one threshold,

`ell^H <= x^(17/1135)` and `ell^H <= x^(1/20)`.

These pay the three high-conductor terms. The first and third leave exponent `a+3`; the middle leaves `a+1`. Their fixed coefficient is explicitly retained as

`2*g^J*[64 + 256*(lsLogCoefficient+1)*dyadicCountCoefficient + 128*lsLogCoefficient]`.

Finally `2D <= 2*dyadicCountCoefficient*g*ell` pays both prefix lanes and every binary head scale. The combined estimate is a fixed constant times `height*x/ell^a`. No stronger large-sieve theorem is substituted and no existing logarithmic loss is dropped.

`P2GammaJointLogBudget.exists_joint_scalar_threshold` supplies this entire scalar implication. Its threshold depends on a and J, not on the later selector height, word, row or policy. The finite helper assumptions are primitive algebraic scale conditions; the next module supplies all of them from actual source occupancy.

## Actual joint rows and original N

`P2GammaDyadicJointLogSaving.exists_joint_row_log_saving` invokes the prior `exists_chosen_joint_row_estimate` at the stronger prime order S. Actual occupancy supplies the factor floors, cap floors and complete scale `N^(1-kappa)<=x<=N`. The existing original-scale threshold and log-unit transport then give

`norm(jointSignedRow) <= C*height*N/(log N)^a`.

One N threshold precedes every later c, tail word within J, grid indices, allowed nu/epsilon, retain/cap policy, finite modulus subfamily, selector and its nonnegative height. Nonoccupied original charts are exactly zero by the previous source theorem. There is no occupancy assumption in this final row statement.

## Full original grid and mother list

`P2GammaJointMotherLogSaving` proves exact finite-sum identities with the PREVIOUS `headWordError` and `headJointError`. The outside old-pair sum remains inside the joint row before norms are taken. The same upperRho, signed q-coprime mean, original labels and mother repetitions remain unchanged.

The existing symbolic `jointListMomentOrder originalMotherOccurrences` bounds both needed orders for every nonempty occurrence. No list maximum or finite project certificate is evaluated. For a fixed positive mesh exponent B, the row request is increased by `2*(B+1)` to pay `gridLength^2<=9*(log N)^(2*(B+1))`. Both grid indices and the complete literal mother LIST are then summed.

`exists_joint_head_log_saving` supplies

`abs(headJointError) <= C*height*N/(log N)^A`.

For any fixed height and tolerance eta>0, `eventually_joint_head_logAccuracy` requests one additional logarithm and consumes the existing logarithmic decay theorem, giving `eta*N/(log N)^A`. The SAME mesh exponent B is kept when requesting stronger accuracy; there is no circular finer-mesh choice after the constants or threshold.

## Original physical endpoint and actual compact coefficient

`P2GammaActualJointLowRankLogSaving` selects precisely the earlier chosenWidth/chosenGrid for target A. The new full joint head estimate and the previous joint discarded estimate are each invoked with eta/2 on that same grid. Their exact source identity yields

`abs(E_Gamma_low - E_empty_low) <= eta*N/(log N)^A`.

The existing active-low-support identities restore the ORIGINAL `physicalUpperModuli = actualSmallRoughModuli`; the statement is not left on an auxiliary enumeration carrier. No assertion that the high branch lies below N is needed.

The final declaration is

`ImbalancedChen.P2GammaActualJointLowRankLogSaving.eventually_actualCompact_joint_logAccuracy`.

For the ACTUAL existing policy `actualExtendedThirdCompactUpperPolicy e h m N false`, it supplies

`abs(E_Gamma_full - E_Gamma_high - E_empty_low) <= eta*N/(log N)^A`.

All three functionals use the same original physical modulus carrier and the actual coefficient split. The high branch is the existing remainingRho, not defined from a desired error. This removes the old final bound's `C*selectorMass` term for the low nonempty lane. It does NOT pay the high branch or the empty-word lane.

Quantifier order: fix positive height, natural A, `0<kappa<=1/100` and eta>0; choose the common N threshold; then vary N, `0<=nu<=1`, `0<=epsilon<=1/1000`, the actual compact policy parameters/cap and EVERY nonnegative selector bounded by the fixed height. No total selector-mass bound or positive family-mass lower bound is used. No final-full87 identification is claimed.

## Remaining obligations and status scope

The explicit cutoff/logarithm and grid/mother assembly is source-covered for the original upper low-rank NONEMPTY lane. Full P3.6 remains open because the actual causal selected-family/common physical-Q identity, positive-Theta relative conversion, empty-word source, high-rank/enhanced and other coefficient classes, permitted extra coupled profiles and final full PP/spectral assembly are not supplied here. No hUniformPP, hLower, hUpper or unconditional Goldbach theorem is claimed.

Earlier completed narrow leaves retain commit `2d4e135`. The new cutoff/grid/mother and physical-endpoint leaves belong to the containing commit of this packet. Final user-facing status must include the actual returned commit SHA; no source-only leaf is green. The external tracker is not mutated.

## Inspection and validation boundary

The earlier delivered ZIP sources were read at their mounted paths. The base branch and commit/tree were freshly checked through GitHub. Pinned repository bodies read for this increment include PrimitiveScaleThreshold, ConductorScaleThreshold, OriginalScaleTransport, BoundaryArbitraryLog and the original joint mother moment definition. The existing dyadic row, energy and small-conductor proof bodies were inspected from the prior packet. No new external analytic result or current-library upgrade is used. The original manuscript and every transitive proof were not re-audited.

`check_packet.py` inventories exact bytes/imports/declarations, scans comment-stripped proof text and delimiters, verifies 2,121 exponent-allocation instances, and runs 192 independent high-precision scalar regressions with the required power/log threshold inequalities. All passed. These are finite implementation sanity checks, not Lean elaboration, kernel replay, a proof of Python/Lean correspondence, or verification of the imported analytic arguments. CHECKS and INVENTORY record their exact output. VERIFY remains unexecuted.
