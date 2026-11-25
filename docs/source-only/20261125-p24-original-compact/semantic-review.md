# P2.4 original compact semantic review — 2026-11-25

## Status and scope

Source inspection only. **No semantic bug was found in the checked operational path. The decisive two-million-split finite guards remain UNEVALUATED; this note supplies no compilation, kernel, or numerical-run receipt.** The reviewer made no Lean changes and ran no compiler or numerical generator. The reviewed working tree was based on repository HEAD `543643fd074ca989e7b21d3b2f749531bb0e89c8`.

The scope is the original Q80 compact third integral, its actual adaptive run, complete charge forest, and original whole-functional endpoint. It excludes the independent P160/P112 replacement path, later savings, physical-density asymptotics, and the final current-K counting theorem.

## Pinned manuscript and replay sources

Publication repository: `UyNewNas/chen-imbalanced-semiprimes`, frozen commit **`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`**. The commit publishes the frozen 20261106 bilingual manuscript.

| Source at that commit | Binding or relevant section |
| --- | --- |
| `paper/release-20261106/en/numerical-appendix.tex` | `app:numeric`; directed arithmetic and delayed-function enclosures; upper density; `num:complete-tail`; `num:certificate-chain`. Lines 232–233 require a disjoint compact partition with conservative boundary-box upper bounds. Lines 53–65 retain primitive enclosure obligations. |
| `paper/release-20261106/en/sieve-appendix.tex` | `sv:selected-gate`, `sv:full-gate`, `sv:branch-licence`, and `sv:third-envelope`; individual branch conditions remain attached to the cap policy. |
| `proof-library/source/extended-prefix-upper.tex` | `eq:extended-prefix-functional`: literal first-stop/variable-third-cap functional. Older analytic-interface references in this supporting fragment are not adopted as new assumptions here. |
| `verification/data/certify_extended_prefix.py` | SHA-256 `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`. Original Q80 generator, initial roots, strict outside tests, priority loop, and original fixed first/tail terms. |
| `verification/data/certify_extended_prefix.json` | SHA-256 `f13a607d03e46987e12c4192bfe466a20827f1b2778e4659b2210e7aa00c18ab`. Historical output used as the comparison target, not imported as a proof. |
| `verification/data/certify_conservative_chen.py` | SHA-256 `67b9429667e18786058e0fe58676fbe09d556868468f1281166cac2b55f8604e`. Original Q80/log32 interval dependency. |

The 20261106 numerical supplement is distributed separately at Zenodo record `23755453`. This review did not download it or independently check its renamed `generator-*`/`record-*` aliases; the original named files and bindings above were read at the fixed Git commit.

The compact object uses `Theta = 299/500`, `rho = 19/96`, `mu = 25/128`, `h = 1/100`, coordinate denominator `805306368000`, and `Q = 2^80`. On ordered triples with `h <= z <= y <= x <= rho` and `x+y+3z <= Theta`, its kernel is

\[
4\,\frac{\bar f((\Theta-x-y-z)/z)-\bar f((L-x-y-z)/z)}{xyz^2},
\qquad \bar f=f/(2e^\gamma).
\]

Here `L = min(Theta, Phi)` below `mu`, and the original fallback uses `v(x)` above `mu`. The symmetric above-mu extension uses `v(max(x,y))`. The factor 4 already belongs to the kernel and rectangle mass.

## Operational correspondence checked

All Lean references below are in `ImbalancedChen/`.

| Area | Definitions and review conclusion |
| --- | --- |
| Priority and ties | `P2OriginalPrioritySerialQueue.Before`, `issueSerial`, `advance`, `children`, `afterChildren` reproduce the Python key `(-(hi-lo), serial)` and allocate serials only for positive error. Left child precedes right child. `P2OriginalCompactConcreteLoop.originalRun_serial_nodup` accounts for multiplicity, so Python's later tuple fields never break a reachable active-key tie. |
| Heap semantics | `P2OriginalEfficientPriorityHeap.deleteMin_spec` proves both minimum selection and exact multiset preservation. The manifest-pinned Batteries source at commit `41bd267b3f6b7252f6676af46d4ffc6783b64de9` was inspected. Its heap layout differs from Python's binary heap, but unique ordered keys determine the same selected item. |
| Initial order | `P4AOriginalInitialSeedInventory.initialSeeds`, `seedStrip`, and `records` retain cuts `h, 2h, 4h, 8h, 16h, mu, rho`, with x outer/y inner order. There are exactly 21 raw roots, in producer order. |
| Split choice | `P2OriginalAdaptiveSourceSplit.chooseWider`, `originalAxis`, `originalMidpoint`, `sourceLeft`, `sourceRight` retain the strict relative-width scan 0 then 1 then 2, incumbent on ties, floor midpoint, and side0/side1 order. The integer width-at-least-two check is equivalent to the original strict midpoint assertion. |
| Boundary branches | `P2OriginalCompactQ80Encloser.outside` preserves original strict `>` tests, not the independent replay's `>=` tests. `symmetricHalf`, `inside`, and full-cap/zero-loss/Jensen branches match the original. Interval-operation order was checked for means, chord weights, first-series endpoints, and the tail. No rounding-changing regrouping was found. |
| Stop and budget | `P2OriginalCompactConcreteLoop.keepRunning`, `runFuel`, `stopResult` and their cached counterparts use `splits < 2000000` and `target <= fixedUpper + totalUpper/2^80`, with target `6809/1000`. Equality continues; strict target crossing stops. At the budget boundary the first condition is false, so fuel zero returns budget stop rather than exhausted-fuel failure. |
| Table and cache | `P2OriginalCompactQ80ArrayTable.appendNode`, `buildFrom`, `tableArray_lookup` reproduce the full original table with 196609 slots. `P2OriginalCompactQ80CacheEncloser.encloseWith_eq` and `fixedUpperWith_eq` are symbolic exact equalities, not numerical assumptions. `P2OriginalCompactCachedRun.cachedRun` binds the shared array and fixed term before the loop. No original functional `sourceState` query was found on its checked cached data path. |
| Update and complete ledger | `P2OriginalCompactConcreteRun.driverStep` and `P2OriginalCompactCachedRun.cachedStep` subtract the popped parent's charges and add both children. `cachedEntries`/`cachedOrderedUpperCharges` traverse every terminal leaf; only queue insertion filters positive error. Exact and empty leaves remain in the forest and total. |
| Closed finite comparison | `cachedHistoricalEndpointCheck` accepts only budget stop with 2000000 splits, upper total `144590669409566793572719`, active heap size `1852040`, and the stated assertion accumulator true. `cachedRun_eq`, `cached_ordered_upper_sum`, and `cached_complete_leaf_count` bind that result to the original run and complete forest. These definitions and symbolic proofs do not establish that the closed guard evaluates to true. |

The complete terminal forest has **2000021 leaves**, whereas the historical active heap has **1852040 entries**. These quantities are intentionally different. The final integral charge is not a sum over only the active heap.

No concrete opaque/oracle-dependent obstruction to kernel reduction of the inspected finite data path was found. Ordinary `def` bodies, finite recursion, and exact arithmetic are used. This is not a resource or completion guarantee; actual resource failures must be reported from execution, not inferred as mathematical errors.

## Mathematical enclosure versus full Python assertion refinement

`P2OriginalCompactQ80Encloser.sourceAssertions` explicitly records only part of the original Python assertion inventory. It must not be described as a complete AST/assertion refinement certificate.

**That partial inventory is not a new premise of the mathematical endpoint proof.** In `P2OriginalCompactQ80CompleteSoundness`, `enclose_contains_integral` takes only `Geometry box`. `Geometry` contains coordinate bounds, positive widths, and the x/mu cut; it contains no desired cap, mean, charge, or integral estimate. Residual positivity and required logarithm/Jensen denominator conditions are derived in the analytic chain. `forestEntry_contains_integral` obtains Geometry from the original 21 roots and literal midpoint children via `P2OriginalCompactQ80Reachability`.

Thus the complete-forest enclosure does not assume `assertionsPassed = true` or a per-leaf enclosure certificate. For P2.4's stated leaf covering the original literal source domain, parameters, concrete run, and complete endpoint binding, compilation of those soundness proofs plus successful evaluation of the actual finite guard is the relevant closure. Claiming that every Python internal assertion is separately reproduced would be a stronger, distinct claim.

## Supported endpoint and exclusions

The original compact comparison is

\[
I_{3,c}\le\frac{144590669409566793572719}{2^{80}}.
\]

`P2OriginalCompactQ80FixedBindings` retains the original first integral and original table/log32 tail. `P2OriginalCompactWholeFunctionalEndpoint.original_whole_functional_le_archived_upper` consumes the complete compact term once and the original tail once, yielding the source candidate

\[
\frac4\Theta+I_1+I_3
\le\frac{1230679674488580033396846301}{180734410032387061618573312}
<\frac{681}{100}.
\]

The archived upper rational exceeds the old stopping target `6809/1000`; this agrees with the original JSON's `strict_upper_target_verified: false`. It is compatible with the supported `681/100` endpoint. It is not a proof of the later selected `K = 6.7617368`, which also uses separate savings and assembly.

The independent compact replay explicitly reports `original_leaf_partition_replayed: false`. Its achievement of the old allowance does not establish the original run/charge instance and is not used to close this review's target.

**Conclusion:** no semantic discrepancy was identified in the checked original operational path. Final completion credit still requires actual compiled soundness and a successful closed two-million-split guard; this source review grants neither by itself.
