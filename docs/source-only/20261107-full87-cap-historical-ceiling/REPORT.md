# P1.4 — actual eight-word historical ceiling below the original frozen cap

## Immutable recovery pins
Base: `6d0b742da97dbdceb28103f1b386ab0c269988b2` on `chatgpt/p1-full87-odd-gates-physical-tuple-20261107`. New isolated branch: `chatgpt/p1-full87-cap-historical-ceiling-20261107`. Manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; c=49044063/25000000, K=8452171/1250000.

## New manuscript-internal SOURCE_ONLY candidate proofs
1. `nodup_toFinset_prod` explicitly tracks the conversion of each strict finite suffix word into the original Rosser set-product; duplicates are not silently dropped.
2. `ordered_tuple_gates_imply_eight_ceiling` starts from the four distinct ORIGINAL processing-prefix gates, recovers exactly the suffixes of sizes 1,3,5,7 in the reversed eight-word and reuses `actual_eight_odd_square_ceiling_lt`; both odd parity and the extra square on the youngest of each suffix are retained. No synthetic prime list replaces occurrences.
3. `owned_actual_history_ceiling_below_cap` obtains `selectedPrefix.length=8` and strict order directly from `owned87_eighth_state_exact_carrier`, recovers the entire actual list with `primeHistoryTuple_reverse_ofFn`, uses `primeHistoryTuple_strictAnti`, and applies `owned_four_physical_tuple_gates_below_actual_cap` at the SAME cap. Under original (4,width(n)<width(r)) and (N>1), obtains the strict finite inequality (J(H)<R_{cap}) for every genuine owned occurrence.
4. By existing `actual_inherited_nil_of_history_ceiling` and cost-zero result, the CAP-side rank-nine inherited odd-history-square occurrence list and its physical reciprocal cost are exactly zero. No claim about the parent side, the cubic failure mode, terminal arithmetic or signed monotonicity.

The source is an **UNEVALUATED / UNCOMPILED Lean candidate**, not a theorem checked by the kernel; the preceding statements refer to supplied proof bodies pending elaboration. No axiom, sorry/admit, native_decide, unsafe or equivalent goal-carrying assumption introduced.

## Actual checks
- Read last HEAD, complete predecessor .lean and REPORT/REGISTRY/INPUT_BOUNDARY/HANDOFF, eight-word J proof, actual eighth carrier, prime-log coordinate and finite geometry definitions, rank-nine inherited nil proof, fixed manuscript blob.
- Root/parent AGENTS.md lookups: not found on this branch.
- 20,000 independent exact integer eight-distinct-prime tests: original Rosser odd-suffix ceiling equals maximum of the four processing-order products, all passed. This does not validate Lean elaboration, archive or asymptotics.
- No Lean/Lake, kernel replay, transitive axiom check, independently reviewed proof, saved87 reproduction or CI; source-only blob SHA in registry.

## Remaining obligations
The effective cap-side historical-shell invoice is removed **only conditional on this candidate elaborating**. Parent-side historical crossing and the cubic annulus still require same-rho quantitative weighted reciprocal costs and one-time legitimate reserve allocation; no reserve paid. Continue with real owner/cap physical support, archive evidence, ordinary continuation integral, signed sixth losses, primitive/AP/centre/modulus, saved87 full numerical gain, changed/tagged, compiler and density reserves. Verify candidate compilation before promoting any status to COMPILED or GREEN. No external theorem is invoked in this packet.
