# P5.6 → h34 — actual occupied position mass and original q unpaid envelope

Date: 2026-11-09 UTC.
Repository: UyNewNas/goldbach-formalization.
Isolated branch: chatgpt/p5-h34-actual-occupied-mass-20261109.
Verified input baseline: `972acf8c0631c0f00a76d4e73416b305a6b48e00`.
Mathematical source commit: `563461447a4e3cf13eafbee28b3b97ec19e5c780`.
Read-back source Git blob: `c32fde1addd5dee47a529a60726fb2558e1aef4b`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` (blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).
Pinned toolchain: Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual manuscript-local mathematical increment

One new file: `Part5OriginalH430ActualOccupiedMass.lean`, 190 source lines, 7 candidate theorem proof bodies and 4 definitions.

The preceding `ActualSievedPositionPayment` packet showed that any ONE resolved position with positive literal source-sieve cardinality contributes at most the true same-Q Phi, lowering the unpaid original q-count bound by its weighted source term. This packet makes a stronger, genuinely finite multi-position payment ledger without confusing arithmetic q with history product d.

1. `actualPositionSourceCount` evaluates the installed `sourceSieveCount N d (d*N)` at the ORIGINAL integer parent product and SAME physical root Q with its exact cutoff `(Q/d)^(1/(11/5))`. The actual product is not postulated to be an original quotient prime q.
2. `actualOccupiedPositions` filters the original `activePositions` Fin indexes by strictly positive source-sieve cardinality. Different live request positions with identical d remain separate. `occupied_positions_are_resolved` proves this is a subset of the actual resolver output.
3. `actual_Phi_eq_occupied_position_sum` proves an EXACT identity for original Phi: only occupied positions contribute, each with the original positive `levelMark`, and positions with zero natural source count vanish.
4. `actual_occupied_mass_nonneg`, `actual_occupied_mass_pos_of_nonempty` and `actual_occupied_mass_le_Phi` use the actual finite support and the elementary natural fact that every occupied source count is >=1. Consequently **the sum of ALL occupied original path marks**, not merely one mark, is a proven-candidate lower bound for the real source Phi.
5. `actual_unpaid_le_occupied_mass_envelope` transfers that unconditional bound to the original arithmetic receiver count:
   `actualUnpaidAt <= max(card(originalReceiver)-5*actualOccupiedMass, 0)`.
   This still retains a possibly large UNPAID gap and does not assign any particular q/tag to a historical position.
6. `actualU34OccupiedEnvelope` and `actual_U34_unpaid_le_occupied_envelope` sum this tighter bound separately over the ORIGINAL U3 and U4 tagged root bands. Overlap is deliberately counted twice, with root-specific physical Q and arbitrary actual depth choices. This is neither a selected-count owner theorem nor an H430 asymptotic estimate.

This source strengthens the previous one-position and ordinary whole-count envelopes into a finite ALL-occupied-position weighted ledger. It does NOT establish uniform source occupancy, a positive lower bound large enough for the H430 coefficient, the true selected owner, q/tag capacity, or correct historical signed Euler payment. It retains the exact original c/K, root norm 7/2, row norm 12, alpha, common Q per root, scalar/specified-cell difference, and 430+11 reserve geometry.

## Validation and ownership

The authenticated owner has push permissions. The predecessor 20261105 REPORT, REGISTRY and EXTERNAL_INPUTS were read, followed by the newest 20261109 occupied-source predecessor REPORT/REGISTRY and exact Lean source. Existing same-task/other-task branch ownership was respected by creating a NEW isolated h34 branch from the verified prior HEAD, touching only this new subdirectory. No merge, force-push, old file overwrite, manuscript edit, P1.4/P3.6 edit, toolchain or CI change.

The GitHub mathematical source commit was read back: exactly one new 190-line Lean file and zero deletions; Git blob `c32fde1addd5dee47a529a60726fb2558e1aef4b`. A source-only delimiter/forbidden-proof-marker scan passed. These tests are **NOT Lean parsing, elaboration, compilation, kernel replay or transitive axiom auditing**. The execution container has no Lean, Lake or Elan executable and native github.com DNS was unavailable; the prior source-only import closure is not installed as production ImbalancedChen modules. No CI was dispatched, no numerical430 finite guard was evaluated, and no green formal credit is claimed.

## Remaining internal mathematical obligations and next exact step

- Identify the TRUE original upper H430 U3/U4 selected-count owner, stage/physical z0 and root weights. Prove full/selected/inherited source filters on genuine Fin positions, including cross-q collisions and U4 double tag payment capacity.
- Show quantitative actual occupancy and mark mass from the real source/resolver, strong enough to make the UNPAID original q debt fit the H430 reserve. The present mass inequality is unconditional but does NOT supply this missing lower bound.
- Pay all six rejection lanes, signed Euler suffix, first-excluded direction, selected-count owner and historical position erasures.
- Close request-level all-action CLOSED-CELL arithmetic induction; correct base/switched/seed/floor, feedback rounding to integrals, PP/same-rho and outer Theta-count correspondence.
- Complete native-history proper/equality/inherited mass and one shared nested 430+11 causal refinement.
- Stage pinned source-only imports and run targeted Lean/Lake compilation, kernel replay, transitive axiom audit and finite numerical430 certification before claiming verified results.

No new external analytic theorem or assumed count licence was introduced. See EXTERNAL_INPUTS.md. **完整h34稿内证明仍未闭合。**
