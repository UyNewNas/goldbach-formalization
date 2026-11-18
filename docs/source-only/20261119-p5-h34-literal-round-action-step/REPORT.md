# P5.6 → h34 — literal Q80 action-level CLOSED-CELL successor and overflow witness

Date: 2026-11-19 (Asia/Shanghai).
Dedicated continuing branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Verified incoming HEAD: `452ad3de4c90132ad818f71c9c74427019855e21`.
Mathematical source commits: `677bee008620e1cc3f58e8eb22f019a924e4a787` (initial), `d2c97e7c1ea6164360836e8a43293823c54e9db4` (scope and source cleanup).
Source blob after correction: `2c252fd72cada147a92f3badd1bda08e7edca85d`.
Module: `Part5OriginalH430LiteralRoundActionStep.lean`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned toolchain (not changed): Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## What was actually added

The previous packet `uniform_actual_prefix_closed_cell_winning_budget` paid *conditional* summed read-minus-child action errors over genuine causal prefixes, but had not supplied a predecessor-to-successor CLOSED-CELL table step. This packet returns to the original pinned Q80 integer producer, `P2Selected430CausalOccurrenceExporter`, and constructs that exact one-round **reduction** with proof bodies.

The producer has one actual `roundDecision`: retained value; for cells `i >= 50`, the actual cross-table Buchstab suffix (including the upper `max 50 (i-49)`); and, **upper table only**, a left-to-right scan of the original `List.finRange 106` bank rows, offered only if `i.val` belongs to `(rows k).targets`. Each bank candidate uses the original integer quotient, original row divisor, physical read occurrences, and original tie policy. These are finite producer statements, not additional count channels.

Six exported theorems and four private proof lemmas are provided:

1. `literal_round_le_of_three_action_bounds`: exact one-round integer upper bound from three explicitly named same-table candidate inequalities (retained, conditional Buchstab, targeted upper-bank). It does NOT sum unchosen alternatives as costs.
2. `actual_iterate_succ_le_integer_ceiling`: instantiate that rule at every actual `g : Fin 430` using `iterate (g.val + 1) = roundTable (iterate g.val)`. No modulo wraparound at generation zero.
3. `literal_round_overflow_has_actual_action_witness`: conversely, if the actual next numerator exceeds its proposed integer ceiling, a retained, enabled Buchstab, or targeted upper-bank candidate must be a concrete witness of overflow.
4. `actual_iteration_overflow_has_action_witness`: transfer the exact three-channel alternative to the real 430-generation iterate.
5. `floorValue_le_of_integer_ceiling`: preserve the literal `2^80` integer-to-real normalization; no approximate replacement or clipping.
6. `actual_succ_closed_cell_of_literal_action_ceiling`: if the three true integer candidate checks and an independent closed query-cell envelope `floorValue (ceiling upper) i <= F upper s` are proved, then the successor's original `floorValue (iterate (g.val+1) upper) i <= F upper s` follows on every original `queryCell i`, separately for upper and lower.

This **does not prove** that the needed integer ceilings and real envelopes hold for the frozen analytic F, nor that the Buchstab/bank candidates receive sufficient positive analytic payment. The result is a true literal *step-reduction*, not a completed 430-stage CLOSED-CELL induction or an original U3/U4 count theorem. The all-action upper-bound obligations remain in the antecedents and are not relabelled external inputs.

The proof does not change `iterate`, `seed`, `roundDecision`, `rows`, selected read modes, original Q, thresholds, c/K, root norm 7/2, row norm 12 or the 430+11 budget. It does not touch P1.4/P3.6 or any production source.

## Validation and ownership

The GitHub connector reported repository push permission and the dedicated branch HEAD `452ad3d` before writing. The inspected branch Actions query returned 12 completed runs (no queued/in-progress run on this branch). New edits are only in `docs/source-only/20261119-p5-h34-literal-round-action-step` and were pushed as normal fast-forward contents API commits with `[skip ci]`. No CI/workflow or dependency setting is changed.

Runtime inspection: no `lean`, `lake` or `elan` on PATH; native git HTTPS failed DNS lookup; fixed source-only import closure was not installed. No Lean compilation, Lake build, kernel replay, transitive axiom audit, independent verification or finite certificate replay was possible or performed. The ten proof bodies have only source-text inspection; **not one is marked COMPILED or green**.

## Remaining manuscript-internal obligations

1. Stage the unchanged import closure and compile this module and its exact ancestors. Repair any actual Lean elaboration errors; text scans are not evidence.
2. Derive the **three original candidate ceiling inequalities** from frozen same-Q Buchstab, retention, all 106 genuine targeted bank rows and original arithmetic/analytic estimates. The new witnesses isolate any failure; a fresh assumed closed-cell result is prohibited.
3. Supply an accurate initial seed/analytic F bound and prove the actual `g -> g+1` CLOSED-CELL induction for all 430 rounds, including the true physical scalar versus specified-cell read and fixed/ideal/floor creditors. The new local reduction by itself does not pay them.
4. Connect complete U3/U4 full/selected/inherited q/tag count sources, genuine root norm 7/2, six rejection classes, first-forbidden non-edge owners, collision capacities and signed surplus payments to this request history.
5. Finish base/fixed/switched/seed and positive Buchstab/retention payments, manuscript-local PP/same-rho, native-history and integral–Theta–count correspondence, and one causally consistent 430+11 nested refinement.
6. Only after complete source closure, perform targeted compilation, kernel replay, transitive axiom audit and finite-certificate validation.

Next mathematical move: apply the exact three-channel overflow witness to identify *which original candidate inequalities* remain unproved at a genuine predecessor cell, then prove those inequalities using the existing same-Q source/floor dictionary. Avoid another conditional global summation interface.

**FULL H34 MANUSCRIPT-INTERNAL PROOF IS NOT CLOSED.**
