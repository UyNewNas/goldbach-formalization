# P5.6 / h34 — root-matched versus wrong-root invisible rejection keys

Date: 2026-11-18. Baseline branch HEAD: `64fcf6bf1cc5841445ab44526868614eefd66732`.
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`. Scope: manuscript-INTERNAL source-only increment.
Pinned manuscript: `ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## Concrete mathematical correction

The predecessor's `invisibleActualQExitKeys` compares all original q/tag failure keys with one fixed generated root. Its invisible set includes *every* original physical key with a different Q or root prime. These are not failures to generate a rejection action for that root; no such owner should be expected there.

`Part5OriginalH430RootMatchedInvisibleKeys.lean` makes this distinction formal. Theorems:
- `visible_key_matches_root`: any literal second-edge-visible key matches BOTH physical Q and original root prime.
- `source_mismatch_forces_invisible` and `mismatched_invisible_eq_original_filter`: the wrong-root invisible keys equal the original q/tag failure-key set filtered by physical Q or p mismatch; they do not depend on the 430-generation search.
- `matched_invisible_eq_original_matched_minus_visible`: genuinely same-root unrepresented keys are exactly the source's root-matched keys minus true full-430 edge-visible keys.
- `invisible_keys_matched_mismatched_partition`, `matched_mismatched_disjoint` and `invisible_signed_exit_matched_mismatched`: exact disjoint and signed correction partition, retaining the original Euler suffix.
- `matched_key_true_event_but_no_literal_edge`: under the unchanged cap hypothesis, a same-root invisible key has an actual historicalRejectedEvents singleton and a genuine signed Euler remainder but no literal Fin second-edge position at any g < 430.
- `matchedInvisibleReceipts` / `matched_receipt_true_root_no_literal_edge`: receipt-level physical root matching without merging distinct original q/tag entries.

This is a REAL source classification and prevents erroneously charging different-root historical events to one generated root. It does not assert that the same-root invisible subset is nonempty, nor create a non-edge CLOSED-CELL request action.

## Remaining manuscript-internal work

1. Establish whether genuine same-root invisible historicalRejectedEvents map to actual generated rejection/first-forbidden request actions; note the current resolver Choice has only retention, Buchstab and bank, so a new rejection lane cannot be pretended to be an existing Choice.
2. Prove the full original selected/inherited U3/U4 owner, root norm 7/2, q/tag multiplicity and six rejection payments; quantify the original signed receipt gap instead of treating each key as multiple history occurrences.
3. Finish all-action CLOSED-CELL, Buchstab/retention positive source, base/seed/floor and original PP/same-rho, native-history, integral–Theta–count, and one common 430+11 causal realization.
4. Compile the fixed import closure, replay the kernel and audit transitive axioms and still-unevaluated finite certificates.

## Verification and concurrency

Source-only / UNCOMPILED / UNEVALUATED; no kernel replay or transitive axiom audit. Local `lean`, `lake`, `elan` are unavailable, and native git cannot resolve github.com; existing Actions do not compile this new source-only module. No fixed dependencies, CI settings, P1.4/P3.6 or other branches changed. GitHub branch preflight confirmed `64fcf6bf1cc5841445ab44526868614eefd66732` with push permission and no active workflow on that HEAD.
