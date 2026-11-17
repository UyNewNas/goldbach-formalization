# P5.6 → h34 — distinct retained U4-overlap slots at real Fin positions

Date: 2026-11-17. Status: **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**.

## Recovery and unchanged boundaries

- Verified starting branch `chatgpt/p5-h34-full-tagged-actual-fin-20261112` HEAD `001d139e667eb5cb42f1e9ca8f02de221b00db5c`; the 20261105 request-admission SHA is an original entry, not the current restart.
- Read its original REPORT/REGISTRY/EXTERNAL_INPUTS and the latest 20261112 U4 actual-Fin packet, plus full-tag pushforward, four-lane exact source, sequential tagged debt, and the prior global U4 shortfall. This is not another single-U4 witness or representative-slot six-lane bound.
- Frozen manuscript `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. No change to c/K, root norm 7/2, row norm 12, actual alpha, same-Q, original tags, or 430+11 reserve order.
- New task-owned source only: `Part5OriginalH430DistinctU4FinReceiptDebt.lean`. No edit to P1.4/P3.6, earlier packets, CI, dependencies or master.

## Candidate Lean proof bodies

1. `u4OverlapSlotsAtQ`: actual, distinct observed fixed-Q physical slots with a retained U3-tagged original U4 witness. Using a Finset of slots prevents charging a slot once per original U4 pair.
2. `u4OverlapFinAtQ`: the unique actual rank-two Fin index for each such slot, preserving the original fixed-Q injection.
3. `u4_overlap_slot_card_ge_two`: each selected slot carries both original q/tag arithmetic receipts, with possible further receipts.
4. `u4_overlap_fin_pushforward_exact`: signed full q/tag source summed over these actual selected Fin indices equals its corresponding distinct physical-slot sum.
5. `u4_overlap_fin_two_plus_extra_exact`: exact aggregate unit identity at a fixed Q: **two times the number of distinct occupied slots plus the sum of all extra original receipts**. No pairwise disjointness of U4 pairs is asserted.
6. `u4_overlap_fin_signed_quarter_exact` and `all_actual_q_u4_overlap_signed_quarter_exact`: carry the exact negative-quarter contribution across all actually observed Q separately. This is arithmetic source charge, not the root 7/2 or signed Euler payment.

The new statements do not identify the frozen selected/inherited causal owner. An original U4 pair may share a physical slot with another U4 pair; its extra q/tag receipts remain charged within that slot's excess. Other observed slots and the four outside-source rejections are not covered by this restricted double-overlap sum.

## Unclosed manuscript-internal obligations

- Bind the actual full/selected/inherited owner to each complete q/tag receipt, and quantitatively pay the two-tag baseline and the extra receipt sum with native signed Euler mass/root norm 7/2.
- Pay four outside-source lanes, original selected/erased residuals, row errors, and prove the correct signed selected-count inequality.
- Complete request-level Buchstab/retention, all-action CLOSED-CELL induction, base/switched/seed/floor, manuscript PP/same-rho, outer Theta/integral/count and a single nested 430+11 causal refinement.
- Install pinned source-only transitive dependency closure. The current container has no lean/lake/elan on PATH, and native git cannot resolve github.com; therefore the new candidate source is NOT COMPILED. No kernel replay, transitive axiom audit, or finite certificate check has run; finite certification remains UNEVALUATED.

Next: verify and compile this new true-Fin aggregate against pinned imports when the closure is available; then identify true selected/inherited causal owner and prove a signed-payment inequality with the exact two-tag plus extra q/tag arithmetic costs. Full manuscript-internal h34 remains OPEN.
