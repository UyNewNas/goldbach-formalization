# P5.6 / h34 — actual sequential tagged-receipt source debt

Date: 2026-11-12 (Asia/Shanghai).
Repository: UyNewNas/goldbach-formalization.
Dedicated branch: `chatgpt/p5-h34-actual-nexttable-signed-source-residual-20261109`.
Verified predecessor: `565aff5aa40be36ea037ae799abaf64c2c6f0bd0`.
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes at `ba6ec11d800eccc54406490631895e174de85766`.
SOURCE_ONLY / PARTIAL_SOURCE_INCREMENT / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.

## Why this is not the previous sequential SLOT ledger again

The previous `Part5OriginalH430SequentialSlotErasure` tracks one natural-number charge for each physical `(Q,p,ell)` slot that disappears between two historical filters. But one physical slot may represent **multiple original U3/U4 tagged `(p,q)` receipts**; in particular the U4 overlap may carry two tags, and several q values can collapse to one slot. A paid slot cardinality is therefore not a paid original receipt multiplicity.

This packet uses the existing actual `originalReceiptsAtPhysicalSlot` and `observedReceiptQs`, at each actual physical Q. It attaches the complete signed sum of original tagged q receipts to each `SlotAtQ`, not just the representative and not an invented history mass. All weights are functions `TaggedReceiver → ℝ`, so the proof is valid for signed weights and does **not** pay an absolute value or infer a final coefficient.

## Concrete new Lean declarations

Module `Part5OriginalH430SequentialTaggedReceiptDebt.lean`:
- Definitions: `actualSlotTaggedWeight`, `actualErasedTaggedReceiptWeight`, `actualSecondStageTaggedReceiptWeight`.
- Theorems: `fixed_q_sequential_tagged_erasure_exact`,
  `fixed_q_sequential_tagged_conservation`,
  `actual_sequential_tagged_erasure_exact`,
  `actual_slot_unit_weight_is_receipt_count`,
  `actual_full_prefix_tagged_erasure_zero`,
  `actual_after_full_prefix_tagged_erasure_exact`.

For actual first/second Q-dependent tests, the new source writes the original tagged *receipt-weighted* deletion as

[
D_{\rm tagged}(A\wedge B;w)=D_{\rm tagged}(A;w)+D_{\rm tagged}(B\mid A;w).
]

Here the incremental term sums **every original tagged `(p,q)` receipt** attached to slots which passed A but failed B. It does not replace each slot fibre by one. At the genuine ordinary Rosser full-prefix first stage, the old actual-prefix theorem makes the first deletion term exactly zero, leaving the stage-two tagged receipt debt. For the unit weight, the weight at a slot is its **actual receipt-fibre cardinality**, not 1.

## Proof provenance and boundary

Direct imports:
`ImbalancedChen.Part5OriginalH430SequentialSlotErasure` and
`ImbalancedChen.Part5OriginalH430U4PostfilterExactCapacity`.

Actual-source reusable facts:
`erased_slots_sequential_exact`,
`first_erased_disjoint_second_increment`,
`original_fixed_Q_receipt_filter_signed`, and
`actual_full_prefix_erases_no_observed_slots`.
Those are manuscript-internal candidates and have NOT become independent verified facts here.

The entire generated-source-only import closure has NOT been staged or compiled. The environment checked in this run did not contain Lean/Lake/Elan; native `git ls-remote` failed with `Could not resolve host: github.com`. The GitHub connector permitted a remote source-only object write, but **does not provide a substitute Lean kernel**. No Lean/Lake build, kernel replay, transitive-axiom audit, external theorem replay, or finite430 certificate validation was run. Static checks found no new sorry/admit/axiom/unsafe/native proof bypass; these checks do not make any theorem COMPILED.

No new external analytic input. Fixed c/K, root norm7/2, row norm12, real alpha/same Q, both -1/4 U3/U4 tags, 430+11 reserve, manuscript commit, original toolchain and CI configurations are unchanged. Nothing in P1.4 or P3.6 was modified.

## Open manuscript-internal obligations and next action

1. Identify the actual frozen full/selected/inherited owner and its original root weight7/2 with the position predicates; prove the **actual** new stage-two tagged receipt debt is quantitatively payable. The arbitrary second-stage gate is not this missing identification.
2. Pay the six excluded q/tag lanes, U4 overlapping and repeated q collision multiplicities, and the actual signed Euler/native-history suffix; do not substitute the slot cardinality.
3. Prove the original U3/U4 upper selected-count and signed negative-quarter compatible upper budget from real causal receipts; reconcile the base/switched/seed/floor, request-level CLOSED-CELL induction and feedback error.
4. Finish PP/same-rho, outer integral—Theta—count correspondence and one common nested430+11 causal refinement.
5. Stage the frozen import closure and compile these six declarations and imports; then kernel-replay and audit transitive axioms and finite certificates.

**Complete h34 manuscript-internal proof remains OPEN.**
