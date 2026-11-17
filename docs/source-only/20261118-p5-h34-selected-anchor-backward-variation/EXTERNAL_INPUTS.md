# P5.6 / h34 — selected Q80 anchor backward variation: external boundary

Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766.
Pinned toolchain: Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
Prior branch HEAD: 47f47e49d0b8679cbc7b029ef6208f78e61afad5.

**New genuinely external number-theory or analytic inputs: NONE.**

## Existing foundations reused without new axioms

- Mathlib finite range sums, sum distributivity, Finset.sum_range_succ, max/positive-part inequalities, arithmetic and nonnegative scalar multiplication in clipped_gap_le_seed_plus_drops and selected_anchor_payment_le_seed_plus_backward_variation.
- Original Q80 table recurrence P5OriginalFeedbackTableKernels.iterate and floorValue: used at precisely iterations k and k+1 in actualUpperCellDrop; not rebuilt or replaced.
- Original 106-bank fixed endpoint selectors w1Cell, w2Cell, W1Anchor, originalW2At: used in actionBackwardDrop and selected_action_anchor_le_seed_plus_variation; the W2 4/5, 1/5 weights are unchanged.
- Existing manuscript-local Part5OriginalH430SelectedPositiveAnchorPayment.actionPositiveAnchorAllowance, occurrenceScale_nonneg, bankFixedSlackMass_le_selectedPositiveAnchorPayment, and Part5OriginalH430RequestedLevelBankSupply.selectedLevel: used in both the actionwise and genuine selected Fin sum comparisons.
- Manuscript-local Part5OriginalH430ClosedCellPositivePrefloor.bank_prefloor_le_closed_cell_positive and Part5OriginalH430ClosedCellIdealSplit.bank_closed_cell_positive_sandwich: used in the new root consumer, whose entire predecessor CLOSED-CELL premise remains explicit and **unproved**.
- Manuscript-local Part5OriginalH430ExactOuterQ80FloorCredit.frozen_root_le_prefloor_with_complete_credit and bankCompleteFloorCredit: use BOTH actual integer Q80 floor losses, clipped only by the same pre-floor positive excess. No second charging of those losses.

## Still manuscript-internal, not outsourced

- Prove the original Q80 upper-table downward variation budget quantitatively, along with the literal zero-iterate anchor mismatch. The finite nonnegative-step decomposition is not a smallness estimate.
- Complete original base/fixed/switched/seed/floor CLOSED-CELL induction and PP/same-rho instantiation; pay true Buchstab and terminal zero-generation seed.
- Bind full original U3/U4 count owners, selected/inherited/full filters, root weight 7/2, q/tag multiplicities and rejected lanes.
- Resolve signed Euler and native-history mass, outer integral–Theta–count transport and the same 430+11 causal refinement under the fixed c/K.
- Stage the original fixed dependency closure, compile and kernel replay this module and dependencies, audit transitive axioms and replay finite guards.

No target-equivalent assumption, new analytic oracle, replacement rho, widened budget, additional prime theorem or custom axiom has been introduced. Mathlib results are reused; they are not claims that the h34 counting theorem is proved.
