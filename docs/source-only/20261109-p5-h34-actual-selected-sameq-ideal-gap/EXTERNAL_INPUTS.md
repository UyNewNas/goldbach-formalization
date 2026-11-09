# External-input boundary — actual selected same-Q ideal gap

2026-11-09. Math source commit db2c1baa475c7c2f9c0004afad28b8989d1b4f6f.
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766.
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**No new external analytic theorem or axiom.**

Reused Mathlib finite algebra and inequalities:
- Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_comm and Finset.mul_sum in marked_row_read_gap and actual_bank_same_q_ideal_gap;
- Finset.abs_sum_le_sum_abs, abs_mul, abs_of_nonneg, mul_le_mul_of_nonneg_left in marked_row_read_gap;
- abs_add_le, add_le_add, real ordered-ring arithmetic in actual_selected_same_q_gap_le_error.

Existing *manuscript-local, still UNCOMPILED* interfaces:
- Part5OriginalH430RequestedHistory.levelMark and mark_pos; Part5OriginalH430RequestedLevelBankSupply.levelRow/levelError/selectedLevel;
- Part5OriginalH430RequestedLocalBankSupply.requestError using original cellReadIdeal;
- Part5OriginalH430ActualRequestNonbankQuantitative.actualBuchstabError / actualBuchstabRow, which use the original physical upper/physical integralRow;
- Part5OriginalH430ActualSelectedFeedbackOperator.actual_selected_old_read_split;
- Part5OriginalH430ActualSelectedRowBudget.uniform_actual_selected_error_row_budget, called once by uniform_actual_selected_same_q_gap.
The latter's pinned prime-profile and coefficient estimates remain inherited inputs at their previous exact interfaces, not proved anew here. Their transitive axiom closure has **not** been audited.

Still manuscript-INTERNAL, not moved to external inputs: correspondence with the *actual* PP/same-rho integral and original floor/seed; U3/U4 arithmetic selected-count owner, all rejection lanes, full/selected/inherited gates, root weights, original CLOSED-CELL induction, native-history, Theta/count and 430+11 common causal refinement.

Source-only/UNCOMPILED/UNEVALUATED. No input is silently upgraded to a proven theorem.
