# P5.6 / h34 external inputs — physical weighted nonretention bridge

Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766, paper/source/manuscript-body.tex.
Fixed Lean v4.33.0-rc1 and Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

No new PNT, Mertens, BV, distribution or other analytic theorem, no new custom axiom and no target-equivalent count premise. New external inputs: NONE.

Existing Mathlib real/finite-sum facts reused: `Finset.abs_sum_le_sum_abs`, `Finset.sum_congr`, `abs_mul`, `abs_add_le`, `add_le_add`, `linarith` and `ring`. Used by the absolute-correction bound, source-defect inequalities and exact rearrangements.

Existing manuscript-INTERNAL interfaces used unchanged: `actual_weighted_new_table_exact`, `actual_new_table_eq_retained_physical_plus_source_gaps`, `actual_theta_correction_retained_nonretained`, `actual_retained_theta_cancels_to_child`, `actual_selected_same_q_gap_le_error`; original `levelReadMass`, `levelChildMass`, `retainedLevelValue`, `actualSelectedSameQIdealRead`.

Still manuscript-INTERNAL and OPEN: actual U3/U4 count owner and nonretention Theta/source-gap bounds, previous CLOSED-CELL induction, base/seed/floor, root weights, filters and rejection payments, PP/same-rho, native-history, outer Theta/count, common430+11 refinement.

SOURCE_ONLY; no Lean elaboration/compile, kernel replay, transitive axiom audit or numerical430 executed. All candidates UNCOMPILED and finite certificates UNEVALUATED.
