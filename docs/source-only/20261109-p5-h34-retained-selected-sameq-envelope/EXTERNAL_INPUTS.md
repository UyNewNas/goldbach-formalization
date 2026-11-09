# External-input boundary — actual retained/selected same-Q envelope

2026-11-09. Mathematical source commit: `344c843fc72c586b3918dc9817a099a29fcbded2`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, path `paper/source/manuscript-body.tex`.
Pinned toolchain: Lean `v4.33.0-rc1`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**New external analytic theorems, new axioms, or alternative external proof implementations: none.**

## Standard Mathlib results used by the new proof body

- `abs_add_le` and `abs_sub_comm`: triangle symmetry in `actual_selected_same_q_ideal_abs_envelope` and `actual_retained_selected_ideal_abs_envelope`.
- `abs_eq_zero`, `sub_eq_zero`, `le_antisymm`, `abs_nonneg`: actual joint-zero-Theta case in `actual_selected_same_q_ideal_zero_of_zero_thetas`.
- `ring`, ordered-ring addition monotonicity (`add_le_add`, `add_le_add_left`): algebraic and finite-real bound composition in the same proof bodies.

They are reused at their pinned imported versions, not re-proved.

## Exact inherited manuscript-local consumers, not newly outsourced

- `Part5OriginalH430ActualRequestNonbankQuantitative.actualRetainedRead`: true next-table retained request locations and path marks.
- `Part5OriginalH430ActualSelectedFeedbackOperator.actualSelectedOldRead`: genuine selected bank/Buchstab predecessor array read.
- `Part5OriginalH430ActualSelectedSameQIdealGap.actualSelectedSameQIdealRead` and `actual_selected_same_q_gap_le_error`: literal original same-Q cell/integral ideal and its exact absolute error.
- `Part5OriginalH430ActualPredecessorAbsStability.predecessorAbsMass`, `actual_selected_old_read_l1_envelope`, and `actual_selected_old_read_zero_of_zero_thetas`: literal finite L1 predecessor atom mass and selected-operator bound.
- `Part5OriginalH430ActualSelectedRowBudget.uniform_actual_selected_error_row_budget`: one common epsilon threshold with the actual bank row 12Theta and Buchstab row 5Theta budgets.

The upstream raw coefficient/Buchstab suppliers retain their preexisting pinned PNT/Mertens/BV/prime-profile dependencies at their actual interface versions. This packet introduces no new call to those theorems, no changed constants or thresholds, and no new assertion about their transitive axiom closure.

## Still internal and OPEN

This packet does NOT take as external inputs: original U3/U4 complete count-source identity, bank/Buchstab next-table-to-old-array residual, same-rho PP/floor/seed correspondence, actual `predecessorAbsMass` base/induction growth, root count weights, original full/selected/inherited owner, rejection payment, native-history masses, outer Theta/count or common 430+11 causal refinement. None is disguised as a new abstract assumption.

All inherited source-only assertions and these five new theorem candidates are still UNCOMPILED/UNEVALUATED. No kernel replay or axiom audit has been run.
