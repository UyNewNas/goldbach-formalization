# h34 external inputs — actual predecessor absolute stability

2026-11-09; source commit `a3a013e504b85a4c32f41f8b317df8c6543051f6`.
Pinned frozen manuscript `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**No new genuinely external analytic inputs or axioms.**

## Existing named dependencies and call sites

- Elementary Mathlib finite nonnegative sums
  (`Finset.sum_nonneg`), an indexed term bounded by a nonnegative
  finite sum (`Finset.single_le_sum`), distributivity
  (`Finset.sum_sub_distrib`), and ordered multiplication:
  `predecessor_abs_mass_nonneg`, `predecessor_abs_le_mass`,
  `actual_selected_row_difference_l1`.
- Manuscript-local, currently uncompiled
  `Part5OriginalH430ActualSelectedFeedbackOperator.actual_selected_old_read_le_row_budget`
  and `nonnegative_row_old_input_bound`: called in
  `actual_selected_old_read_l1_envelope` and
  `actual_selected_row_difference_l1`, respectively.
- Manuscript-local, currently uncompiled
  `Part5OriginalH430ActualSelectedRowBudget.uniform_actual_selected_error_row_budget`:
  called in `uniform_actual_predecessor_abs_stability`. Its upstream
  original 106 bank and Buchstab analytic coefficient interfaces remain
  as previously recorded; they are **reused, not proved anew**.

## Still manuscript-internal

Actual old table vs fixed/switch/base/seed and same-Q feedback-integral
vector; its growth estimate across 430 levels; original U3/U4 count
identity with root weights, full/selected/inherited filters and six
rejection lanes; signed Euler payments; native-history and 430+11
nested common refinement; manuscript-local PP/same-rho instances.
None has been relabelled as external and no theorem-equivalent
premise or alternative axiom was inserted.

All source declarations remain **UNCOMPILED/UNEVALUATED**.
