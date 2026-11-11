# P5.6 / h34 — original Theta absolute payment: external-input register

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Original source `paper/source/manuscript-body.tex`. Toolchain Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

No new genuinely external prime-distribution/PNT/Mertens/BV input was assumed or implemented, and no new axiom/sorry/admit/unsafe/native proof escape was added.

- Mathlib finite real sums, `Finset.sum_le_sum`, `abs_le`, `abs_mul`, `Finset.sum_filter`, `ring`, `linarith` and ordinary absolute-value order were invoked in the candidate statements `actual_theta_correction_abs_le_payment`, `actual_theta_absolute_payment_all_actions` and `actual_source_debt_theta_absolute_payment_upper`. Version fixed above.
- Original manuscript-internal `actualThetaReadCorrection` and its exact physical-Q / physical-parent-product definition are consumed at `actual_theta_correction_abs_le_payment`.
- Original manuscript-internal `unresolved_level_value_zero` and `resolved_level_sum_all_actions` are consumed at `actual_theta_absolute_payment_all_actions`. They are not reclassified as external results.
- Original manuscript-internal `actual_source_debt_theta_floor_upper` is consumed at `actual_source_debt_theta_absolute_payment_upper`; all its original prior-cell geometric and CLOSED-CELL induction preconditions are kept literally.

Still internally open: real original selected/full/inherited U3/U4 count owner, root weights, physical Theta correction quantitative control, base/switched/seed/floor, real bank/Buchstab source residual payments, rejection classes, PP/same-rho, native-history, Theta/count and 430+11 causal refinement.

Status: SOURCE_ONLY / UNCOMPILED / KERNEL_REPLAY_NOT_RUN / TRANSITIVE_AXIOM_AUDIT_NOT_RUN / FINITE_CERTIFICATION_UNEVALUATED.
