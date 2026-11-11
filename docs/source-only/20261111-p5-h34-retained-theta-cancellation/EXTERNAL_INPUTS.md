# P5.6 / h34 — retained physical Theta cancellation: external-input register

Fixed manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766 (paper/source/manuscript-body.tex).
Fixed Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

No new external PNT, Mertens, BV, prime distribution or other analytic theorem has been implemented or assumed. No new custom axiom, sorry/admit, proof-equivalent license, unsafe or native proof escape was introduced. No transitive axiom audit has been run.

Existing Mathlib elementary finite-sum and ordered-real facts:
- Finset.sum_union, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_le_sum and abs-multiplication laws, used in actual_theta_correction_retained_nonretained, actual_nonretained_theta_correction_lower and actual_nonretained_payment_le_all_action_payment.
- linarith / ring and positivity on the real field, used to rewrite and compare the exact physical budgets. These are standard fixed-version library calls; no novel external arithmetic input.

Existing manuscript-internal interfaces reused in the new module (NOT outsourced):
- actual_theta_correction_all_actions, from Part5OriginalH430ActualNextTableThetaFloorBridge, applies the real resolver's retained/Buchstab/106-bank partition at generation g+1.
- bank_level_sum_eq_original_106 and buchstab_bank_disjoint, from Part5OriginalH430ActualRequestAllActionPartition, preserve actual Fin positions and 106-bank multiplicity.
- actual_retention_child_exact, from Part5OriginalH430ActualRequestNonbankQuantitative, identifies the REAL retained physical Theta child edge, including specified-cell read.
- actual_theta_absolute_payment_all_actions, from Part5OriginalH430ActualThetaAbsolutePayment, provides the old full absolute payment partition.
- actual_source_debt_theta_floor_upper, from Part5OriginalH430ActualNextTableThetaFloorBridge, retains its own original geometric and previous-cell CLOSED-CELL premises, and has the original Q80 floor sign.
- actualRetainedSelectedPhysicalRead and actualSelectedOldRead retain their existing original definitions; no replacement owner/source/count relation.

Remaining INTERNAL obligations are an effective selected nonretention Theta bound derived from true U3/U4 arithmetic counts, predecessor CLOSED-CELL induction, bank/Buchstab genuine source gaps, full/selected/inherited owner/root counts, six rejection and Euler payments, manuscript-local PP/same-rho, native-history, Theta/count and single common430+11 causal refinement.

Validation: SOURCE_ONLY / UNCOMPILED / KERNEL_REPLAY_NOT_RUN / TRANSITIVE_AXIOMS_NOT_AUDITED / FINITE_CERTIFICATION_UNEVALUATED.
