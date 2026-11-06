# P5.6 h34 — external input ledger for read/integral defect bridge

Base branch head `f8c3a3babd6810fdfbf73c30aedae91108a5abf4`. Pinned manuscript is `ba6ec11d800eccc54406490631895e174de85766` with the existing h34 proof mapping; neither parameters nor goals have been changed.

No new external number-theory theorem, distribution bound, custom axiom, or analytic proof is introduced here.

## Exact reused interfaces and call sites

* Mathlib finite `Finset.sum_add_distrib`, `Finset.sum_sub_distrib`, finite sum congruence, ordered real absolute-value inequalities and ring arithmetic: `buchstab_defect_ideal_split`, `buchstab_defect_le_integral_residual`. They are standard library inputs, not redeclared assumptions.
* Existing manuscript-local `Part5OriginalH430RequestedSignedStep.buchstab_abs_le_applied`, `buchstab_applied_le_rowError`, its `buchstabIdeal`/`buchstabActual` definitions: `buchstab_defect_le_integral_residual`. The latter theorem uses the previously established row certificate through the old `requested_buchstab_applied_le` and immutable430 arithmetic-row supply. Its original analytic provenance and transitive proof dependencies have NOT been newly audited.
* Existing manuscript-local `Part5OriginalH430RequestedNonbankLevel.uniform_level_buchstab_supply` with exact pre-N quantifiers, true physical root assumptions, both polarities, and the original row bound: `uniform_actual_one_generation_integral_residual_upper`. It supplies only the error on the strict-prime-to-integral term, not the new integer suffix residual.
* Existing manuscript-local `Part5OriginalH430ActualReadEdgeDefect.level_defect_nonretained` and `bank_defect_sum_le`: `actual_one_generation_integral_residual_upper`. The bank base/fixed/feedback candidate upper is left intact; it is not presented as paid.

## Manuscript-local obligations (not reclassified external)

The true integer `buchstabValue` suffix against the ideal integral, correct directional fixed/switched/seed/floor budget, original U3/U4 selected count and history owner, original PP/same-rho consumer, outer Theta and 430+11 common refinement remain UNPROVED in this packet.

Status: SOURCE ONLY; UNCOMPILED; NO KERNEL REPLAY; NO AXIOM AUDIT; FINITE GUARDS UNEVALUATED.
