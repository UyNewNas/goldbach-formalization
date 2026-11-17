# P5.6 → h34 exact final outer integer quotient: external boundary

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean: `v4.33.0-rc1`; pinned Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**New genuinely external analytic inputs: NONE.**

Mathlib `Int.emod_add_ediv`, `Int.emod_nonneg`, finite sums, integer/real coercions, nonnegative products and real positive-part arithmetic are reused as foundational library theorems, not reimplemented.

## Reused manuscript-local interfaces and call sites

- `P2Selected430LiteralActionData.candidate`, `rows`, `slotOfAction`: original integer row, point numerator and outer divisor in `originalPointNumerator`, `originalOuterRemainder`, `literal_candidate_plus_outer_floor_eq_real`.
- `Part5OriginalH430FixedReadDictionary.feedbackNumerator`, `rawFixedValue_eq`, `literal_divisor_pos`, `baseValue`, `fixedValue`, `feedbackValue`: exact signed integer/real outer-quotient identity in `literal_candidate_plus_outer_floor_eq_real`. No reinterpretation of specified-cell as scalar owner.
- `Part5OriginalH430ActualFeedbackQuotientRemainders.ideal_feedback_exact`, `feedbackRoundingLoss_nonneg`: existing exact *per-product* feedback floor, combined once with the NEW outer quotient floor in `prefloor_eq_literal_plus_both_floors`.
- `Part5OriginalH430LiteralBankQ80PhysicalExcess.literalChosenBankQ80`, `bankLiteralQ80IdealExcess` and `Part5OriginalH430TrueBankFeedbackFloorCredit.preFloorAtom`, `floorAtom`, `bankPreFloorIdealExcess`: exact signed difference, clipped positive-part and real selected Fin sum in `bank_literal_plus_complete_credit_eq_prefloor`.
- `Part5OriginalH430SelectedBankGlobalFloorBaseLedger.occurrenceTheta` and `Part5OriginalH430RequestedLevelBankSupply.selectedLevel` / `levelMark`, `Part5OriginalH430RequestedMember.rootHistory_support`: true same-Q Theta positivity and selected repeated occurrence weighting.
- `Part5OriginalH430LiteralBankQ80PhysicalExcess.frozen_root_le_seed_buchstab_literal_q80_applied`: unchanged root consumer upgraded to full selected clipped integer floor credit in `frozen_root_le_prefloor_with_complete_credit`.

## Still manuscript-internal, not outsourced

Actual base/seed/CLOSED-CELL induction, real pre-floor positive dynamic/anchor payment, Buchstab prime source, complete original U3/U4 count-source and filtering, root norm7/2, native history, PP/same-rho and common 430+11 causal refinement remain open. No conditional h34 conclusion is replaced with an external lemma, new axiom or free smallness assumption. Exact compiler and kernel verification remain pending.
