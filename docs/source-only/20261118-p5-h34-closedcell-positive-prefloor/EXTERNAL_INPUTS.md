# P5.6 → h34: external-input boundary — actual CLOSED-CELL positive pre-floor

Pinned manuscript: `ba6ec11d800eccc54406490631895e174de85766`.
Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**No new external analytic input or axiom.** This packet only uses existing local manuscript interfaces and foundational Lean/Mathlib algebra and sums. All source-only prior declarations are UNCOMPILED candidates, not pre-certified black-box theorems.

## Existing manuscript-local interfaces (to be compiled and audited)

- `Part5OriginalH430ActualFixedClosedCell.selected_fixed_reference_upper`: for each original `a : Original106Action`, from `∀ i s, s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s`, conclude `fixedValue (iterate g.val true) a ≤ fixedReference F a`. This retains W1 anchor and W2 4:1 physical reads. Consumer: `preFloorAtom_le_closedCellPreFloorAtom`, then `bank_prefloor_le_closed_cell_positive`.
- `Part5OriginalH430RequestedMember.rootHistory_support`, `parentWindow_logs`, and `thetaAtom_nonneg`: derive positive actual parent Theta from the original root history under `4 ≤ N`, `0 ≤ tau ≤ 1/12`, `1/(n+1) ≤ 11/384`, prime/coprime and physical root-band conditions. Consumer: `bank_prefloor_le_closed_cell_positive`.
- `Part5OriginalH430TrueBankFeedbackFloorCredit.bank_literal_excess_plus_floor_credit_le_prefloor`: literal winning bank Q80 positive gap + capped actual per-product feedback floor credit ≤ pre-floor positive gap. Consumer: `bank_literal_plus_credit_le_closed_cell`.
- `Part5OriginalH430SelectedBankGlobalFloorBaseLedger.selectedBankRoundingLoss`, `selectedBankRoundingEnvelope`, `selected_bank_rounding_le_envelope`, `occurrenceScale`: existing true winning Fin-position original remainder, divisor and Q80 envelope. Consumers: `bank_credit_le_original_rounding`, `bank_credit_le_original_product_envelope`, `frozen_430_credit_le_product_envelopes`.
- `Part5OriginalH430TrueBankFeedbackFloorCredit.frozen_root_le_prefloor_with_actual_feedback_credit`: true selected same-Q 430-root physical upper with capped feedback credit, zero-generation seed, Buchstab and original applied bank abs error. Consumer: `frozen_root_le_closed_cell_positive_with_credit`.

## Lean/Mathlib features

`Finset.sum_le_sum`, `max_le`, `min_le_right`, `mul_le_mul_of_nonneg_left`, `linarith`, `simpa`, `ring`-related ordered real arithmetic. Consumers are direct pointwise proofs followed by true Finset sums. The import closure and relevant transitive axioms have NOT been compiled/audited.

**Remain manuscript-internal:** predecessor CLOSED-CELL base/seed/floor induction (the new `hclosed` is its explicit *unproved* input), quantitative positive base/fixed/ideal-feedback gap, Buchstab/seed, true U3/U4 owner and 7/2 weight, full/selected/inherited/rejected filters, q/tag receipts, PP/same-rho, signed Euler/native-history, integral–Theta–count and joint 430+11 common causal refinement. Do not recategorize these as external black boxes.
