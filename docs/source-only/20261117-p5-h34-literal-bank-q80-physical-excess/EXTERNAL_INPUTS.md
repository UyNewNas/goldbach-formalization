# P5.6 → h34 genuinely external inputs: literal selected Q80 physical packet

Pinned manuscript: `ba6ec11d800eccc54406490631895e174de85766`.
Pinned toolchain: Lean `v4.33.0-rc1`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

No new external number-theoretic theorem or custom axiom is introduced or proved here.

## Imported existing interfaces and exact consumer positions

- Existing manuscript-local `Part5OriginalH430RequestedReads.selected_value` is called in `selected_bank_true_read_eq_literal_q80`: genuine selected `Selected g r i (.bank k)` and read from `iterate (g+1)`.
- Existing `Part5OriginalH430RequestedReads.selected_bank_candidate_upper` is called in `selected_literal_q80_le_real_candidate`. Its conclusion compares the true selected read to `baseValue + fixedValue + feedbackValue` on `iterate g` without replacing one request mode by another.
- Existing manuscript-local `Part5OriginalH430RequestedMember.rootHistory_support`, `parentWindow_logs`, and `thetaAtom_nonneg` are consumed in `literal_q80_excess_le_real_candidate_excess` under `4 ≤ N`, `0 ≤ tau ≤ 1/12`, `1/(n+1) ≤ 11/384`, root prime/coprimality and band hypotheses, and the original Fin occurrence. These are not new hypotheses on arbitrary parents.
- Existing `Part5OriginalH430DirectPhysicalBankPayment.frozen_root_le_seed_buchstab_ideal_excess_applied` and `uniform_frozen_root_le_partly_paid_physical_source` are used exactly in the final two root theorems. The bank applied-error uniform threshold is inherited, not duplicated.
- Mathlib arithmetic, `Finset.sum_congr`, positive-part monotonicity, `mul_le_mul_of_nonneg_left` and real order operations are reused, not reimplemented. No `PNT` / `Mertens` / `BV` theorem proof is expanded.

## Manuscript-internal, not outsourced

The physical Q80 positive surplus's actual numerical payment, original base/fixed/feedback floor, Buchstab, zero-generation seed, full original U3/U4 count owner/7/2 normalization, all filters and rejections, native-history, PP/same-rho and common 430+11 integral/Theta/count refinement all remain internal obligations. None is discharged by declaring an external count licence.

No actual build or transitive-axiom audit has been performed. Inputs are **referenced**, not newly verified.
