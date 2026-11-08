# H34 external-input boundary — actual upper retained Fin source fibre

- Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
- Manuscript body: `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Lean source commit: `c5851b9a1b74542b29ad9cc2e5972f4fa7f3b580`.
- Pinned toolchain: Lean v4.33.0-rc1; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**NEW EXTERNAL ANALYTIC INPUTS: NONE.**

Existing Mathlib finite-set, List membership, Fin index, natural-cardinality and additive-monoid identities are reused as internal finite bookkeeping. Existing analytic interfaces from the original S18/Part5 stack remain unchanged; no new PNT/Mertens/BV/Rosser external proof is constructed.

Exact manuscript-local dependencies used by the new source:
- `original_u4_retained_inl_iff_inr` and `original_u4_overlap_actual_slot_equal`: `original_u4_retained_two_tags_in_slot_fibre`.
- `retainedReceipts`, `observedRankTwoKeys`, `physicalRankTwoSlot`, `chosenRankTwoKey`: `original_u4_retained_slot_card_ge_two` and `original_u4_retained_two_tags_one_actual_fin_position`.
- `observed_slot_has_actual_rank_two_position` and `actual_rank_two_full_prefix_passes`: `original_u4_retained_two_tags_one_actual_fin_position`.
- Native `Finset.add_sum_erase`: `original_u4_retained_slot_signed_two_tags_plus_other_q`.

**Still manuscript-internal (NOT outsourced):** exact original upper H430 full/selected/inherited owner and physical z0; historical Fin payment multiplicity; original q/tag counts and root weights; six rejection lanes; signed Euler payment; all-action CLOSED-CELL; base/seed/floor; feedback-integral/Theta; PP/same-rho; native-history mass; shared 430+11 refinement.

Validation: SOURCE_ONLY; Lean elaboration NOT RUN; compile NOT RUN; kernel replay NOT RUN; transitive axiom audit NOT RUN; numerical430 UNEVALUATED; no new green claim.
