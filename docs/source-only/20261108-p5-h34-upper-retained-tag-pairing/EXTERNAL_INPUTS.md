# P5.6 / h34 — external inputs for actual upper-retained tag pairing

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`; `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Mathematics source commit: `65b38afe5c8e8f2e452b1f2e0f01bb7a115a702c`.
Original toolchain: Lean v4.33.0-rc1 and Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**NEW EXTERNAL ANALYTIC INPUTS: NONE.**

The new module imports `Part5OriginalH430UpperOverlapCommonQ`. It reuses the existing original U3/U4 selected (p,q) source, real frozen physical Q, actual `selectedOriginalRootStage`, `hasRetainedOriginalSecond`, `retainedReceipts`, and actual `physicalRankTwoSlot` / `chosenRankTwoKey`.

Internal dependencies and actual call sites:
- `original_u4_overlap_root_stage_iff` and `original_u4_overlap_has_retained_iff`: `original_u4_overlap_full_retention_gate_iff`.
- `original_u4_pair_has_two_tags` and literal `retainedReceipts` definition: `original_u4_retained_inl_iff_inr`.
- `original_u4_both_retained_all_same_slot` and `actual_chosen_slot_map_not_injective_of_overlap`: `original_u4_one_retained_forces_slot_collision`.
- `original_u3_pairs_signed_partition` and native `Finset.sum_disjSum`, `Finset.sum_filter`, `Finset.sum_add_distrib`: `original_retained_u34_tagged_overlap_weight`.

Existing Mathlib finite-set and additive-monoid identities are used with their inherited pinned version, not restated as outside analytic inputs. No PNT/Mertens/BV proof, new postulate, custom axiom, signed Euler payment, upper-history full/selected/inherited owner, or PP/same-rho premise is implemented or asserted.

**Still MANUSCRIPT-INTERNAL:** actual upper H430 selected/full/inherited history owner and finite list position multiplicity; two-tag capacity and cross-q collisions; original root weights and six rejection lanes; signed Euler/first-excluded payment; request all-action CLOSED-CELL, feedback/seed/floor, PP/same-rho, native-history mass and common 430+11 refinement. None has been moved to the external-input list.

Verification: SOURCE_ONLY, elaboration NOT RUN, compilation NOT RUN, kernel replay NOT RUN, transitive axiom audit NOT RUN, numerical430 UNEVALUATED.
