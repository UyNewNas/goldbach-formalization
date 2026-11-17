# P5.6/h34 — global true-Fin U4 overlap and remaining original count inputs

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned tools: Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**New external analytic theorem inputs: NONE.** No PNT/Mertens/BV or theorem-equivalent axiom is re-proved or added. Lean code invokes existing finite sum/disjoint filter algebra, nonnegative sums and real ring arithmetic from pinned Mathlib.

Reused *uncompiled manuscript-internal* source candidates (not external axioms or certified results):

- `Part5OriginalH430DistinctU4FinReceiptDebt.u4_overlap_fin_two_plus_extra_exact`: exact two original q/tag receipts plus every extra receipt at EACH distinct U4-overlap-occupied true Fin position. Used by `actual_fin_two_tags_excess_and_rest`.
- `Part5OriginalH430OriginalTagSeparatedFinSource.allObservedFinWeight`: literal observed true-Q and true-Fin total. Used by `all_observed_fin_two_tags_excess_and_rest`.
- `Part5OriginalH430FourLaneFullTaggedFin.original_source_four_lanes_all_tagged_fin` and `originalFourOutsidePositionLanes`: entire original tagged U3+U4 source and four original rejections. Used by `original_u34_count_full_overlap_balance`.
- `Part5OriginalH430TaggedArithmeticReceivers.original_U34_eq_tagged_card`: exact original tagged count, used by `original_u34_count_full_overlap_balance`.
- `originalU34SignedQuarter` definition: exact negative-quarter source sign, used by `original_negative_quarter_full_overlap_balance`.

**Still manuscript-internal and not outsourced:** full/selected/inherited owner equality; multiple q/tag receipt payment by root norm 7/2 and signed Euler history mass; four outside-source rejections; original selected-count inequality; request-level Buchstab/retention and CLOSED-CELL; base/seed/floor; same-rho/PP instances; outer Theta/count/integral; full 430+11 joint causal refinement. SOURCE_ONLY is not COMPILED or axiom audited.
