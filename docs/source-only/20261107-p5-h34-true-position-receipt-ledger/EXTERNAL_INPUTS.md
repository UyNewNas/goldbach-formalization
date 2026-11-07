# P5.6/h34 — external analytic input ledger (true position receipt packet)

Math source: `06f16cfc3664818aace3615e27224b701a532fee`.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex`, blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Pinned Lean `v4.33.0-rc1` / Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## Newly required external analytic results: NONE

No new PNT, Mertens, BV, Buchstab asymptotic, sieve distribution,
Rosser asymptotic, or any external analytic proof was implemented.
No custom axiom or target-equivalent proof hypothesis was introduced.

## Actual dependencies and call locations

- Manuscript-INTERNAL `fixedQSlotPositionMap` and
  `fixed_q_slot_position_injective` in
  `Part5OriginalH430FixedQSlotInjection.lean`: called at
  `originalWeightAtActualPosition`,
  `actual_position_preimage_subsingleton`,
  `actual_position_weight_zero_outside_slots`.
  Per fixed physical Q, each observed physical slot receives an actual
  `Fin` position of the original rank-two **LIST**. Prior source
  is uncompiled and thus not externally certified.
- Manuscript-INTERNAL `actual_full_prefix_keeps_positions` in
  `Part5OriginalH430FixedQPositionFilterLedger.lean`: called at
  `actual_prefix_keeps_position_rep_weights`. It relies on the
  preexisting `mem_firstExitDepthFrontier_ordinaryRosser_admissible_of_pos`
  in `ImbalancedChen/FirstExitFrontierAdmission.lean` for the *same*
  `ordinaryRosserRetainedPolicy lower Q` used by the recursion. This is
  the original finite historical admission fact, NOT an analytic
  Rosser asymptotic and NOT a full count-filter equivalence.
- Manuscript-INTERNAL `retained_physical_slot_signed_ledger` in
  `Part5OriginalH430PhysicalSlotCollisionLedger.lean`: called by
  `retained_receipts_actual_position_signed_ledger`. It retains
  all original tag/p/q fibres, same-key surplus and cross-tag
  collisions; all these upstream candidates are UNCOMPILED.
- Pinned Mathlib `Finset.sum_comm`, `Finset.sum_congr`,
  `Finset.sum_filter`, `Finset.mem_image`,
  `Finset.sum_eq_zero` and finite subtype/Fin reindexing.
  Consumed by `actual_position_rep_weight_sum`,
  `observed_slot_rep_weight_by_Q` and the final signed ledger.
  No additional analytic preconditions were supplied.

## STILL INTERNAL, NOT OUTSOURCED

Actual full/selected/inherited count filters and owner weights,
original q/count-root mass, phase/threshold/z0/same-rho matching,
signed Euler and exceptional-lane payments, all-action CLOSED-CELL
induction, true seed/base/floor, outer integral—Theta—count,
native-history mass and ONE common 430+11 causal refinement.

No claim of Lean compilation, kernel replay, transitive axiom audit or
finite table certification. All inherited finite checks: UNEVALUATED.
