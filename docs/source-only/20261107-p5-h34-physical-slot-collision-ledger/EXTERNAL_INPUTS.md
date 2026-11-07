# P5.6/h34 — EXTERNAL_INPUTS (record only)

New source commit: `379a419c29656507f2800be1fe418b6178a29797`.
Previous branch HEAD: `7919973d0d949aa03345040e863840278176850f`.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex` blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Lean: `leanprover/lean4:v4.33.0-rc1`.
Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## Newly required genuinely external analytic inputs

**NONE.** No new PNT, Mertens, BV, Rosser, density,
Buchstab, or analytic theorem proof is written, and no new axiom,
h34-equivalent premise, or target-licensed count assumption is added.

## Exact reused interfaces and consumers

- Pinned Mathlib `Finset.image`, `Finset.mem_image`,
  `Finset.filter`, `Finset.mem_filter`, `Finset.sum_ite_eq`,
  `Finset.sum_comm`, `Finset.sum_filter`,
  `Finset.add_sum_erase`, `Finset.sum_add_distrib`,
  `Classical.choose/spec`, `Prod.mk.injEq`, `Finset.card`.
  These are used in
  `physical_slot_representative_spec`,
  `physical_slot_has_actual_source_and_frontier`,
  `physical_slot_weighted_partition`,
  `physical_slot_representatives_and_collisions` and
  `physical_slot_capacity_card`. Premises: actual finite
  observed tagged-key image and its nonempty physical fibres;
  no sieve density or mass/Theta inequality follows from them.
- Existing manuscript-local SOURCE-ONLY/UNCOMPILED candidate
  `key_receipt_has_actual_rank_two_frontier` in
  `Part5OriginalH430TaggedRankTwoFibreCapacity` is invoked in
  `physical_slot_has_actual_source_and_frontier`.
  Its premises come from the real observed-key image and retained
  original receiver membership. Its conclusion is a genuine
  frontier state under the receiver's actual per-tag/root Q.
- Existing manuscript-local SOURCE-ONLY/UNCOMPILED candidate
  `actual_frontier_state_determined_by_prefix` in
  `Part5OriginalH430RankTwoFrontierConverse` is used in
  `equal_physical_slot_same_frontier_state`. Premises: both
  actual rank-two frontier memberships, identical physical Q,
  identical ordered [ell,p] prefix and same N/cap/z0/lower
  history carrier. This is equality of state values, NOT of list
  occurrence positions or payment rights.
- Existing manuscript-local SOURCE-ONLY/UNCOMPILED candidates
  `retained_source_representative_and_surplus` and
  `retained_source_capacity_card` in
  `Part5OriginalH430TaggedRankTwoFibreCapacity` are composed in
  `retained_physical_slot_signed_ledger` and
  `retained_physical_slot_capacity_card` respectively.
  Premises: actual original tagged q Finsets, chosen genuine
  retained prime factor, physical root Q, and finite fibres.
  No new externally assumed count source is introduced.

## Still manuscript-internal

Actual full/selected/inherited LIST POSITION multiplicities and
owner payment capacity, original count source/root weight matching,
rejected/non-event lanes and correctly oriented Euler exits,
request-level all-action CLOSED-CELL, feedback/base/seed/floor
integrals/Theta/count, manuscript PP/same-rho and common nested
430+11 refinement. No part is relabelled external.

All new proof bodies remain SOURCE ONLY / UNCOMPILED;
numerical finite guards UNEVALUATED. No CI dispatched.
