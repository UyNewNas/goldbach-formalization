# Existing external inputs only — actual U3/U4 root gate refinement

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` (blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).
Lean toolchain: `leanprover/lean4:v4.33.0-rc1`.
Mathlib: unchanged manifest revision `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**New external analytic inputs: NONE.** No PNT/Mertens/BV result is implemented or changed.

Reused local source declarations and actual new consumers:
- `Part5OriginalH430TaggedArithmeticReceivers.original_band_prime`, `originalBand` and `rawPairs`: `raw_root_prime_coprime` for each original U3/U4 root p.
- `Part5OriginalH430TaggedReceiverFibres.arithmeticPrime`: `raw_root_prime_coprime`, `raw_root_not_target` and the full root gate identification.
- `Part5OriginalH430TaggedSourceRejections.frozen_tagged_subset_raw`, `rawTagged`, `rejectedFrozen`: `frozen_only_raw`, `rejected_frozen_raw`, and the two genuine source theorems.
- `Part5OriginalH430ReceiverRootGateAccounting.rootLicensed`, `gateBlocked`, `ownCarrierOutside`, `ownPolicyPass`: `raw_root_licensed_iff`, `actual_root_gate_split`, `refinedNonEventWeight`.
- `Part5OriginalH430TrueReceiverWeightedExit.fourthNonEventWeight`, `fourthDistinctKeys`, `fourthKeyReceipt`, `original_U34_rejected_weighted_signed_exit_gap`: `refined_non_event_weight_eq`, `original_rejected_refined_signed_gap`.
- `Part5OriginalH430RealSignedExitPayment.actualRankTwoSignedExit`: `original_rejected_refined_signed_gap`; unchanged literal signed Euler correction.
- Mathlib finite set membership, disjoint unions, finite sums, `Nat.dvd_gcd`, `Nat.le_of_dvd` and elementary arithmetic: local proof bodies only.

These are existing manuscript-local arithmetic and basic library dependencies, NOT new assumptions or external analytic oracle calls. In particular, the manuscript's correct signed count ownership, actual selected/full/inherited gate filters, residual receipt payments, CLOSED-CELL induction, original base/seed/floor, PP/same-rho and common 430+11 geometry remain manuscript-internal obligations.

**Validation: SOURCE_ONLY / UNCOMPILED / UNEVALUATED.** No new axiom or claimed transitive audit.
