# P5.6 h34 even-N signed-exit bounds: existing external inputs

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Lean source commit: `ac8fa47005eb55f9d13d29488e1a9dd38c9d9510`.
Lean: pinned original `leanprover/lean4:v4.33.0-rc1`. Mathlib: existing manifest `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. Neither upgraded nor replayed.

**New external analytic inputs: NONE.**

The new theorem `original_fourth_key_signed_exit_interval` needs exactly the original manuscript's **even integer N** (`hEven : 2 ∣ N`), actual root cap (`hzcap : z0 ≤ cap`) and a key in the real original fourth-lane event-key set. These are arithmetic/manuscript conditions, not new PNT/Mertens/BV estimates. The manuscript's "N>2 tends to infinity through the even integers" was directly checked in its pinned source.

Reused **existing local** declarations and actual call sites:
- `ImbalancedChen.roughPrimeUniverse`, `mem_roughPrimeUniverse_prime` and `mem_roughPrimeUniverse_not_dvd`: `even_rough_euler_factor_bounds`, `historical_remaining_member`. Prime membership and exclusion of primes dividing N come from the actual original list, not assumed analytic positivity.
- `Part5OriginalH430HistoricalRejectedExitLedger.historicalRejectedEvents` and `historicalExitValue`: `historical_remaining_member`, `original_fourth_key_signed_exit_interval`. Literal recursive suffix and sign retained.
- `Part5OriginalH430RealSignedExitPayment.original_fourth_lane_key_unique_signed_event`, `actualRankTwoHistory`, `actualRankTwoSignedExit`: `original_fourth_key_signed_exit_interval`; the earlier source remains source-only and uncompiled.
- `Part5OriginalH430TaggedArithmeticReceivers.original_band_prime`, `Part5OriginalH430TaggedReceiverFibres.frozen_tagged_band`, `Part5OriginalH430TaggedFirstBadPrimeOwner.frozen_only_tagged_first_bad`, `rejected_frozen_tagged_first_bad`: `original_fourth_key_primes` and `original_fourth_key_mass_nonneg`.
- `Part5OriginalH430TrueReceiverWeightedExit.fourthDistinctKeys`, `fourthKeyReceipt`, `two_source_true_weight_sum_by_keys`: `original_fourth_key_receipt_gap_interval`, `original_fourth_total_receipt_gap_interval`, `original_unit_fourth_receiver_gap_lower`.
- Mathlib `Finset.sum_le_sum`, `List.mem_filter`, `List.prod_cons`, `mul_le_mul_of_nonneg_right`, `div_le_iff₀` and elementary arithmetic tactics; foundation/library use only.

**Manuscript-internal, NOT relabelled external:** the correct U3/U4 count/sign/owner, six non-event lane payments, q/tag duplicate weights, CLOSED-CELL and base/seed/floor, true PP/same-rho compatibility, native-history masses and causal 430+11 refinement. No target-equivalent acceptance assumption has been added.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED. No new analytic result is claimed or proven outside the manuscript scope.
