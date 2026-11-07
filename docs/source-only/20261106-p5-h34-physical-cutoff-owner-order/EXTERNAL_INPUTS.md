# P5.6 / h34 physical-cutoff order — external inputs (record only)

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Existing Lean toolchain and Mathlib lock remain unchanged. No PNT/Mertens/BV, PP, same-rho or other external analytic theorem has been implemented or strengthened.

## Imported library operations actually used
- Integer / real cast monotonicity (`exact_mod_cast`) for comparison of the same prime with a real physical cutoff in `root_le_bad_iff_quotient_rough_at_root`, `rejected_frozen_quotient_first_of_physical_le_root`.
- `min_eq_left`, `min_eq_right`, `Nat.lt_of_not_ge` and `Nat.not_lt_of_ge`, to preserve equality-case ownership and strict-order direction.
- `Finset.sum_add_distrib`, `Finset.sum_congr`, classical `by_cases`, to partition signed real mass without positivity assumptions.
These are invoked through existing pinned imports, not new external mathematical assumptions.

## Existing manuscript-local providers reused, NOT outsourced
- `rough_iff_below_first_bad`, `bad_implies_not_rough`, `frozen_only_tagged_first_bad`, `rejected_frozen_tagged_first_bad`.
- `frozen_only_additive_prefix`, `rejected_frozen_additive_prefix`, the real `frozenPrimeCutoff`, `frozenOnly` and `rejectedFrozen`.
- `jointFirstPrime` and original `TaggedReceiver` with the same (U3/U4,p,q,P) semantics.

## Not external / still open
Retained-prefix and first-excluded policy identification, selected/full/inherited filtering, causal cap/parity/sign, every original receipt count, rejection-mass inequalities, manuscript-local PP/same-rho, closed-cell all-action estimate, feedback integral comparison, native-history and common 430+11 causal refinement. No proof is replaced by a custom axiom or an equivalent count-license parameter.
