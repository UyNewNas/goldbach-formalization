# External inputs — receiver-specific rank-one root source

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes` at `ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.

**NEW genuinely external analytic inputs: NONE.** No PNT/Mertens/BV estimate is introduced or re-proved.

Reused *manuscript-internal* source statements (all source-only/uncompiled in this incremental chain):
- `firstExitDepthFrontier` and its actual rank-one stopping recursion from `ImbalancedChen.FirstExitDepthSplice`; consumed in `rank_one_selected_occurrence`.
- `mem_firstExitDepthFrontier_roughPrime_remaining` from `ImbalancedChen.FirstExitFrontierInvariants`; consumed in `receiver_root_mem_of_physical_and_policy` to recover the exact real smaller-prime suffix.
- `mem_roughPrimeUniverse_iff_of_cutoff_le_cap` from `ImbalancedChen.RoughPrimeUniverse`; consumed in `raw_receiver_root_mem` with actual cap/root premises.
- `raw_tagged_root_prime` from the original tagged arithmetic receiver source; consumed in `raw_receiver_root_mem`.
- `raw_factor_post_root_remaining_iff`, `frozen_only_bad_post_root_first_exit`, `rejected_frozen_bad_post_root_first_exit` from `Part5OriginalH430PostRootRemainingExact`; consumed in `raw_receiver_factor_in_root_suffix_iff`, `frozen_receiver_own_root_first_exit`, `rejected_receiver_own_root_first_exit`.
- `frozen_only_tagged_first_bad`, `rejected_frozen_tagged_first_bad` and original raw receipt inclusions; consumed in both precise first-bad channel instantiations.

Still *manuscript-internal* and OPEN: universal root physical/retained admission, full/selected/inherited owner and multiplicity, all signed rejection payments, Buchstab/retention closed-cell count induction, literal same-rho and PP consumers, outer integral/Theta count and common430+11 refinement.

Mathlib standard finite/list logic, natural-number primality and real arithmetic are reused without new axioms.

Validation: SOURCE_ONLY; no Lean elaboration, kernel replay, transitive axiom audit, numerical430 or CI. All finite checks UNEVALUATED.
