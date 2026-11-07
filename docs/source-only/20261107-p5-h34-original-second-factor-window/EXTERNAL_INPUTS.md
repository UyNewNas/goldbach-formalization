# P5.6 h34 — external-input boundary: original second-factor candidate window

Status: SOURCE_ONLY / UNCOMPILED / UNEVALUATED. No new external analytic result is implemented.

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Lean toolchain unchanged: `leanprover/lean4:v4.33.0-rc1`; Mathlib unchanged: `leanprover-community/mathlib4@e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## Existing infrastructure reused, not proved anew

- Mathlib finite Finset sigma membership, finite sums, list constructor equality and casts. Used in `original_quotient_is_rough`, `original_factor_in_rank_one_suffix_iff`, and `stage_second_candidate_eligibility_signed_ledger`.
- Existing `ImbalancedChen.FirstExitCandidateGeometry.mem_firstExitNextSelectionCandidates_iff` and `roughPrimeUniverse` carrier membership/strict upper bound, applied with the exact root prime, cap and target N in `original_factor_in_rank_one_suffix_iff` and `second_candidate_true_mass_sign`.
- Existing source-only interfaces `original_tagged_subset_raw_unconditional`, `raw_quotient_factor_not_target`, `stage_zero_candidate_exact_suffix`, `stage_zero_candidate_mass_sign`, `actual_next_candidate_iff` and `selectedOriginalRootStage` are manuscript-internal candidate dependencies, NOT external black boxes; used in `original_factor_in_rank_one_suffix_iff`, `original_factor_next_candidate_iff`, `possible_original_second_iff` and `second_candidate_true_mass_sign`.
- The original `ChenPrimeRough ((N:ℝ)^a) q` sieve is obtained from the actual definition of `originalReceiver N p` in `original_quotient_is_rough`. No new roughness assumption or unpinned cutoff is introduced.

No PNT, Mertens, BV, analytic Buchstab distribution input or any external number-theory lemma is added or re-proved. Their pre-existing interfaces remain at the fixed versions and are not newly invoked by this packet.

## Still manuscript-internal, not outsourced

The TRUE second-rank Rosser retention, all full/selected/inherited gates and owner/count multiplicities, signed Euler payment, precise physical z0/phase, original q-to-history counting, all-action induction, seed/feedback/integral-to-Theta, manuscript-local PP/same-rho and one common causal 430+11 refinement are INTERNAL and remain open.

No transitive axiom audit or kernel proof check has been performed. Source-only proof bodies are not certified.
