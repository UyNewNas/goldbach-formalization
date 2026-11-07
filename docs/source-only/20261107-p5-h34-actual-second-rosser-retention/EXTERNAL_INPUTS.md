# P5.6 h34 — external-input ledger: actual second Rosser retention

Status: SOURCE_ONLY / UNCOMPILED / UNEVALUATED; no new external analytic input.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` at `paper/source/manuscript-body.tex` (blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).
Unchanged Lean toolchain `leanprover/lean4:v4.33.0-rc1`; unchanged Mathlib `leanprover-community/mathlib4@e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## Existing infrastructure reused, not re-proved

- Mathlib: `Finset.sum_add_distrib`, `Finset.sum_congr`, finite membership, `decide_eq_true`, `of_decide_eq_true`, basic real casts. Used in `stage_original_second_retention_signed_partition`, `retained_original_second_iff` and the retained-factor implication.
- Existing original first-exit enumerator `firstExitNextSelectionCandidates`, original full ordinary policy `ordinaryRosserRetainedPolicy` and `ordinaryRosserPrefixAdmissible` at the same physical `originalPhysicalQ`: invoked literally in `retainedOriginalSecond` and `retained_original_second_iff`.
- Existing manuscript-internal SOURCE-ONLY candidate lemmas `possible_original_second_iff`, `second_candidate_true_mass_sign`, `original_quotient_factor_lower`, `selectedOriginalRootStage` and `actual_original_signed_with_historical_root_candidates` are reused; they are **not external theorems and not yet compiled**.

There is no new invocation, reimplementation, proof or change of PNT, Mertens, BV or any other external analytic number-theory theorem in this packet. No new axiom is declared. Transitive external assumptions have not been audited.

## Remaining manuscript-internal duties

True recursive frontier membership beyond the literal two-step candidate/policy test, full/selected/inherited owner and multiplicities, correctly signed first-exit payments, all rejection lanes, request-level all-action count induction, base/seed/integral/Theta/PP/same-rho and common causal430+11 remain INTERNAL. A five-lane identity cannot be used as a target-equivalent assumption.

All new proof bodies are uncompiled and candidate only. Numerical430 guards remain UNEVALUATED.
