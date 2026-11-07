# P5.6/h34 — EXTERNAL_INPUTS (record only)

New source commit: `a5438071cecd9c2eb2e2a793a0f58497c9f2af10`.
Base: `c7d163db038d439ed48d12454f9a3af803fe900d`.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex` (blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).
Lean: `leanprover/lean4:v4.33.0-rc1`.
Mathlib4 revision: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## New genuinely external analytic inputs

**NONE.** PNT/Mertens/BV/Rosser analytic proofs are not rewritten.
No new axiom, h34-equivalent assumption, or oracle.

## Reused declarations (not assumed anew)

- Pinned Mathlib finite `Finset.filter`, `Finset.image`,
  `Finset.mem_image`, `Finset.mem_filter`,
  `Finset.sum_ite_eq`, `Finset.sum_comm`,
  `Finset.sum_filter`, `Finset.add_sum_erase`,
  `Finset.sum_add_distrib`, and `Classical.choose/spec`:
  used in `chosen_second_factor_spec`,
  `key_representative_spec`, `chosen_key_weighted_partition`,
  `key_fibre_signed_split`,
  `retained_source_representative_and_surplus`,
  and `retained_source_capacity_card`.
  Premises: explicit finite originalTagged/retained Finsets,
  witnesses of real retained factors, keys from actual image,
  and membership of representative in nonempty fibre.
  No analytic threshold, convergence or density claim is supplied by these lemmas.
- Existing manuscript-local source-only **uncompiled candidate**
  `retained_original_second_window_and_policy` in
  `Part5OriginalH430ActualSecondRosserRetention`:
  called in `key_receipt_has_actual_rank_two_frontier` with
  originalTagged membership, chosen ell prime/divisor,
  and actual retained Rosser witness.
- Existing manuscript-local **uncompiled candidate**
  `retained_original_second_in_actual_rank_two_frontier` in
  `Part5OriginalH430ActualRankTwoFrontierSupport`:
  called in `key_receipt_has_actual_rank_two_frontier`
  at the exact per-root `originalPhysicalQ`,
  preserving sign, multiplicative mass and prefix.
- Existing manuscript-local **uncompiled candidate**
  `original_count_source_five_unpaid_lanes` in
  `Part5OriginalH430ActualSecondRosserRetention`:
  called in `original_source_with_tagged_key_surplus_and_unpaid`
  with the actual original tagged source and `z0 ≤ cap`.
  This is a source identity, not a count-to-history payment theorem.

## Still internal, not outsourced

True full/selected/inherited owner, list position and cross-tag state
capacity; root count weights, filter and physical stage matching;
cutoff/ordinary-Rosser/no-factor/non-event rejection payment;
signed Euler correct orientation; all-action CLOSED-CELL;
base/seed/switched/floor and feedback/integral/Theta/count;
manuscript PP/same-rho and common 430+11 causal refinement.

All proofs SOURCE ONLY/UNCOMPILED, finite guards UNEVALUATED.
