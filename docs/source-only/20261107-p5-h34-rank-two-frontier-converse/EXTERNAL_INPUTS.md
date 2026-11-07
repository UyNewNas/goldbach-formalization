# P5.6/h34 — EXTERNAL_INPUTS (record only)

Source commit: `9f269ad9f761ee9e775d2b909c4a21ffb3abcb77`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Lean: `leanprover/lean4:v4.33.0-rc1`.
Mathlib4: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
No toolchain/dependency version or manuscript change.

## New genuinely external analytic input

**NONE**. Do not implement PNT/Mertens/BV/Rosser external analytic proofs.
No new analytic axiom, manuscript target-equivalent hypothesis or oracle.

## Reused inputs and exact call sites

- Existing Mathlib List.mem_append, List.mem_cons, List.cons.inj,
  finite-list simplification and omega at pinned Mathlib revision:
  `one_step_frontier_is_next`, `two_step_frontier_is_two_nexts`,
  `actual_rank_two_frontier_implies_retained_original_second`.
  Premises: finite list membership, explicit policy Bool equalities,
  and prefix length; no analytic hypotheses.
- Existing manuscript-local `firstExitDepthFrontier` original
  recursion in `ImbalancedChen.FirstExitDepthSplice` and
  `firstExitDepthFrontier_of_rank_le_length` in
  `ImbalancedChen.FirstExitFrontierInvariants`. Called in the two
  private reverse-recursion helpers. No policy-test licence supplied.
- Existing manuscript-local `mem_firstExitNextSelectionCandidates_iff`
  in `ImbalancedChen.FirstExitCandidateGeometry`. Called in
  `actual_rank_two_frontier_implies_retained_original_second`.
- Existing manuscript-local *uncompiled candidate*
  `retained_original_second_in_actual_rank_two_frontier` from
  `Part5OriginalH430ActualRankTwoFrontierSupport`, used in
  `retained_original_second_iff_actual_rank_two` and
  `retained_original_second_unique_frontier_state`.
- Existing manuscript-local
  `mem_firstExitDepthFrontier_roughPrime_remaining`,
  `mem_firstExitDepthFrontier_positive_eq_evenListLength`,
  `mem_firstExitDepthFrontier_mass_eq_selected_prod` in
  `ImbalancedChen.FirstExitFrontierInvariants`. Used in
  `actual_frontier_state_determined_by_prefix`: same fixed
  physical policy/carrier, positive rank, real frontier memberships
  and equal ordered prefixes.
- `originalPhysicalQ`, `ordinaryRosserRetainedPolicy` and
  `retainedOriginalSecond` are unchanged manuscript-local objects.

## Obligations NOT outsourced

Original U3/U4 selected-count, q/tag occurrence and exact historical
owner/capacity, full/selected/inherited filtering, physical z0/phase,
signed rejection payments, all-action CLOSED-CELL induction,
base/seed/feedback/integral/Theta/count, manuscript-local PP/same-rho
and common 430+11 causal refinement are still internal.

All source-only candidate proofs UNCOMPILED, finite guards UNEVALUATED;
no kernel replay or transitive axiom audit.
