# P5.6/h34 external inputs — recorded, not implemented

Source commit: `a5b52ac2002d8380297cf4929f4c3314efdc29f7`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Lean toolchain unchanged: `leanprover/lean4:v4.33.0-rc1`.
Pinned Mathlib4 revision from unchanged `lake-manifest.json`:
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## New genuinely external analytic inputs

**NONE.** No external PNT/Mertens/BV/Rosser theorem was reimplemented.
No new analytic premise or h34 target-equivalent oracle was added.

## Existing helpers used

- Mathlib finite List operations and member/append simplification,
  `List.mem_append`, `List.nil_append`, `List.cons_append`,
  `List.append_nil` and ordinary arithmetic normalization at the
  pinned Mathlib revision above. Call site:
  `Part5OriginalH430ActualRankTwoFrontierSupport.lean`,
  private skip/lift lemmas. Their relevant premises are list membership
  and the actual `pre.length < k`; no analytic hypotheses.
- Existing **manuscript-local** `mem_firstExitNextSelectionCandidates_iff`
  from `ImbalancedChen.FirstExitCandidateGeometry`: exact
  `remaining = before ++ q :: after` and the selected state with
  flipped sign, multiplied mass and untouched after suffix.
  Applied in `retained_next_lifts_to_frontier`.
- Existing **manuscript-local** `firstExitDepthFrontier_of_rank_le_length`
  from `ImbalancedChen.FirstExitFrontierInvariants`: at
  `k <= selectedPrefix.length`, frontier is the singleton incoming
  state. Applied to the real selected rank-two state.
- Existing **manuscript-local candidate** theorem
  `second_candidate_true_mass_sign` from
  `Part5OriginalH430OriginalSecondFactorWindow`.
- Existing **manuscript-local candidate** theorems
  `retained_original_second_window_and_policy` and the literal
  `retainedOriginalSecond` from
  `Part5OriginalH430ActualSecondRosserRetention`.
  Used at the actual per-root Q; all remain UNCOMPILED.

## Still strictly manuscript-internal

Exact original (tag,p,q) source and full/selected/inherited history
owner, all action closed-cell induction, correct base/seed/PP-same-rho
matching, original signed rejection payments, true integral/Theta/count
connection, and one 430+11 causal refinement. No obligation was moved
to the external category.

No dependency versions or source pins changed. No transitive proof
axioms have been audited in this source-only packet.
