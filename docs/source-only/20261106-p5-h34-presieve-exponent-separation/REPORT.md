# P5.6 → h34 — original U3/U4 and presieve-exponent separation

Status: **PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED**.

- Repository: `UyNewNas/goldbach-formalization`; branch: `chatgpt/p5-h34-request-admission-20261105`.
- Actual preceding remote HEAD: `c4f1f4dba1533636068d3651af3b9cf6a876019c`.
- New source commit: `9632e6757131f9d16e34f367e112e783aeb3672d`.
- Source module: `Part5OriginalH430PresieveExponentSeparation.lean` (228 lines, 12 uncompiled theorem candidate bodies); Git blob `6cb8e0e83ed4e176e34b8feb937e84e7841c32f9`.
- Pinned manuscript unchanged: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Only an additive source-only packet; no production source, P1.4/P3.6, compiler/dependency/CI or manuscript edits; no CI dispatched.

## Mathematical finding, and what it does NOT establish

The fixed manuscript §lower, lines 695–696, says the **ordinary lower trees start at w=a and w=h**. Lines 712–719 separately introduce a **projection presieve** `z0=N^omega`, without specifying a numerical omega there. These are not interchangeable stages. The original selected-prime bands start at `N^a`, `a=417/5000` (the pre-existing `original_band_lower_power` follows the actual U3/U4 selectors).

The new source proves, for `N≥2` and `omega≤a`, the genuine real-power comparison `N^omega≤N^a`. Therefore any actual original raw (U3/U4,p,q) receipt satisfying the **initial historical rank-one root licence** at `z0=N^omega` would require `a<omega`—contradicting this exponent regime. This is stronger than the last packet's uninstantiated `z0≤N^a`: it proves the exponent implication in Lean candidate source rather than leaving the power comparison to prose.

For EVERY subfamily of the actual raw source, the rank-one licensed-root filter is empty and `gateBlocked` is the whole subfamily. With the real initial-carrier cap hypothesis `N^omega≤cap`, no original selected p enters the literal `roughPrimeUniverse N cap 0 z0`.

More importantly, the existing receiver-specific four-lane bookkeeping is **preserved, not dropped**: the `ownCarrierOutside`, `ownPolicyPass`, and `ownPolicyFail` rank-one lanes are all empty for both `frozenOnly` and `rejectedFrozen` under this exponent condition. The exact original rejected count stays in the two gate-blocked sources; the NEW signed ledger proves the same equality for an arbitrary `TaggedReceiver → ℝ` weight, without assuming positivity, changing root norm 7/2, row norm12, or paying an event more than once.

The conclusion is strictly about mapping the ORIGINAL arithmetic selected p to the FIRST prime of the **small-presieve historical tree**. It says NOTHING that excludes a different genuine later-stage owner, does not prove this manuscript chooses `omega≤a`, and does not establish a full/selected/inherited history. No original U3/U4 receipt or q multiplicity is eliminated, and no signed mass has been paid.

## Accurate new candidate declarations

- `presieve_power_le_original_band_start`
- `raw_rank_one_licence_forces_exponent_gt_a`
- `raw_rank_one_carrier_excluded`
- `raw_rank_one_licensed_filter_empty`
- `raw_presieve_blocked_exact`
- `raw_presieve_own_outside_empty`
- `raw_presieve_own_pass_empty`
- `raw_presieve_own_fail_empty`
- `frozen_presieve_no_own_root_event_lanes`
- `rejected_frozen_presieve_no_own_root_event_lanes`
- `rejected_presieve_original_count_unpaid`
- `rejected_presieve_signed_source_unpaid`

## Remaining manuscript-internal obligations

1. Locate the exact omega and thresholds at **each actual historical consumer**; the pinned text gives symbolic `z0=N^omega` here. If `omega≤a`, abandon the impossible original-p-as-initial-root map and build a correctly staged full/selected/inherited owner or explicitly pay the full blocked source. If `omega>a`, prove the actual per-root cutoff/cap and Rosser obligations (no claim that all roots are admitted).
2. Bind original U3/U4 selected-count, multiplicity of actual `(band,p,q)` receipts and true root weights to the correct history, with noninjective event fibres and signed/outside/pass/fail payments. The exact signed unpaid ledger is not a count inequality.
3. Complete request-level Buchstab/retention and the all-action closed-cell arithmetic induction, remaining feedback weights/floors and ordinary/fixed/switched/seed/beta terms.
4. Finish manuscript-local PP/same-rho compatibility, native history, external integral–Theta–count bridge and one 430+11 nested causal refinement, without weakening c/K or original normalization.
5. Compile staged dependencies, kernel-replay every proof, audit transitive axioms and independently evaluate the inherited numerical/finite guards.

## Validation

Source blob and source commit read back from the remote; remote HEAD confirmed and single-file diff inspected. Text-only restricted-token and basic bracket checks were run. These **do not** establish successful Lean parsing, elaboration, compilation or kernel replay. No heavy build or CI is requested. No transitive axiom audit, independent review, numerical430 or other finite certification: **UNEVALUATED**. No green engineering node or formal proof credit.

**完整 h34 稿内证明仍未闭合。**
