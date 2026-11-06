# P5.6 → h34 — actual Buchstab physical trim cancellation

2026-11-06. Branch: `chatgpt/p5-h34-request-admission-20261105`. Verified parent: `567ec8284387435d04065374b54417288eefde76`.
Fixed manuscript: UyNewNas/chen-imbalanced-semiprimes, `ba6ec11d800eccc54406490631895e174de85766`; unchanged parameters, c/K, root norm 7/2, row norm 12, real alpha, common Q, 430+11 target and original upper/lower polarities.

## Mathematical increment

Last packet left a moving physicalStart/baseStart integral trim as an unpaid signed residual. Examination of *existing proved-in-source geometry* reveals a stronger, **request-specific** statement: `RequestedAdmission.Coherent` already contains `ceiling_pos` and `cutoff_fits : residual ≤ argument × ceiling`. `RequestedMember.rootHistory_coherent` propagates it to every selected generated history occurrence (root and actual chosen LocalDomain edges). `CutoffCoherence.physicalStart_eq_baseStart` then gives `physicalStart = baseStart`; with the actual lower-direction guard from `RequestedNonbankSupply.requested_buchstab_guard`, `CutoffCoherence.idealProfile_eq_original` proves equality of the two *literal* integrals. This is **not** equality for arbitrary PhysicalNode, nor a claim that strict ceiling filtering can be removed from the actual prime child carrier.

Seven new candidate proofs: `coherent_start_eq_base`, `selected_integrals_eq`, `selected_buchstab_read_le_ideal`, `actual_buchstab_physical_trim_eq_zero`, `actual_buchstab_residual_nonpos`, `actual_one_generation_without_trim`, and `uniform_actual_one_generation_without_trim`. They eliminate the previous signed **Buchstab integer suffix physical-start** loss on the generated histories, including specified-cell requests, while preserving actual occurrence positions, positive path marks, parent Theta, same root Q, and the original strict-prime row error and 106-bank candidate gaps. There is no double payment and no weaker target.

The key logical distinction is important: `CutoffFits` is a genuinely proved geometric induction invariant in existing *uncompiled candidate sources*. Were that invariant or one of its import dependencies to fail Lean elaboration, this packet has no verified cancellation.

## Remaining internal obligations

- The full bank/base/fixed/switched/seed/floor application and actual CLOSED-CELL **arithmetic count** induction; a one-generation feedback inequality is not the original U3/U4 count licence.
- Complete original U3/U4 selected-count, root normalization, full/selected/inherited history filters, authentic owner, rejection-event multiplicities and payment. Original p versus initial z0/presieve stage mismatch remains.
- Manuscript-local PP/same-rho, native-history proper/equality/inherit masses, outer integral–Theta–count and one common nested 430+11 causal refinement.
- Lean staging/compilation, kernel replay, transitive axiom audit and numerical430/finite guards, all still UNEVALUATED.

No new external analytic input, sorry, admit, axiom, unsafe, native escape, CI run, dependency upgrade, default-branch change or modification of others' files. New source is additive in a dedicated source-only directory. This is **SOURCE_ONLY / UNCOMPILED / UNEVALUATED**, formal credit zero; complete h34 OPEN.

Next action: use the no-trim one-generation inequality as a real premise for the original bank/base/fixed/seed arithmetic CLOSED-CELL induction, but first match actual U3/U4 count and owner filters rather than asserting a target-equivalent source identity.
