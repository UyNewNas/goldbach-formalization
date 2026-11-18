# P5.6 → h34 — least genuinely admitted second divisor

Date: 2026-11-18.
Repository: UyNewNas/goldbach-formalization.
Continuation branch: chatgpt/p5-h34-full-tagged-actual-fin-20261112.
Verified pre-write HEAD: 28e42c36afb65f8d6e06cede89709182bc7ca219.
Fixed manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766.
Pinned Lean v4.33.0-rc1 and Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

SOURCE_ONLY / CANDIDATE / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.

## Manuscript-internal increment

New file: Part5OriginalH430LeastEligibleSecondDivisor.lean.

The previous source packet built the actual original U3/U4 retained rank-two prefix from Nat.find but only used its existential witness. The new packet proves candidate source terms for the MINIMUM accepted prime divisor, not a new choice or a generic key reindexing.

- eligibleSecond is exactly: genuine prime ell, ell divides the original literal quotient q, and the true tag/p-specific second ordinary Rosser policy retains ell at the original physical Q.
- least_key_witness_and_minimality: selected ell has those properties and no smaller ell meets ALL of them.
- chosen_second_le_any_eligible: the chosen ell is at most every genuine eligible divisor of that same q.
- canonical_key_iff_first_eligible_divisor: bidirectional characterization, using the existing Nat.find witnesses, not an assumed count or historical owner.
- mem_canonical_fibre_iff_first_eligible: each actual arithmetic q receipt belongs to the canonical fibre iff it passes this smallest-eligible-prime sieve, preserving literal tag/p/q.
- least_key_original_window: connects the chosen factor to actual original N^a <= ell < p window, without claiming that all prime factors below ell are absent.

This is substantive progress toward an actual arithmetic first-exit decomposition. Crucial distinction: an ineligible smaller prime factor may divide q. One cannot identify the Nat.find first-eligible divisor with the first prime factor, the original historical Buchstab owner, or one historical mark per q.

## Validation and engineering boundary

Read original 20261105 REPORT/REGISTRY/EXTERNAL_INPUTS, the previous 20261118 retained-prefix source/REPORT/REGISTRY, and the actual arithmetic/Rosser/tagged fibre sources. Also inspected prior 20261107 tagged rank-two capacity packet to avoid duplicating its arbitrary-choice representative/surplus ledger. Last remote HEAD and repository write permission were independently checked before the commit.

Local shell check: git is present, but github.com DNS resolution fails. Neither lean, lake nor elan exists on PATH. The repository's source-only modules have not been staged into their fixed ImbalancedChen import paths and the frozen import closure is unavailable here. Do not treat textual or hash verification as Lean elaboration.

No actual Lean/Lake success, kernel replay, transitive axiom audit, finite certificate evaluation or valid module CI compile. This candidate remains UNCOMPILED even after remote commit and diff are verified. No CI configuration, dependencies, frozen parameters or manuscript changed. No additional external analytic inputs.

## Open internal obligations

1. Actually stage pinned source-only import closure; compile this and prior modules using fixed Lean/Mathlib; repair any true errors without admits.
2. Identify whether canonical first-eligible arithmetic second factor coincides with the ORIGINAL history first-exit owner; prove precise q/tag, physical-Q, root norm 7/2 and full/selected/inherited filter compatibility. NO inference from arithmetic key partition alone.
3. Control multiple q per tag/p/ell and real signed history capacity; pay rejected receipts rather than quotienting them away.
4. Close strict-prime Buchstab/retention, correct seed/base/fixed/switched/floor CLOSED-CELL induction, same-rho/PP consumers, native-history, integral–Theta–count, and one common 430+11 causal refinement.

FULL h34 manuscript-internal proof is NOT closed. Next concrete action: bind the canonical least-eligible divisor to the actual rank-two historical frontier or exhibit a precise mismatch and account for it; restore fixed import staging and compile.

## Confirmed source commit and remote readback

- Mathematical source commit: 271e2fdd66ca2c677545ba4e25a8f666d133285f.
- Lean source Git blob: 82f06caa534a6d6f1bb99c0f6dcbbc2e0d19688e.
- Remote source content reread matched exactly. Four-file source commit was checked; this does not constitute Lean elaboration.
- This documentation commit advances the branch only to persist the verified SHA, not to add a new theorem.
