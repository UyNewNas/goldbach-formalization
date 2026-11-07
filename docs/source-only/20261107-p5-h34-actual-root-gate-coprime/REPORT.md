# P5.6 → h34 — actual U3/U4 root-gate nondivisibility and two remaining blockers

Date: 2026-11-07 UTC.
Task branch: `chatgpt/p5-h34-request-admission-20261105`.
Verified preceding remote HEAD: `9b5dcab031d05fc3af07e37e7c482232989670f3`.
Initial mathematics commit: `f2a4ea1c6c89605d52c54cfd41453e2c5e38c039`.
Corrected mathematics commit: `6aa124224d47cced2903d4e9a84d78375ae71b5f`.
Source blob: `db99db48eff32c1078b749bd9c49e75fed8a2b28`.
Module: `Part5OriginalH430ActualRootGateCoprime.lean`, 245 lines; 13 theorem bodies (including three private), 3 definitions.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.

**PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED.**

## Actual increment

The previous packet `EvenSignedExitBounds` showed that, for even N and a genuine original fourth-lane event key, the ACTUAL signed rank-two historical exit is in [-W,0]. Thus its negative sign cannot pay a positive arithmetic receiver. This packet does not reopen that signed ledger or turn an equality into a payment.

Instead it discharges an independent **actual root-gate condition** from the full U3/U4 source. Existing `original_band_prime` states that the selected p in BOTH original root bands is prime and coprime to N. The new `raw_root_prime_coprime` pulls this concrete fact through every genuine tagged (U3/U4,p,q) raw receiver, retaining overlapping-band occurrences. The new `raw_root_not_target` uses p|N together with p.Coprime N to derive p|1, contradicting p.Prime. Consequently no actual rejected raw receiver can fail the `¬p∣N` clause of `rootLicensed`.

The NEW `raw_root_licensed_iff` derives the exact remaining two tests, **not** a stronger assumed root licence:

    rootLicensed N z0 Q lower receiver
       ↔ p < z0 ∧ ordinaryRosserPrefixAdmissible lower Q [p]

`actual_root_gate_split` partitions each genuine raw-source subset's former `gateBlocked` into exactly the disjoint cutoff-blocked and singleton-policy-blocked lanes. `actual_root_gate_card` and `actual_root_gate_signed` retain distinct original q/tag occurrences and arbitrary signed weights, respectively.

`original_two_source_gate_card` and `original_two_source_gate_signed` specialize these identities to the ACTUAL distinct `frozenOnly` and `rejectedFrozen` cutoff sources; no invented receiver family appears.

Finally `refined_non_event_weight_eq` rewrites the prior **six** original non-event lanes into **eight** actual non-event lanes: cutoff and singleton-policy obstruction for each source, plus each source's unchanged own-carrier-outside and second-prefix-policy-pass lanes. `original_rejected_refined_signed_gap` installs that refinement in the exact original rejected-U3/U4 signed-count ledger while keeping one actual signed Euler exit PER DISTINCT key and the full unpaid q/tag/key gap.

Mathematically the N-divisibility root obstruction is **eliminated for genuine arithmetic roots**, while all remaining non-event receipts and signed-history gaps stay explicitly unpaid. This is genuine source-level narrowing, not a full/selected/inherited owner proof.

## What remains internal and open

- Prove actual orientation/owner of the full, selected and inherited U3/U4 counts and root weights; preserve true q/tag overlap and noninjective event-key fibres. Determine the correct sign placement before any attempted cancellation.
- Pay or correctly filter each genuine root-cutoff/singleton-policy obstruction; the post-root carrier-outside and prefix-policy-pass lanes in both original sources remain.
- Bound actual fourth-lane q/tag receipt residuals against an appropriate signed historical mechanism; `actualRankTwoSignedExit≤0` itself is not a positive payment.
- Bind complete U3/U4 selected counts to generated root history and genuine CLOSED-CELL predecessor, plus base/switched/seed/floor, integral/Theta/count, PP/same-rho, native-history and single nested causal 430+11 refinement.
- Stage under pinned ImbalancedChen imports and perform Lean elaboration, kernel replay, full transitive axiom audit and held numerical430/finite replay.

## Validation and permissions

Only this task's new source-only directory was touched; no production code, P1.4, P3.6, fixed manuscript, toolchain, CI configuration or scheduled workflow was changed. The connected account has push rights and the existing h34 branch was fast-forwarded (not forced). The preceding branch HEAD was checked before creation.

The remote source file was read back after its first commit: one new file, 243 original source lines, zero deletions. A two-line import namespace correction was then committed to `6aa124224d47cced2903d4e9a84d78375ae71b5f`. The final source blob is `db99db48eff32c1078b749bd9c49e75fed8a2b28`; its content and final diff are to be read back. Static token and parenthesis checks were performed; they are NOT Lean parsing or compilation.

NOT RUN: Lean/Lake, kernel replay, transitive axiom audit, CI, independent mathematics review, numerical430 or finite guards. They remain UNEVALUATED. No new green node or mathematical closure claim.

**Next precise action:** take the real original U3/U4 selected-root/full/inherited filter and identify whether the cutoff-blocked and singleton-policy-blocked receivers are absent at that selection stage or require explicit mass payment. Then match the true negative Euler exit to its correct owner/sign without counting one (p,ell) event per q.
