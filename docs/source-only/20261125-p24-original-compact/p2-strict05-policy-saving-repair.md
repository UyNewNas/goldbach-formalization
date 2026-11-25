# P2 strict05 policy gate instance repair

Actual input source: `ed3b16671f377f1e122db28baaae321cf667a597`.
Original P2 task: `bb4d0ea087c8466b945c36f6e68a2b04`.
Complete log: `p2-strict-symbolic-05.log`, 17467 bytes, SHA-256
`d16e52df7542486074b3ccadc65abca416f372283e7f7c34cfe7e20271d841e4`.
The batch completed with 283/321 symbolic modules accepted (276 reused,
seven fresh), four direct failures, and no pending work. Both unchanged
existing dictionary modules added in strict04 now passed in this context.

## Actual failure and classification

At lines 102 and 105 of `ActualExtendedThirdCompactPolicySaving.lean`,
`rw [if_pos hc]` and `rw [if_neg hc]` failed. The emitted diagnosis identifies
an inconsistent elaborated conditional after the preceding simplification:
the displayed proposition uses `p2`, but its `Decidable` argument still has
the condition containing `[p2, p1, p0].headD 0`. Under the rewrite tactic's
implicit transparency the application is not type-correct.

This is a formal expression/instance normalization issue. The frozen
1106 `sieve-appendix.tex` first-exit section (cube tests and
`sv:first-exit`) retains the earlier prefix tests and the complete odd-rank
continuation. The existing definition `actualOwnCubeGatedMinusDensity`
contains exactly the strict own-cube test and the same residual density.
Neither a missing mathematical premise nor a new estimate is introduced.

## Candidate

Introduce one local `hgate` equality, proved by `rfl`, displaying the existing
density at `[p2, p1, p0]` as a complete conditional with `p2` as its head.
Rewrite by this whole equality before `if_pos hc` or `if_neg hc`. This avoids
rewriting only the head occurrence inside an elaborated condition while
leaving its instance argument in the old form. The negative branch still
uses `mul_zero`; the positive branch still uses the same admitted residual
identity and negative third-prefix mass.

The new local equality is an expansion of the existing definition, not an
additional assumed theorem. The strict inequality, inherited first cube,
both physical levels, and all prime-history parameters are unchanged.
No already accepted module or existing dictionary proof was edited.

## Static checks and evidence boundary

A byte-level comparison against the actual input source preserves all eight
existing theorem headers, the single computation definition and all five
imports. `git diff --check` passes. No axiom, `sorry`, `admit`, unsafe/partial
declaration, `native_decide`, option, or gate change was introduced.

Candidate SHA-256:
`bf5fd477ee188ae3e65a03b7993def076da29a2b9d69045ae80fc2f938a18711`.

Independent read-only review at this exact source hash found no static
blocker in the complete conditional equality or either branch rewrite.

This candidate has not yet passed the original compiler. Finite certificates
and the complete independent owned-declaration audit remain open.
