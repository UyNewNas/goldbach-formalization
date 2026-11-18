# P5.6 h34 — exact full Q80 generation-zero CLOSED-CELL base

2026-11-19 (Asia/Shanghai). Dedicated branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Incoming HEAD: `b993421fc834d6877c2f1f7cd329d67108d447f7`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; no updates.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Increment and precise limits

The previous `Part5OriginalH430LiteralRoundActionStep` gave a correct producer-level reduction of one round to actual retention, enabled Buchstab and targeted original 106-bank candidate inequalities. It did not prove the FULL CLOSED-CELL base. The previously written `Part5OriginalH430LiteralZeroFixedSeed` establishes only that original fixed W1/W2 bank anchors start at zero (all above cell 59).

This new module evaluates the full original `iterate 0 = seed` and the unchanged 2^80 `floorValue` for both Boolean tables. Its integer quotient is
`2327 * 2^80 / 100000 = 28131703822432420895412` (Euclidean integer division),
with discarded remainder **71552**. The literal upper first-60-cell height is thus `28131703822432420895412/2^80` and is STRICTLY smaller than `2327/100000`.

The source proves a formal candidate IFF reducing the actual two-table generation-zero CLOSED-CELL condition to three manuscript-internal analytic conditions on the unchanged F:
(1) `seedHeight <= F true s` on each original upper cell `i<60`;
(2) `0 <= F true s` on upper cells `i>=60`;
(3) `0 <= F false s` on all lower cells.
Every queryCell remains closed, including shared boundaries. No analytic F or h34 count closure is assumed or inferred. The algebraic integer identities were checked separately using exact integer arithmetic, which is NOT a Lean build or finite certificate.

## Verification and provenance

The head was checked before write. All changes are in the NEW directory `docs/source-only/20261119-p5-h34-exact-q80-full-seed-base`; no edits to P1.4/P3.6, production source, CI, dependency files, other users' files or the frozen manuscript. No proof escapes or custom assumptions. Direct import: `ImbalancedChen.Part5OriginalH430LiteralRoundActionStep`.

No Lean, Lake, Elan, or staged fixed source import closure is available in the execution environment. No targeted compile, kernel replay, transitive axiom audit, independent review, or original finite certificate replay took place. All 7 theorem bodies plus 1 definition remain uncompiled candidates, not green.

## Manuscript-internal next actions

1. Check the F actually fixed in the proof against the three exact seed clauses; the first-60 positive Q80 seed is a genuine obligation.
2. Prove retention, real Buchstab suffix and 106 targeted bank Q80 candidate ceiling inequalities under the same predecessor F and correct scalar versus specified-cell modes, then establish all 430 induction steps.
3. Complete the original U3/U4 full/selected/inherited count source, root norm 7/2, owner collision and signed rejection payments, full base/fixed/switched and floor/seed costs.
4. Finish manuscript-local PP/same-rho, native history, outer integral/Theta/count and ONE common 430+11 nested causal refinement; compile, kernel-replay, audit axioms and finite certificates once a complete dependency closure is staged.

**The complete manuscript-internal h34 proof is still OPEN.**
