# P5.6 → h34 — exact original first-round 400-cell Q80 receipts

Date: 2026-11-20 (Asia/Shanghai).
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Parent HEAD: `d54e2f02f54f18da0331919ef28a041900fc37c0`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Toolchain pinned: Lean v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual mathematical increment

Read the original 106 `rows` from the archived literal file
`docs/source-only/20261028-resume-30c/certificate_triple/P2Selected430LiteralActionData.lean`
at the parent commit. Independently reconstructed each original
`candidate seed` with exact signed BigInt arithmetic, original
per-term Q80 quotients, fixed divisors and row targets. All 106
independently computed values match the prior `REGISTRY.json`
`first_bank_row_candidates` exactly.

Computed the true upper first-round numerator at each physical index
0..99 as the maximum of the ORIGINAL retention seed and precisely
the targeted bank offers. There are 23 distinct receipt values.
Indices 0..54 have numerator 29109517144010128037267; 95..99 are exactly 0.
Every upper index >=100 is already known to vanish structurally.
This yields **95 possible nonzero upper** + **59 possible nonzero lower**
= 154 possible first-round physical cells, improving the previous 159.
This does NOT mean all these positions are strictly positive.

The Lean candidate `upper100Numerators : Fin 100 → ℤ` stores every
physical upper receipt. `first_upper_100_exact` proposes direct
finite evaluation against the real `iterate 1 true`, not a copied
recurrence. `first_round_all_400_exact` joins it to the already
recorded exact 59 lower integers and both actual zero tails.
`first_round_ceiling_iff_receipts` reduces the true original first
table to those indexed receipts for arbitrary integer ceilings,
without asserting any unpaid F comparison.

## Precise boundary

No frozen analytic F inequality has been proved at any physical
closed-cell endpoint. No second-to-430th-generation positive-source
payment, U3/U4 count owner/filter/rejection identity, PP/same-rho,
intercept/seed payment, native-history or joint 430+11 refinement
has been supplied. The prior seven-integral candidate total remains
0.590 against the 0.650 target and is also UNCOMPILED.

This source has not been compiled: Lean, Lake, Elan and the pinned
import closure are absent from the execution environment; native
GitHub DNS access is unavailable. Neither first-round finite
`decide` certificate nor inherited ones have had kernel replay.
Independent BigInt checking is not Lean certification.
No CI job, transitive-axiom audit or finite Lean certification was run.
No green completion status is warranted. No change to CI,
pinned mathlib, c/K, root norm 7/2, row norm 12, same-Q or alpha.

## Next exact actions

1. Stage this new module after `Part5OriginalH430FirstRoundQuantitativeReceipts`
   under `ImbalancedChen` in the pinned toolchain; run isolated Lean
   compilation and repair any actual errors (no sorry/admit/unsafe).
2. Use the exact per-cell integer receipts to compare with frozen
   F at real closed-query endpoints, preserving flooring and the
   designated-cell versus scalar semantics.
3. Prove actual 429 later-round Buchstab and bank payments and full
   CLOSED-CELL induction, then root weights and count-source mapping.

**完整h34稿内证明仍未闭合。**
