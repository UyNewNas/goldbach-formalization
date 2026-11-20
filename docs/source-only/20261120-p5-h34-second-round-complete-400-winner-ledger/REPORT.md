# P5.6 → h34 — full original second-round Q80 receipts and winner ledger

Date: 2026-11-20 (Asia/Shanghai).
Repository: `UyNewNas/goldbach-formalization`.
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Incoming HEAD: `52b154e83b99093ea3f87151cbbd060b5a1915ac`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean: v4.33.0-rc1; pinned mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual internal source increment

- `Part5OriginalH430SecondRoundComplete400.lean` defines *exact candidate integers* for 100 upper + 59 lower second-round interior physical slots. The previous 58 upper + 35 lower exterior receipts are imported and reused.
- The new finite Lean candidate proofs compare the 159 interior integers directly to the authentic second-generation `iterate 2` and original 106-row scan, after substituting the previously proved-in-source `iterate 1 = firstRoundExactReceipts`; they do not replace the old producer or divide outside each suffix summand.
- Combines them with the prior exterior + support proofs into `second_round_all_400_exact`, a full two-table equality at every genuine physical cell. `second_round_ceiling_iff_receipts` permits future *actual* F-envelope comparison but does not pay it.
- Keeps the `roundDecision` original winning `Choice`: in upper interior positions 0..89, a true 106-row bank wins, and positions 90..99 are genuine Buchstab winners. `second_upper_100_winning_choice_actual` checks the exact chosen row for each bank cell, not just the integer maximum. `second_upper_100_bank_winner_count` yields 90 **physical winner cells**, not 90 selected-count source weights.
- This is a second-generation physical certificate only, NOT the original U3/U4 selected-count/root/owner source, an all-430-round CLOSED-CELL bound, or an analytic theorem.

## Independent BigInt audit (NOT Lean proof)

- Parsed original `P2Selected430LiteralActionData` row data: 106 rows, 200 log weights, `q=2^80`.
- Recomputed the literal `seed` and original round producer; ALL 100 prior upper-first and 59 lower-first receipts matched.
- Recomputed round two; ALL 58 previous upper exterior and 35 lower exterior receipts matched, with original signed integer floor division and strict bank scan tie-breaking.
- Second-generation nonzero cell count: 158 upper + 94 lower = 252.
- Second-generation Q80 physical numerator totals: upper `2528340365584154650020615`; lower `878425811255153033256372`. These are not arithmetic selected-count or Theta.
- Upper interior winning actions: 90 bank physical cells (22 distinct winning row indices, possibly repeated per target) and 10 Buchstab cells; zero retention winners. Distinct bank row indices: 75, 78, 80, 81, 83, 85, 86, 87, 89, 90, 91, 92, 94, 95, 96, 98, 22, 100, 101, 31, 103, 41.

## Validation boundary

The active runtime has no Lean/Lake/Elan or pinned import closure; the original `P2Selected430CausalOccurrenceExporter` and `P2Selected430LiteralActionData` are source-only packet files, not installed buildable `ImbalancedChen` modules. Thus the new `fin_cases/decide` proof bodies are **not compiled or kernel-checked**. No `COMPILED`/green evidence, kernel replay, transitive axiom audit, finite Lean certification or heavy CI dispatch. Static forbidden-token scan and arithmetic cross-check are not compilation.

No P1.4, P3.6, production modules, CI, frozen manuscript, toolchain, c/K, root norm 7/2, row norm 12, actual alpha, or same-Q changes. No new external mathematical theorem or axiom.

## Specific next action and outstanding internal obligations

1. Restore/install the exact pinned producer import closure under `ImbalancedChen` and compile `FirstRoundExact400`, `SecondRoundExteriorSources`, then this module, fixing actual errors without proof escapes.
2. Compare the full 400-cell second-generation numerators with frozen F at its *actual closed query endpoints* and pay the true seed/base and positive bank+Buchstab sources.
3. Complete generations 3..430 CLOSED-CELL; original U3/U4 selected-count, root norm, owner/full/selected/inherited/rejected lanes; seven-integral ≥0.65 (previous candidate total 0.590); same-rho/PP, native history, outer integral–Theta–count and common 430+11 causal refinement.

**完整h34稿内证明仍未闭合。**
