# P5.6 → h34 — actual 430-generation prefix CLOSED-CELL winning budget

Date: 2026-11-19 (Asia/Shanghai).
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Verified incoming head: `0879c2fbe3301923f7d60d50acaf895e86871bbb` (the preceding unified-winning-action packet).
Mathematical source commit: `05cd67e7315f2a68d95e5f2506dd45617d5880cd`.
Mathematical source blob: `c506f1b4ab87cbd7fcb3ebbb0eb44b5a2f436cf5`.
Source: `Part5OriginalH430PrefixClosedCellWinningBudget.lean`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean: `v4.33.0-rc1`; Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual increment

The preceding `uniform_actual_winning_action_budget` supplies a single pre-N threshold for one generation's genuine Buchstab winner plus all 106 selected bank action families. The existing `uniform_actual_one_generation_fixed_upper` separately propagates the *actual* selected fixed-cell predecessor bound through the signed read-minus-child step. This packet combines them over every real causal prefix of the 430-generation request history.

- `generationPrefix m` uses genuine `Fin 430` generation positions with `g.val < m`. `generationPrefix_zero` and `generationPrefix_full` identify the exact two endpoints, avoiding generation-zero wraparound. `generationPrefix_mono` preserves causal-prefix inclusion.
- `uniform_actual_prefix_closed_cell_winning_budget` chooses `T = max Tf Ta` **before** N, n, root, tau, p, m, F and individual actual generated positions.
- The first conclusion sums the real signed `levelReadMass - levelChildMass` across the prefix and bounds it using original Buchstab epsilon*Theta plus selected 106 bank fixed-reference gap. Crucially the only CLOSED-CELL premise is the *previous-table fixed-cell inequality at generations belonging to that prefix*, with the real queryCell and `iterate g.val true`. It is an unresolved induction premise, not a root counting licence.
- The second conclusion bounds the prefix-summed actual Buchstab error plus **selected bank applied error**, by epsilon times the **matching action-specific Theta sum**.
- The third conclusion preserves the distinct Buchstab 5*Theta and bank 12*Theta row masses over the same prefix and real Fin positions. No 5+12 combination per winner and no charge for unselected alternatives.
- The physical root-dependent Q, true alpha prerequisites and W1/W2 specified-cell versus scalar distinction are inherited unchanged from the two named suppliers. There is no new source enumeration, repeated physical product quotient, q/tag collision payment or claimed CLOSED-CELL base.

The theorem is a **conditional causal-prefix estimate**, not an induction deriving the predecessor CLOSED-CELL bounds, not an original U3/U4 arithmetic source-count identity, and not the final h34 claim. In particular it does not pay positive dynamic ideal/seed, first-excluded non-edge mass or q/tag multiplicities.

## Engineering and source boundary

This branch is the dedicated continuing h34 branch, identified by the actual prior remote commit ancestry; the original 20261105 request-admission branch is an earlier entry and was *not* reset or rewritten. Initial remote branch HEAD was checked before a fast-forward source commit. At inspection the branch's returned 12 Actions records were completed; none was running or queued. GitHub reported push permission.

The current runtime has no `lean`, `lake`, `elan` or staged pinned source-only import closure. No corresponding CI compile was dispatched or observed; prior workflow outcomes do not verify this source. No kernel replay, transitive-axiom audit or finite-certificate evaluation was run. Source review and git SHA/diff checks are *not* compilation. All four theorems are candidates; **no green status is granted**.

No production modules, P1.4/P3.6, CI configuration, Mathlib/toolchain pin, manuscript, c/K, root norm 7/2, bank row norm 12, alpha, same-Q or 430+11 constraint were changed.

## Still-open manuscript-internal obligations

1. Stage fixed source-only import closure and run targeted Lean/Lake on this module and the two predecessor suppliers; repair actual elaboration errors rather than bypassing.
2. Prove the genuine **m to m+1** CLOSED-CELL recursion from an initial base/seed and actual floor/read/feedback conditions, instead of treating the prefix predecessor premise as discharged. Show proper scalar and specified-cell coverage.
3. Quantitatively fund positive Buchstab/dynamic ideal, base, fixed/switched anchors, exact Q80 floor and signed remainder; a one-step error bound is not a positive source payment.
4. Connect original U3/U4 full/selected/inherited q/tag count source, root norm 7/2, six rejection lanes, real first-forbidden owner and signed collision capacity to true generated history.
5. Establish manuscript-local PP/same-rho, native-history, integral–Theta–count correspondences and one common causal 430+11 refinement.
6. Run kernel replay, transitive axiom audit and finite certificates after compilation.

**Next concrete mathematical move:** prove an actual predecessor-to-successor CLOSED-CELL step at prefix boundary m using the existing real `iterate` recurrence and exact seed/cell bounds; do not add a hypothetical all-430 CLOSED-CELL certificate.

**FULL H34 MANUSCRIPT-INTERNAL PROOF IS NOT CLOSED.**
