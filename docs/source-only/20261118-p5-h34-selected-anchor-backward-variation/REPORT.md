# P5.6 → h34: selected original Q80 anchor backward variation

Date: 2026-11-18 (Asia/Shanghai).
Work branch: chatgpt/p5-h34-full-tagged-actual-fin-20261112.
Verified predecessor HEAD: 47f47e49d0b8679cbc7b029ef6208f78e61afad5.
Mathematical source commit: 1c85e709d9fe367d89d89dee0806731883789376.
Lean source: Part5OriginalH430SelectedAnchorBackwardVariation.lean (258 lines).
Verified source Git blob: c2db8ef615c07e63e88924d80b83dea88d04dd46.
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766.
Pinned toolchain: Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## What changed mathematically

Earlier selected positive anchor proof exposed the actual winning W1/W2 positive fixed-reference defect, but did not relate it to the literal original Q80 recurrence. Rather than introducing another arbitrary small delta or a redundant floor ledger, this source defines the genuine per-cell **downward motion**:

  drop(k,i) = max(0, floorValue(iterate k,true,i) - floorValue(iterate (k+1),true,i)).

For every real reference z, original fixed cell i, and nonnegative integer m, the candidate proof gives the elementary but essential finite temporal bound:

  max(0,z-H_m(i)) <= max(0,z-H_0(i)) + sum_{0<=k<m} drop(k,i).

The proof is a real max inequality followed by literal Finset.range induction. It neither presumes the original Q80 table monotone nor discards a negative/positive change by signed cancellation.

An original W1 action is charged only its one fixed endpoint; W2 pays exactly 4/5 of the first fixed endpoint drop and 1/5 of the second. The theorem selected_action_anchor_le_seed_plus_variation expresses this for the **actual action at the actual preceding generation g**, with initial action-positive defect from genuine iterate 0 and the precise prefix k<g.

At the true selected Fin locations, including repeated request positions, selected_anchor_payment_le_seed_plus_backward_variation multiplies by original occurrenceScale and sums only the actual winning actions:

  bankSelectedPositiveAnchorPayment(g,F)
    <= bankSelectedSeedAnchorPayment(g,F)
       + bankSelectedBackwardVariationPayment(g).

The final root theorem frozen_root_le_seed_and_backward_variation_with_complete_floor composes the **full two-floor-credit** source inequality from the prior 9437873 packet, pre-floor-to-closed-cell ordering, the genuine fixed/dynamic positive sandwich and the new selected temporal anchor estimate. It preserves the literal zero-generation seed, actual Buchstab positive physical source, bank dynamic ideal positive excess, applied bank error, and full capped integer floor credit on the LEFT.

This new root consumer uses the original preceding CLOSED-CELL hypothesis explicitly. It does **not** imply that the literal zero-iterate anchor gap or the Q80 backward variation are small; they remain separate **internal quantitative debts**, not externally assumed estimates. The seed-anchor charge is a per-current-occurrence anchor mismatch and must not be confused with the terminal zero-generation request seed.

## Declaration coverage

Six definitions:
- firstOriginalGeneration;
- actualUpperCellDrop;
- actionBackwardDrop;
- actionCumulativeBackwardDrop;
- bankSelectedSeedAnchorPayment;
- bankSelectedBackwardVariationPayment.

Four candidate theorems (one private):
- clipped_gap_le_seed_plus_drops (private);
- selected_action_anchor_le_seed_plus_variation;
- selected_anchor_payment_le_seed_plus_backward_variation;
- frozen_root_le_seed_and_backward_variation_with_complete_floor.

## Current blockers / next mathematical action

1. Quantify the true ORIGINAL Q80 upper-table backward variation and genuine iterate-0 anchor deficits by the actual base/fixed/switched/feedback/seed recursion. This finite decomposition is not a paid numerical budget.
2. Prove all-action preceding CLOSED-CELL count induction and actual Buchstab strict-prime physical payment and terminal seed payment.
3. Finish complete U3/U4 original full/selected/inherited, root norm 7/2, owner, q/tag, rejected lanes and counting correspondence.
4. Complete PP/same-rho, signed Euler/native-history, outer integral–Theta–count and single common nested 430+11 causal refinement with fixed c/K and row norm 12.
5. Restore original pinned source-only import closure; compile this module and direct dependencies, correct compiler errors, kernel-replay and audit transitive axioms and inherited finite guards.

## Verification and ownership

Initial remote branch HEAD was exactly 47f47e49d0b8679cbc7b029ef6208f78e61afad5. Zero in-progress and zero queued Actions on that branch were observed before writing. Repository push permission was confirmed. The math source was created only under the new dedicated docs/source-only directory at commit 1c85e709d9fe367d89d89dee0806731883789376. GitHub read-back returned blob c2db8ef615c07e63e88924d80b83dea88d04dd46 with exactly 258 lines, and compare showed only this file +258/-0, ahead one, behind zero at the math commit.

Static text checks found no sorry/admit/axiom/unsafe and balanced parentheses. These checks do NOT constitute Lean parsing/elaboration or proof verification. Local command checks found git but **not** lean, lake or elan; direct git ls-remote failed with github.com DNS resolution. No fixed import closure is installed in the execution container. The available GitHub connector has read/write contents but no supported targeted CI module build dispatch. The existing push-triggered variable-envelope workflow is not a proof check of this new source-only module.

Thus: NO Lean/Lake success, NO kernel replay, NO transitive axiom audit, NO finite certificate replay. All four new theorem bodies are UNCOMPILED candidates, and no green status is assigned. No dependency, production file, P1.4, P3.6, CI configuration, manuscript, c/K, root norm 7/2, row norm 12, alpha, same-Q or 430+11 scope was changed.

**完整h34稿内证明仍未闭合。**
