# P5.6 → h34: exact original anchor defect instead of a supplied bound

Date: 2026-11-18 (Asia/Shanghai).
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Actual predecessor HEAD: `60532586028722f78c4c84bb5be93b9d8e613a25`.
Mathematical source commit: `92865fc6fbc06a0fc958e37ac8d492db5043cbe4`.
New source: `Part5OriginalH430ExplicitAnchorDefect.lean`.
Git blob: `85a61c89a23e8055829235594ca15870dbddeb37` (214 lines).
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned toolchain: Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Exact manuscript-internal increment

The preceding FixedAnchorSlackPayment packet had identified the precise original fixed-read slack but required the caller to supply an independent `FixedAnchorUpper g F (delta g)` proof. This packet eliminates that additional hypothesis without pretending the budget is small.

Define three FINITE REAL maxima at the literal preceding Q80 table, over the original 10 W1, 36 W2-first and 36 W2-second endpoint appearances. For each generation g:

- `w1AnchorDefect g F` is the exact maximum of F(W1Anchor j) - floorValue(precedingH g)(w1Cell j).
- `w2FirstAnchorDefect g F` and `w2SecondAnchorDefect g F` are exact maxima of the two ORIGINAL W2 endpoint/table differences.
- `actualAnchorDefect g F := max 0 (max W1 (max W2-first W2-second))`.

The three original index domains are nonempty; `Finset.sup'` is used with an explicit nonempty witness. This has exactly 82 anchor APPEARANCES and does not quotient overlapping physical values, resample endpoints, change W2 4:1 coefficients or create an adjustable error.

Candidate proofs establish:
1. `actualAnchorDefect_nonneg`;
2. each original W1 and W2 endpoint deficit is at most its genuine finite maximum;
3. `actualAnchorDefect_supplies_upper`: the previous packet's `FixedAnchorUpper` predicate holds for this concrete defect, with no extra source hypothesis;
4. `actualAnchorDefect_le_any_nonnegative_upper`: this is the LEAST NONNEGATIVE uniform anchor allowance satisfying all original endpoint bounds, ruling out an unjustified smaller delta;
5. `bank_fixed_slack_le_actual_anchor_defect`: the same true winning selected-bank Fin positions, same-Q Theta and positive original history marks are paid by `actualAnchorDefect g F * bankSelectedTheta g`;
6. `frozen_root_le_actual_anchor_defect_budget`: substitute the concrete defects at all 430 generations into the prior real-root bound. The previous independent `hanchor` hypothesis is absent; the predecessor CLOSED-CELL `hclosed` remains explicit.

This is a strictly stronger dependency statement than the previous conditional root consumer: the additional arbitrary finite-anchor upper certificate is no longer required. It is NOT a numerical estimate of the defects, a h34 proof, or a substitute for completing the actual original table induction.

## Manuscript-internal remaining obligations

- Obtain a usable quantitative estimate for the now explicit maxima from the true previous integer table, seed, original Q80 recurrence and both-sided anchor comparisons. The earlier one-sided CLOSED-CELL majorant cannot make the excess small.
- Close the actual base/fixed/switched/seed/floor CLOSED-CELL induction and correctly pay positive dynamic `base + idealFeedback - dynamicIdeal` imbalance.
- Pay strictly-prime Buchstab positive physical source and correct zero-generation seed.
- Complete original U3/U4 root count-source identity, full/selected/inherited owner, root weight 7/2, q/tag multiplicities, rejection lanes and signed Euler/native-history.
- Complete manuscript-local PP/same-rho instantiation, outer integral–Theta–count correspondence and ONE common nested 430+11 causal refinement.
- Compile this module and the pinned import closure, then run kernel replay, transitive axiom audit and finite certificate replay before marking anything green.

## Validation and ownership

The source was committed to the existing dedicated h34 branch with a fast-forward and expected-SHA check, read back by its Git blob, and compared to the exact predecessor. No P1.4/P3.6 file, master, dependency, CI setting or workflow was modified. Before writing, branch HEAD matched the predecessor and no queued/in-progress Actions runs were reported on this branch.

Local environment check: `git` is available, but `lean`, `lake` and `elan` were not on PATH, and the pinned source-only import closure was not installed. The connected GitHub tool can modify repository content but supplies no targeted Actions dispatch/Lean execution. No actual compile ran; there is no kernel replay, transitive-axiom audit, or finite numerical certification. The static forbidden-token/delimiter checks and remote Git blob compare ARE NOT Lean proof verification. No green node was added.

**完整h34稿内证明仍未闭合。**
