# P5.6 → h34: genuine selected-bank positive pre-floor to original CLOSED-CELL fixed reference

Date: 2026-11-18 (Asia/Shanghai). Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Verified prior head: `1ece19e2e7f183a5aba166f8e81c439073595e35`. Mathematical source commit: `acb6f247946365ac8be3586b1aa84a3e26c5faea`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean: `leanprover/lean4:v4.33.0-rc1`; Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual mathematical source increment

New candidate module: `Part5OriginalH430ClosedCellPositivePrefloor.lean` (238 lines, two definitions, seven theorem declarations; source blob `fcf2682c3c67b721fe253081072615881a31a2f0`).

The previous packet established a clipped feedback-floor credit at the *actual selected* original 106-bank Fin occurrences but left an unbounded positive pre-floor excess. This increment uses the **original preceding-generation query-cell closed-cell premise**, not an arbitrary owner or a global signed-error cancellation, to transfer that positive excess pointwise:

- `closedCellPreFloorAtom` retains the same rootQ, true parent Theta, original base value, ideal per-product (unrounded) feedback, and ideal cell profile. It replaces *only* the old-array fixed read by `fixedReference F a`, whose W1 anchor and W2 physical 4:1 formula is already fixed in the original module.
- `preFloorAtom_le_closedCellPreFloorAtom` uses the actual fixed-cell producer's one-sided lemma `selected_fixed_reference_upper` and nonnegative Theta.
- `bank_prefloor_le_closed_cell_positive` applies the monotonicity of `max 0` **at each selected history position**, then multiplies by its true nonnegative `levelMark`. Thus no signed aggregate is incorrectly converted into a positive-part upper.
- `bank_literal_plus_credit_le_closed_cell` combines the prior exact Q80/floor-credit path with this one-sided closed-cell substitution.
- `frozen_root_le_closed_cell_positive_with_credit` performs the same substitution over precisely 430 generations of the frozen genuine root request, keeping the zero-generation seed, Buchstab source, applied bank row error and capped Q80 credit.

The global source consumer explicitly requires, for each real `g : Fin 430`, `floorValue (iterate g.val true) i ≤ F s` for `s ∈ queryCell i`. **This predecessor CLOSED-CELL induction remains unproved and manuscript-internal.** The new theorem does not assume the h34 conclusion or equate the feedback request tree to the entire original U3/U4 count-source.

## Quantitative anti-over-credit guard

`bank_credit_le_original_rounding` proves the clipped credit is no larger than the **literal original per-product rounding loss**, using `min (max 0 X) Y ≤ Y` at every winning Fin position. `bank_credit_le_original_product_envelope` transports the existing exact divisor and Q80 length envelope. `frozen_430_credit_le_product_envelopes` sums that upper bound over the true 430 generations. No deduplication of repeated integer products, 106 bank actions, or duplicate paths is permitted.

These are *ceilings* on usable floor credit, NOT lower bounds; an upper bound on the credit must not be subtracted from the debt as though it were guaranteed payment.

## Engineering and scope

The branch head was checked at `1ece19e2e7f183a5aba166f8e81c439073595e35` immediately before mutation. Only a new task-owned source-only directory/file was written at `acb6f247946365ac8be3586b1aa84a3e26c5faea`; its blob and exact 238 lines were re-fetched from GitHub. Static prohibited-proof-token scan found no `sorry`, `admit`, added `axiom`, `unsafe` or `native_decide` in the new candidate. The repository itself contains many other source-only packets; no pre-existing or other task's file was rewritten.

The available execution container has `git` but does NOT have `lean`, `lake`, or `elan`. Native `git ls-remote` failed to resolve `github.com`; the pinned source-only import closure is not present in the local container. GitHub connector can read/write source but does not run Lean or dispatch a named Actions job. No actual Lean/Lake elaboration/compilation, kernel replay, transitive axioms audit, finite 430 replay or closed-cell induction was run. **Seven declarations are UNCOMPILED candidates; zero green nodes.** Static source inspection and remote hashes are not formal verification.

The pinned manuscript, existing c/K, root norm 7/2, row norm 12, same Q, true alpha, original action resolver, specified-cell/scalar difference, repeated occurrence and payment multiplicities, Q80 divisor and 430+11 budget remain unchanged. No new external analytic input, sorry, admit, axiom, CI setting, dependency upgrade, branch merge or force push.

## Real remaining manuscript obligations

1. Prove the predecessor `hcells` through a proper **base/seed and CLOSED-CELL induction**, including original W1 anchors, W2 4:1 fixed read, switched and final Q80 floors. This packet only proves the correct nonlinear propagation *given* that predecessor bound.
2. Pay the new closed-cell **positive** base + fixed(F) + ideal-feedback − same-Q ideal-profile excess quantitatively. Existing signed estimates alone do not pay it. Check PP/same-rho source, original integrals, and all quantifiers/thresholds without moving the manuscript's own proof obligations outside.
3. Pay the true winning Buchstab strict-prime positive physical source, terminal zero-generation seed, and the already separate applied error in the correct total budget; do not count upper floor-credit envelope as positive payment.
4. Match the generated same-Q root request bound with the entire original U3/U4 full/selected/inherited count-source: owner, original root factor 7/2, q/tag duplicates and rejection paths, signed Euler/native-history quality, integral–Theta–count, and joint 430+11 causal refinement.
5. Restore pinned Lean/Lake source-only imports locally or in an allowed existing CI job, compile this module and dependency chain, then perform kernel replay, transitive axiom audit, and any required finite checks. No green state before these succeed.

Next concrete action: inspect the pinned `idealCellProfile` against `baseValue + fixedReference F + idealFeedbackValue` on the original 106 selected positions and seek a real bound for its **pointwise positive** gap; independently reconstruct the import closure to run targeted compilation. Do NOT continue generating alternate copies of the same signed ledger.

**完整h34稿内证明仍未闭合。**
