# P5.6 / h34 — actual physical source debt on the ORIGINAL U3/U4 p bands

Date: 2026-11-11. Repository: UyNewNas/goldbach-formalization.
Branch: `chatgpt/p5-h34-actual-nexttable-signed-source-residual-20261109`.
Incoming HEAD: `9d70d94fc3a4f87bfbaa9250995804fe8597fcf8`.
New mathematical source commit: `9bf2503f642398602871c1b0df3e2ffe9909e049`.
Lean source blob: `9f153e249f51c393f82fd398ab33ea8240334bb1`.
New source: `Part5OriginalH430OriginalPrimeBandPhysicalGap.lean`, 197 lines, four definitions and four candidate theorem declarations.

Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@`ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`.
Pinned Lean `v4.33.0-rc1`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**.

## Genuine manuscript-internal increment

The previous packet `Part5OriginalH430PhysicalJointSourceDebt` gave one real physical successor-minus-previous-row residual at each winning bank/Buchstab Fin position and one selected-row error for a fixed original root, p and generation. It did **not** connect that local bound to the manuscript's true original U3 and U4 prime selectors.

The new source uses **existing** `originalBand N .U3` and `originalBand N .U4` without redefining either range. For each genuine original (root,p), the caller's `depth root p : Fin 430` picks a level of the existing request history; it supplies neither a free source identity nor any count bound. All `rootQ N n root tau p` values remain root/p-dependent.

- `actualRootPhysicalClosedCellGap` is the literal prior `levelReadMass-levelChildMass` minus the existing same-Q ideal child-account expression.
- `actualOriginalU34PhysicalSourceDebt` sums actual per-Fin-position physical source residual masses over the TWO original prime bands separately.
- `actualOriginalU34SelectedRowError` sums the previously proved local selected-row errors exactly once per original (root,p) level.
- `actualOriginalU34PhysicalClosedCellGap` is the signed original-prime-band sum of literal local closed-cell discrepancies.
- `actual_root_physical_closedcell_gap_abs_le` directly instantiates the preceding actual physical joint-source theorem, with no extra hypothesis.
- `actual_original_u34_physical_source_debt_nonneg` proves the finite source debt nonnegative.
- `actual_original_u34_physical_source_overlap` proves the exact **U3-exclusive plus U4-overlap** split. Every p in original U4 appears separately in the U3 and U4 physical histories; their Q, generation and marks are not identified, and the U4 contribution is NOT silently reduced to one paid history.
- `actual_original_u34_physical_closedcell_gap_bound` bounds the absolute signed outer p-band mismatch by the original-band physical source debt plus the old selected-row error. It uses the absolute-sum estimate on each original p band and one outer triangle inequality; no claim is made that the two residual totals are small.

This is a concrete **outer original-prime-selector correspondence** for the physical feedback ledger. It is NOT an original q/tag selected-count identity, a proof of root norm 7/2, or a paid H430 final-family bound.

## Still genuinely open

1. Identify original U3/U4 q/tag receipt owner, multiplicities, true root count weights (including norm 7/2), and full/selected/inherited count filters. U4 two-tag overlap still requires a valid history capacity and collision payment.
2. Prove the actual physical successor-minus-old-row residual quantitatively small from the original base, switched, seed, floor, and CLOSED-CELL induction; the present result just sums actual debts.
3. Pay six rejection lanes, signed Euler first-excluded suffix, native-history mass and original outer Theta/count connection without double charging.
4. Instantiate the genuine manuscript PP/same-rho integrals, implement a single common causal 430+11 refinement, and verify the frozen c/K, true alpha and row norm12 without changing them.
5. Stage pinned source-only import closure and target compile all new and inherited dependencies; kernel replay, transitive axiom audit and finite certification are also pending.

## Engineering validation and ownership

The repository connection grants push permission, and the new source commit was based on the verified dedicated h34 branch HEAD. Only a new source-only .lean file was added by the mathematical commit; source blob `9f153e249f51c393f82fd398ab33ea8240334bb1` was read back. No older file, other task, manuscript, CI setting, toolchain or master branch was changed.

This runtime has Git but `github.com` native Git resolution failed and Lean/Lake/Elan plus the pinned import installation are absent. Separate core CI run `43000225257` was in progress and is **not** a proof or build of this source-only module. No new heavy CI dispatched. Static code scanning showed no Lean proof escape placeholders, but it is NOT parsing, compilation or kernel evidence.

Actual Lean/Lake compile: **NOT EXECUTED**.
Kernel replay: **NOT EXECUTED**.
Transitive axioms: **NOT AUDITED**.
Finite430 certification: **UNEVALUATED**.
New green credit: **ZERO**.

Next precise action: stage original pinned imports and compile this module plus its direct dependency closure; repair genuine errors before any green claim. Then connect the two actual U4-tag physical debts to the original q/tag receipts and root weights using true owner/capacity, not an assumed count equality.

**完整h34稿内证明仍未闭合。**
