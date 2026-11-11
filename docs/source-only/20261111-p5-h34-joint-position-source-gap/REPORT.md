# P5.6 / h34 — joint actual next-table source gap at winning Fin positions

Date: 2026-11-11. Repository: UyNewNas/goldbach-formalization.
Dedicated continuation branch: `chatgpt/p5-h34-actual-nexttable-signed-source-residual-20261109`.
Verified incoming HEAD: `f42327367596be0ea8c31c0510319057b23238a8`.
Mathematics source commit: `20e5c158be390fe45213702899342343c0b1ed76`.
Lean source blob: `447b39a0bd71ecfede1b3a795c7a1bddc17a0287`.
New file: `Part5OriginalH430JointPositionSourceGap.lean` (215 lines, one definition, five candidate theorems).

Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@`ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`.
Pinned Lean v4.33.0-rc1; pinned Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Why this is different from the previous physical-read absolute envelope

The predecessor `PhysicalNonretainedAbsoluteControl` exposed actual nonretention physical/unweighted absolute read masses but continued to pay `|actualBankSourceGap| + |actualBuchstabSourceGap|` as two unrelated numbers.

The two actual source gaps are signed and arise from the SAME generated generation. The new module identifies their **joint** sum precisely with the original actual bank-or-Buchstab winning Fin positions. Every position retains its real `levelMark`, its original selected request and read mode, true `rootQ`, true `children` and `edgeRow`, and the exact preceding `oldAtomValue` array. No position is quotiented by parent product, catalog label, or inferred q/tag owner.

New candidate declarations:

1. `actualNonretainedSourceResidualMass`: sum, over actual selected nonretention Fin positions, of the absolute marked difference between the new table value and the old selected row evaluated on the actual predecessor array.
2. `actual_joint_source_gap_eq_position_residuals`: EXACT signed identity: bank source gap **plus** Buchstab source gap equals the sum of those marked pointwise residuals (before absolute values). It uses the genuine original 106 bank positions and the existing selected-old-row winner-position identity.
3. `actual_nonretained_source_residual_nonneg`: the new mass is nonnegative.
4. `actual_joint_source_gap_abs_le_position_residuals`: `|delta_bank + delta_buchstab| <= actualNonretainedSourceResidualMass`, with no independent |delta_bank| + |delta_buchstab| charge.
5. `actual_weighted_closedcell_joint_source_bound`: the exact original `levelReadMass-levelChildMass` defect is bounded by the **joint signed** source gap, one pre-existing nonretention Theta payment and one selected row error.
6. `actual_weighted_closedcell_position_source_envelope`: replaces the unknown joint source gap by its actual termwise residual mass and the Theta payment by the two genuine physical/unweighted absolute read masses. This supplies a traceable finite position-level ledger, **not** a small error conclusion.

The signed combination is genuinely stronger than charging `|delta_bank|+|delta_buchstab|` separately when cancellations occur. The absolute residual mass is an upper bound only; this step does NOT establish any cancellation lower bound or prove that the mass is small.

## Precise still-open manuscript-internal mathematics

- Prove actual next-table/per-request residual mass is quantitatively controlled using the TRUE original base, switched, seed, floor and previous-cell CLOSED-CELL recursion; do not replace this with an arbitrary smallness hypothesis.
- Give actual physical/unweighted absolute nonretention reads a valid **original U3/U4** selected-count source with true root count weight, full/selected/inherited owner, original physical z0, q/tag multiplicity, and genuine selected positions. The current packet only identifies the local read source.
- Pay all six rejection lanes, overlapping U3/U4 q/tag appearances, collisions, signed first-excluded Euler receipts, true native-history source and Rosser constraints.
- Match same-Q bank/Buchstab local ideal to the frozen manuscript's PP/same-rho integral, outer Theta/count conversion and one common 430+11 causal nested refinement.
- No new PNT/Mertens/BV proof or analytic assumption. Original c/K, root 7/2, row 12, true alpha, Q and policy are untouched.

## Validation and code ownership

Authenticated GitHub connector reports repository push permission. Source commit was created on the existing dedicated h34 branch, then the original exact blob and GitHub compare were read back. Compared with the incoming HEAD: **one additive 215-line Lean file, no deletions**, forward by one commit. Text scan: no `sorry`, `admit`, new `axiom`, `unsafe` or `native_decide`. This is neither a Lean parser check nor a proof kernel check.

Checked local runtime: git exists but `github.com` DNS resolution fails; `lean`, `lake` and `elan` are unavailable and the source-only import closure is not staged in the original production source tree. Independent Lean core verification run `43000225257` is in progress on `ci/resume-compile-repairs-20261111`, but it is NOT a build of this new source-only module. No new heavyweight CI was initiated or CI settings changed.

Actual Lean/Lake compilation: **NOT EXECUTED**. Kernel replay: **NOT EXECUTED**. Transitive axiom audit: **NOT EXECUTED**. Finite430 certification: **UNEVALUATED**. New green credit: ZERO. All five new proof bodies are uncompiled candidates.

No production files, P1.4, P3.6, other task files, manuscript, pinned dependencies, workflow or master branch were modified. All changes are confined to this new source-only packet.

## Next exact action

After staging the pinned source-only dependency chain, compile `Part5OriginalH430JointPositionSourceGap` and repair genuine compiler errors. In parallel, identify the actual U3/U4 owner and a genuine preceding-generation recurrence for each selected request's table-minus-row residual, before trying to pay this finite mass. Do not assume the residual vanishes or that a parent product identifies an original arithmetic quotient q.

**完整h34稿内证明仍未闭合。**
