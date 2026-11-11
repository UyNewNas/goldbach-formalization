# P5.6 / h34 — one actual physical joint source debt at winning Fin positions

Date: 2026-11-11. Repository: UyNewNas/goldbach-formalization.
Dedicated branch: `chatgpt/p5-h34-actual-nexttable-signed-source-residual-20261109`.
Incoming remote HEAD: `d16002752a5e7942eba6bf9f513eae838bb06505`.
New Lean source blob: `793c050f72b7332eee8bc421054ff781d503c734` (209 lines, 1 definition, 5 public theorem candidates and 1 private real-algebra lemma).
Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@`ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`.
Pinned toolchain Lean `v4.33.0-rc1`; pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual new manuscript-internal mathematics

The immediately preceding packet `Part5OriginalH430JointPositionSourceGap` obtained an actual new-table/old-row source residual (bank+Buchstab jointly), whereas `Part5OriginalH430ActualRetainedThetaCancellation` established a separate nonretention normalization debt. Both originate from the **same** actual selected bank/Buchstab Fin position. Keeping them as two separate absolute payments unnecessarily loses termwise signed cancellation.

The current candidate packet uses the literal identity
[
(V_{g+1}-R_g)+(Theta-1)V_{g+1}=Theta V_{g+1}-R_g.
]
Its `readTerm` is the original physical Theta-weighted request, and `R_g` is the original selected `edgeRow` applied to `oldAtomValue (precedingH g) (precedingh g)`. The summation includes *every actual winning Fin position* and its real `levelMark` without quotienting duplicate physical products or inventing a q/tag owner.

- `actualPhysicalJointSourceResidualMass`: sum of `|levelMark| * |readTerm - oldRow|` over actual bank/Buchstab winners, excluding already-cancelled retention.
- `actual_physical_joint_source_residual_nonneg`: nonnegativity.
- `actual_joint_physical_gap_eq_position_residuals`: exact equality between *joint signed* bank/Buchstab source gaps **plus** nonretention Theta correction and the single physical successor-minus-old-row occurrence sum.
- `actual_joint_physical_gap_abs_le_position_residuals`: termwise absolute bound using that single occurrence sum.
- `actual_physical_joint_source_le_separate_debts`: this new physical budget is at most the prior separate `actualNonretainedSourceResidualMass + actualNonretainedThetaPayment`; no extra cost.
- `actual_weighted_closedcell_physical_joint_source_bound`: the actual `levelReadMass-levelChildMass` discrepancy from the already-defined same-Q selected ideal is bounded by the new joint physical residual plus **one** existing `actualSelectedError`.

This is a **strictly better accounting form**, in the sense of a universally no-larger upper envelope, not an assertion of strictly smaller numerical value, a new count theorem, or a proof of a small residual. It is still conditional on correctness of imported source-only candidate lemmas, which remain uncompiled.

## True open manuscript-local obligations

1. Establish an original U3/U4 owner and quantitative upper bound for the remaining **physical joint successor-minus-previous-row** residual. Prove genuine base/switched/seed/floor/closed-cell recursion, not a new arbitrary smallness hypothesis.
2. Connect actual full/selected/inherited count filters, root weights (7/2), full original count owners, true alpha and physical Q; pay all six rejection lanes, first-excluded signed Euler suffix, q/tag collision/overlap, with multiplicity.
3. Complete original manuscript-local PP/same-rho compatibility, native-history mass, outer Theta/count/integrals and a common causal 430+11 refinement.
4. Compile pinned source-only modules and their dependencies; execute kernel replay, transitive axiom audit and finite certification. No source-only claim is green without these.

## Validation and ownership

The original repository metadata grants push permission; the existing h34 work branch was checked against incoming HEAD immediately before publication. No earlier h34 files were overwritten. This packet adds a new `.lean`, this REPORT, REGISTRY, and EXTERNAL_INPUTS, and does not touch production, CI, P1.4/P3.6, master, manuscript or dependency versions.

No Lean/Lake/Elan executable or staged pinned source-only import closure is present in this execution environment. No actual Lean/Lake compile, kernel replay, transitive-axiom audit or finite430 certification was run. Source examination and GitHub blob/commit readback are not compilation evidence. New external analytic inputs: NONE.

**Next exact action:** stage and compile the pinned direct import closure; resolve genuine type/proof failures. Then derive genuine original U3/U4 q/tag owner and count-side physical source control, preserving all occurrences and seed/floor deductions. No free residual smallness or hidden additional Theta payment.

**完整h34稿内证明仍未闭合。**
