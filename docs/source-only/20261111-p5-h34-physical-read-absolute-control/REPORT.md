# P5.6 / h34 — original nonretention physical read absolute control

2026-11-11. Repository: UyNewNas/goldbach-formalization.
Branch: `chatgpt/p5-h34-actual-nexttable-signed-source-residual-20261109`.
Verified incoming HEAD: `a7d2d612406e134ae33a4fa3f1d030301cd821e7`.
Mathematics candidate commits: `c850475e496e10a690a11d7b4093ba47c41bc545` (original source) and `d94ef44e20ac944651910320ca40b8aa3fc5060a` (namespace-source correction); corrected source blob: `9e7d8b2703300be869b2d7ef9f5e67ab58bf873b`.
Module: `Part5OriginalH430PhysicalNonretainedAbsoluteControl.lean` (184 lines, 4 definitions, 7 theorem declarations including one private real absolute-value helper).
Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@`ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`.
Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## This increment: expose genuine physical reads, not a free payment

The previous packet left the nonretention correction
`actualNonretainedThetaCorrection` with a nonnegative, but not small,
absolute payment `actualNonretainedThetaPayment`. It had not identified
a legitimate source controlling this payment.

At precisely the actual generated Buchstab and original 106 bank winning
Fin positions, this packet defines the *signed* original physical
Theta-weighted and unweighted table reads, plus each corresponding
termwise absolute read mass. Retention is absent, already cancelled
against the actual child, and no physical products are deduplicated.

New candidate identities and estimates:

1. EXACT signed physical-minus-unweighted reading:
   `C_nonret = R_physical_nonret - R_unweighted_nonret`.
2. Both real absolute read masses are nonnegative, without assuming
   the sign of any rounded table entry or Theta-1.
3. Termwise `|Theta-1| <= |Theta|+1` yields
   `P_nonret <= A_physical_nonret + A_unweighted_nonret`.
   The physical absolute term uses the ORIGINAL `readTerm`, including
   real root-specific physical Q and every actual occurrence mark.
4. Consequently `|C_nonret| <= A_physical_nonret + A_unweighted_nonret`.
5. The genuinely physical `levelReadMass - levelChildMass` SAME-Q
   ideal defect bound now explicitly exposes these two actual reads,
   BOTH still-unpaid new-table source gaps and the existing selected
   coefficient error. No second charge for retention or row error.

This is a source-identification/absolute comparison, not a proof that
either absolute read is small or a replacement original U3/U4
selected-count owner. It does not convert absolute physical mass to
true arithmetic q/tag receipts. The bank/Buchstab new-table source
gaps, nonretained child counts, original base/switched/seed/floor
and full/selected/inherited root owner remain open.

## Source and validation

Read the original 20261105 admission REPORT/REGISTRY/EXTERNAL_INPUTS,
the previous 20261111 weighted nonretention packet and its source,
the actual `ActualReadEdgeDefect`/`AllActionOccurrenceSource` kernels,
the already existing original U3/U4 q/tag source and upper H430
lookups before writing. No P1.4/P3.6, production source, CI workflow,
toolchain, parameters or manuscript mapping changed.

The GitHub connector confirmed push permission and read the exact
source blob and math commit back. Compare from incoming HEAD to math
commit: one additive 184-line Lean file, zero deletions. Text scan:
no `sorry`, `admit`, new `axiom`, `unsafe` or `native_decide`.
These checks are not Lean compilation or kernel verification.

The runtime has no lean/lake/elan executable, the local GitHub
clone cannot resolve github.com, and the fixed source-only import
closure is not installed. Existing separate compile repair CI run
42989742397 was in progress, so no new heavyweight build or unrelated
CI workflow was launched. No Lean/Lake compiler success, kernel replay,
transitive axiom audit or finite430 certificate replay can be claimed.
Every candidate remains UNCOMPILED, all inherited finite guards
UNEVALUATED, and no GREEN status is earned.

## Remaining genuine manuscript-internal work and next action

1. Match the ACTUAL nonretention physical absolute read to a sound
   original U3/U4 selected-count source and owner, with authentic root
   weight, full/selected/inherited masks and original q/tag
   multiplicities. The absolute bound here is not yet a counting bound.
2. Pay/bound the two new-table source gaps and actual nonretention
   physical absolute masses at the correct base/seed/floor and
   previous-cell CLOSED-CELL induction. Do not introduce a free
   smallness hypothesis or charge any one mark twice.
3. Pay six original rejection classes, U4 q/tag slot collisions and
   signed Euler receipts, then finish PP/same-rho, native-history,
   outer Theta/count and one common 430+11 causal refinement.
4. Stage the pinned source-only import closure and incrementally
   compile this module with dependencies, repair actual Lean errors,
   kernel replay, audit transitive axioms and replay finite guards.
5. No new genuinely external analytic input. Old PNT/Mertens/BV
   interfaces, exact c/K, root norm 7/2, row norm 12 and original
   true alpha are unchanged.

**完整h34稿内证明仍未闭合。**
