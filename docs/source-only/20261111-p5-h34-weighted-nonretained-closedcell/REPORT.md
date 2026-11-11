# P5.6 / h34 — physical weighted nonretention CLOSED-CELL defect

Date 2026-11-11; repository UyNewNas/goldbach-formalization.
Verified incoming HEAD: `8f94800f4b8abea131da2bb2ed63fa413b2a648d`.
Mathematical source commit: `4dfb5fb89eb62c097401d6b627b2ec95c26f519b`.
Branch: `chatgpt/p5-h34-actual-nexttable-signed-source-residual-20261109`.
Module: Part5OriginalH430ActualWeightedNonretainedClosedCell.lean, 192 lines; Git blob f160f2b5b13837635d823b87f06ebdf757a9b69a.
Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766, paper/source/manuscript-body.tex.
Fixed toolchain Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**

## Actual increment

This packet does not repeat the old 12Theta/5Theta row estimates, or invent new analytic inputs. Instead it connects genuine physical `levelReadMass - levelChildMass` to selected old-array rows and to both real new-table source gaps, using the immediately preceding exact retained Theta cancellation. Six NEW candidate proof bodies:

1. `actual_nonretained_theta_correction_abs_le_payment`: establishes a genuine two-sided absolute estimate for the actual Buchstab/bank Fin-position Theta correction; previously only a one-sided lower bound had been written.
2. `actual_weighted_nonretention_read_exact`: proves the exact signed physical identity
```
levelReadMass - retainedLevelValue =
  actualSelectedOldRead + actualBankSourceGap
  + actualBuchstabSourceGap + actualNonretainedThetaCorrection.
```
3. `actual_weighted_nonretention_same_q_defect_exact` and `actual_weighted_nonretention_same_q_defect_bound`: subtract the actual SAME-Q fixed-cell/Buchstab ideal, preserving separately both unpaid source gaps and the nonretention Theta payment. Exactly one existing selected coefficient error is used.
4. `actual_weighted_closedcell_ideal_defect_exact` and `actual_weighted_closedcell_ideal_defect_bound`: rewrite this source/ideal discrepancy against the real `levelReadMass - levelChildMass`, with nonretention child balance `levelChildMass - retainedLevelValue`; no free child-count source or inferred full selected owner.

The resulting candidate estimate is
```
|(levelReadMass - levelChildMass) -
  (actualSelectedSameQIdealRead -
   (levelChildMass - retainedLevelValue))|
<= |actualBankSourceGap| + |actualBuchstabSourceGap|
 + actualNonretainedThetaPayment + actualSelectedError.
```
This does NOT prove the bank/Buchstab source gaps or nonretained payment small, nor the U3/U4 original count-source identity, the actual preceding CLOSED-CELL induction, PP/same-rho, or common430+11 closure.

## Scope, concurrency, verification

The first request-admission and latest 20261111 retained-cancellation REPORT/REGISTRY/EXTERNAL_INPUTS and exact source were read; latest dedicated branch SHA checked before writing. New files only in this task-owned directory. A separate branch had Lean core CI 42983649029 in progress; no CI dispatched or modified. No P1.4/P3.6, production modules, pinned manuscript/toolchain, c/K, root norm7/2, row norm12, real alpha or physical Q changed.

Local runtime has neither Lean/Lake/Elan nor fixed source-only import closure, and native GitHub Git DNS resolution fails. GitHub source blob and commit were read back; no Lean parsing/elaboration/compilation, kernel replay, transitive axiom audit or numerical430 was executed. Static checks are NOT Lean validation; six declarations are uncompiled candidates and every finite certificate is UNEVALUATED. No green formal credit.

## Outstanding manuscript-internal proof obligations

- Derive a useful count-side upper for actual nonretention Theta payment and genuine bank/Buchstab new-table gaps from TRUE U3/U4 q/tag owners, not an assumed licence.
- Prove original full/selected/inherited filtering, root weights, six rejection classes, cross-q/tag collisions, signed Euler payment.
- Close preceding CLOSED-CELL base/switched/seed/floor induction with correct Q80 rounding signs.
- Connect manuscript PP/same-rho, native-history mass, outer integral/Theta/count and one common430+11 nested refinement.
- Stage the held import chain; run pinned Lean/Lake, kernel replay, axiom audit, and finite numerical430 certification.

Next: trace actual `levelChildMass - retainedLevelValue` and actual selected winning positions to original U3/U4 q/tag count-owner receipts, preserving unmatched masses; compile this newest module when its fixed dependencies are staged.

**完整h34稿内证明仍未闭合。**
