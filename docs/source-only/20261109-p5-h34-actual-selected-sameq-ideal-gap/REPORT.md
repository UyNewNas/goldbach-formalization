# P5.6 / h34 — actual selected same-Q physical-to-ideal read comparison

Date: 2026-11-09.
Repository: UyNewNas/goldbach-formalization.
Branch: chatgpt/p5-h34-actual-selected-sameq-ideal-gap-20261109.
Verified incoming h34 HEAD: 8f5fc98fd81d0b359fd781f959475693febcdbbc (not the initial 0a3fa5a entry).
Mathematics commit: db2c1baa475c7c2f9c0004afad28b8989d1b4f6f.
Source: Part5OriginalH430ActualSelectedSameQIdealGap.lean.
Source Git blob: 91b1d474aae1963fb340855b6cefb70c022c1ccc.
5 Lean theorem *candidates*, 3 definitions.

**PARTIAL_SOURCE_INCREMENT — SOURCE_ONLY — UNCOMPILED — UNEVALUATED — FULL_H34_OPEN.**

## New manuscript-internal proof candidates

The prior predecessor-array stability packet compared the true selected physical feedback row against an arbitrary vector. This packet **defines the particular ideal read from the original actual-choice winners**, rather than renaming an unconstrained vector "analytic".

For the original 106 bank slots, each selected Fin list occurrence contributes its literal
  levelMark * thetaAtom N (rootQ N n root tau p) (parentProduct old) * cellReadIdeal action rowAtom,
applied to the original precedingH/precedingh oldAtomValue array. For actual Buchstab winners, the corresponding source is
  levelMark * thetaAtom N (rootQ N n root tau p) (parentProduct old) * integralRow current.node.upper current.node.physical rowAtom,
applied to that **same** original old array. Neither term uses an unselected bank choice; scalar and specified-cell action winners remain distinct.

New statements, in the exact source:

1. marked_row_read_gap — finite marked-row signed comparison, with only nonnegative original-position marks, no positivity assumption on old atom values.
2. actual_bank_same_q_ideal_gap — the original 106 bank physical-to-fixed-read signed difference is bounded by the existing actualBankError (summed over true winning slots).
3. actual_buchstab_same_q_ideal_gap — the physical Buchstab difference to the literal upper/physical integralRow is bounded by existing actualBuchstabError.
4. actual_selected_same_q_gap_le_error — the union of both true winning families satisfies
     |actualSelectedOldRead - actualSelectedSameQIdealRead| <= actualSelectedError.
   No second independent absolute-error charge is added.
5. uniform_actual_selected_same_q_gap — one N-threshold chosen before n, root, tau, p, and g gives
     |actualSelectedOldRead - actualSelectedSameQIdealRead| <= epsilon * actualSelectedTheta.
   The underlying bank 12Theta and Buchstab 5Theta mass allowances remain separate.

Three literal ideal-read definitions are used: actualBankSameQIdealRead, actualBuchstabSameQIdealRead, and actualSelectedSameQIdealRead. The same rootQ is used within each root's physical and ideal components; this **does not** assert equality of rootQ between different roots.

## Boundaries and remaining internal obligations

This is a genuine selected **feedback-row comparison**, not a closure of the U3/U4 original arithmetic count source, and the defined target does not yet identify the original analytic integral as the manuscript-local PP/same-rho consumer. Further proof is needed to connect fixed-read cell integrals, floors, switched terms and original seed/base to that target, including correct q/tag and root owner multiplicities.

Still open:
- the correct predecessor absolute norm/base/seed/floor growth estimate over actual generations, and the full all-action arithmetic CLOSED-CELL successor induction;
- original U3/U4 selected-count source, root weights, full/selected/inherited gates, owner and all six rejection lanes, including physical-key collision payment;
- genuine manuscript PP/same-rho compatibility, native-history proper/equality/inherit mass, outer integral-to-Theta-to-count comparison and one common 430+11 nested causal refinement.

The original c/K, root norm 7/2, bank norm 12, Buchstab 5Theta, alpha, positive marks, same-root Q, and generation g+1 versus predecessor g distinction are unchanged. No target-equivalent assumption, sorry/admit, custom axiom, or unsafe/native proof escape is introduced. No new genuinely external analytic theorem.

## Pinned version and validation

Manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766
(current proof mapping's paper/source/manuscript-body.tex; no switch to later manuscript).
Lean: v4.33.0-rc1.
Mathlib: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Repository GitHub write permission was confirmed, the independent h34 branch was created from the verified previous HEAD, and the mathematical commit and source blob were read back. Static declaration/forbidden-token checks are not Lean verification.

The local execution environment has no lean/lake/elan, no staged dependency-complete source-only import closure, and native GitHub git cannot resolve github.com. No targeted Lean/Lake compilation, kernel replay, transitive axiom audit, or finite numerical certificate replay was executed. CI was not dispatched; do not infer success from any unrelated CI run. Every statement stays UNCOMPILED and UNEVALUATED. No green node.

Installation only after the original frozen dependency sources are staged:
  ImbalancedChen/Part5OriginalH430ActualSelectedSameQIdealGap.lean
with import ImbalancedChen.Part5OriginalH430ActualPredecessorAbsStability.

Next: install the pinned import closure and compile just this module plus dependencies; repair actual Lean elaboration errors if any. Then prove the genuine manuscript same-rho/floor/seed integral correspondence for this newly defined actual target, and integrate the result into original U3/U4 owner-aware CLOSED-CELL arithmetic induction.

**完整h34稿内证明仍未闭合。**
