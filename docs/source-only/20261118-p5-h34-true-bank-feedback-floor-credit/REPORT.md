# P5.6 → h34: true selected-bank feedback-floor credit under positive parts

Date: 2026-11-18 (Asia/Shanghai). Working branch: chatgpt/p5-h34-full-tagged-actual-fin-20261112.
Prior verified HEAD: c46960582520d79b0e3f78938f7460586fcc93f3.
New mathematical source commit: b32d22009623eae27969c0aaf5c2af0c1b2dceae.
Fixed manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766.
Fixed Lean: leanprover/lean4:v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual new proof-source increment

New source: Part5OriginalH430TrueBankFeedbackFloorCredit.lean (245 lines, 4 definitions, 6 public theorem declarations and 1 private supporting theorem).

Prior work had connected the true selected bank request to its literal original Q80 candidate, then bounded that by the old real base+fixed+feedback candidate, leaving a positive bank read–ideal surplus. The older original per-product quotient/remainder packet established:
  idealFeedbackValue(old,a) = feedbackValue(old,a) + feedbackRoundingLoss(old,a)
and proved nonnegative actual Euclidean feedback rounding loss, with original per-product divisions and the action's original W1/W2 divisor.

This increment **combines the two existing actual-source chains** at each ORIGINAL selected Fin occurrence, with root-specific SAME-Q Theta and unmodified positive marks. Let
  X = theta * (baseValue + fixedValue + idealFeedbackValue - idealCellProfile)
  Y = theta * feedbackRoundingLoss >= 0.
The old real candidate's signed physical gap is exactly X - Y. The new private algebraic proof and atom theorem establish:
  [X-Y]_+ + min([X]_+,Y) = [X]_+.
The cap is essential: subtracting all Y from a positive-part bound can over-credit a position with insufficient positive gap. No aggregate signed cancellation can substitute for this pointwise result.

The original 106 winning-bank Fin-level sum now has an exact *clipped* floor credit:
  bankRealCandidateIdealExcess + bankFeedbackFloorCredit
    = bankPreFloorIdealExcess.
Because the true selected integer-Q80 read is at most the old real candidate, and its parent Theta is genuinely nonnegative:
  bankLiteralQ80IdealExcess + bankFeedbackFloorCredit
    <= bankPreFloorIdealExcess.
The new nonnegative-credit proof uses original levelMark positivity and genuine rootHistory geometry. These are proofs of algebraic source formulas, **not** proofs that the pre-floor gap is numerically small.

Finally the prior genuine root bound is strengthened to a candidate inequality with the full sum of 430 *actual* clipped credits on the LEFT:
  weightedRequest(root,430) + sum_{g<430} bankFeedbackFloorCredit(g)
    <= genuineZeroGenerationSeed
      + sum_{g<430} (buchstabPhysicalSource(g)
                      + bankPreFloorIdealExcess(g)
                      + bankPhysicalAppliedAbs(g)).
This keeps original rootQ, scalar/specified-cell distinction, selected 106 action, duplicate history positions and exactly one already-existing applied bank absolute error. It DOES NOT pay the pre-floor positive gap, and it does not identify request-level mass with original U3/U4 count-source.

## Imports and proof boundary

Imports: ImbalancedChen.Part5OriginalH430LiteralBankQ80PhysicalExcess and ImbalancedChen.Part5OriginalH430SelectedBankGlobalFloorBaseLedger.
Reused manuscript-local results: ideal_feedback_exact; feedbackRoundingLoss_nonneg; rootHistory_support; thetaAtom_nonneg; literal_q80_excess_le_real_candidate_excess; frozen_root_le_seed_buchstab_literal_q80_applied. No new external number-theoretic input and no rewrite of PNT/Mertens/BV.

The original c/K, root norm 7/2, row norm 12, actual alpha, same-Q, original Q80, per-product floor divisor, selected-cell/scalar distinction, original marks, 430+11 and pinned manuscript stay unchanged. No h34-equivalent premise, sorry/admit, custom axiom, unsafe or native-decide escape was added.

## Engineering reality

New source was created in the task-owned source-only folder on the continuing branch. GitHub returned commit b32d22009623eae27969c0aaf5c2af0c1b2dceae, the remote source blob af4f9a5ccad8df53223d5e7b6ba7e9638ab6294d was re-read and the remote diff confirmed 245 added source lines. Other task files, source files already committed, CI, dependencies and master were not touched.

The execution container was checked: lean, lake and elan are absent; original source-only imports are not installed in ImbalancedChen; native GitHub DNS resolution is unavailable. No usable Lean/Lake command was run; there is NO successful parse/elaboration/compilation, kernel replay, transitive axiom audit or finite 430-table replay. Text/static inspection is not formal verification. New statements remain uncompiled candidates, with zero green nodes.

## Still-open manuscript-internal obligations

1. Truly quantify the original pre-floor base/fixed/ideal-feedback-vs-ideal-profile *positive* excess; validate exact original candidate floor in the correct one-sided direction. This packet exposes a capped credit, not a numeric payment.
2. Actual Buchstab strict-prime positive physical-source, zero-generation seed, ordinary/fixed/switched base cases, original floor and CLOSED-CELL count induction.
3. Complete original U3/U4 full/selected/inherited count-source and owner, actual 7/2 root norm, q/tag repeated receipts and rejection paths.
4. PP/same-rho manuscript-local instantiation, signed Euler/native-history mass, integral–Theta–count identity and single causal 430+11 nested refinement.
5. Reconstruct pinned source-only import closure; incremental Lean/Lake compile, kernel replay, transitive axiom audit and finite certifications.

Next action: identify the real pre-floor surplus with original actual base/fixed and analytic ideal-feedback integrals **without replacing its positive parts by a signed aggregate**; check whether old floor, seed and PP inputs pay it under true selected owners. In parallel, reconstruct the pinned import closure and run targeted Lean compile before awarding green credit.

**完整h34稿内证明仍未闭合。**
