# P5.6 → h34: actual bank positive surplus versus physical row (2026-11-17)

Repository: UyNewNas/goldbach-formalization.
Dedicated task branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Incoming verified HEAD: `32fef5121570a3591ad7e1d4974352837fba698b`.
Mathematical source commit: `6be01669df7ac20f1292bab35cb51bc5b39cbba4`.
Source: `Part5OriginalH430BankSurplusPhysicalSplit.lean`; Git blob `344de2882bd0f7a5a17097738d249654684df694`.
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@`ba6ec11d800eccc54406490631895e174de85766` (old proof map, not the November 6 released manuscript).
Pinned toolchain: Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual mathematical addition

The predecessor packet `Part5OriginalH430ActualQ80CandidateSurplus` isolates
`bankCandidateSurplus` as an unbounded positive part of the actual selected
winning-106-bank Q80 candidate minus the raw old request predecessor list.
A previously available manuscript-local selected-row absolute estimate applies,
however, to *physical* `edgeValue`, which includes child Theta. Equating these
two predecessor sums without accounting for child Theta would be invalid.

This packet proves as **uncompiled Lean candidates**:

1. `selected_bank_physical_minus_raw_eq_child_drift` identifies the exact
   physical-minus-raw difference on the **actual chosen bank action** with
   `childThetaDrift`. It invokes the original `children_eq_bank` winner
   equality, retaining scalar/specifed-cell modes and genuine same-Q edges.
2. `selected_bank_candidate_gap_split` applies the elementary *pointwise*
   positive-gap decomposition at each actual Fin occurrence, not to the
   signed total after summation.
3. `bank_candidate_surplus_le_ideal_plus_applied_and_drift` obtains
   `bankCandidateSurplus <= bankIdealOvershoot +
     actualBankAppliedError + bankChildThetaDriftAbs`
   with original levelMark weights, real selected 106 bank only, and no
   quotienting of repeated request appearances.
4. `uniform_bank_candidate_surplus_open_remainder` reuses the EXISTING
   `uniform_actual_selected_error_row_budget` to pay only the previously
   supplied bank absolute applied error: for any epsilon>0, a single
   threshold T before N/n/root/tau/p/g yields
   `bankCandidateSurplus <= bankIdealOvershoot +
       epsilon * actualBankTheta + bankChildThetaDriftAbs`.
   The original 12 bank-row norm is unchanged; the epsilon supplier is not
   counted twice.

Two new ledger definitions: `bankIdealOvershoot` is the genuine positive
(candidate - same-Q idealCellProfile) gap; `bankChildThetaDriftAbs` is the
absolute true child Theta drift. The imported bank applied-error quantity
was ALREADY defined in the existing selected-row supplier. We have not
assumed either new remainder small or nonpositive.

This is a genuine **payment-source separation**, not a final payment.
The actual bank deficit still requires quantitative bounds on both
candidate-vs-ideal overshoot (original base/fixed/feedback/seed/floor)
and child Theta drift. Buchstab suffix-vs-prime debt also remains open.

## Validation / execution boundaries

The GitHub connector had authenticated write permission. The original
20261105 REPORT/REGISTRY/EXTERNAL_INPUTS were read, the true 20261117
Q80 predecessor source and relevant selected-row, requested-branch,
physical-defect sources were inspected. The dedicated newer h34 branch
was at 32fef51; the original 20261105 branch is an old ancestor and was
NOT used to restart the work. This patch creates a NEW task-owned packet;
there is no modification to P1.4, P3.6, production modules, tools, CI,
manuscript, or any unrelated task files. No merge or force push.

Container checks did not find `lean`, `lake`, or `elan` on PATH. The
pinned source-only import graph is not staged as compiled `ImbalancedChen/`
modules in this environment. Thus no valid Lean/Lake build, elaboration,
kernel replay, transitive axiom audit, or finite 430 certification ran.
Remote Git blob/readback and forbidden-placeholder static inspection do
NOT give kernel proof credit. All new theorem bodies and old finite guards
remain UNEVALUATED. No green status is earned.

## Remaining manuscript-internal obligations

- Compile and correct this actual module and pinned ancestors; audit every
  lemma including `children_eq_bank`, `physical_step_eq_raw_plus_drift`,
  and the uniform selected-row supplier.
- Prove correct one-sided bank candidate/ideal overshoot and child-Theta
  drift estimates; separately pay true selected Buchstab Q80 suffix-prime
  positive gaps. Do not replace positive sums by signed whole-row bounds.
- Supply the correct Q80 base/fixed/switched/seed/floor count induction,
  including all-action CLOSED-CELL and matching to original U3/U4 owner
  sources, real full/selected/inherited filters and root 7/2 weight.
- Pay q/tag overlap, rejection lanes, signed Euler/native-history mass;
  complete manuscript PP/same-rho, integral–Theta–count and one jointly
  nested 430+11 causal refinement. No new external PNT/Mertens/BV proof.

**Complete h34 manuscript-internal proof remains OPEN.**
