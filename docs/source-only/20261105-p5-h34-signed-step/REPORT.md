# P5.6 / h34 — signed generated one-step feedback comparison

2026-11-05. Parent branch: `chatgpt/p5-h34-request-admission-20261105`.
Exact prior HEAD: `5dee88c29c55420c07d0c9a5ce834c358c7cdc16`.
Status: **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / ZERO KERNEL CREDIT**.
The complete manuscript-internal h34 remains **OPEN**.

## Actual new manuscript-internal proof source

New single module: `Part5OriginalH430RequestedSignedStep.lean`
(~302 lines, seven public theorem bodies and one private helper; six finite
definitions). It imports the existing all-choice and bank/nonbank suppliers,
and neither changes those files nor modifies production imports.

The last packet `5dee88c` supplied the exact selected bank/Buchstab/
retention partition and a common coefficientwise absolute feedback budget
of 12 Theta. It did not yet compare the ACTUAL signed generation value
with the SAME selected ideal feedback profiles.

This packet supplies that missing bidirectional manuscript-local step:

* `weighted_abs_difference` is the elementary real finite weighted
  absolute-value inequality, applied to the original LevelIndex **LIST
  POSITIONS** and their genuine positive path-product marks; no quotient
  by equal integer products, distinct labels or owner fibres is made.
* `bank_abs_le_applied` compares each *selected* bank's actual
  `edgeValue` with the original `idealCellProfile` on the same
  predecessor table, bounded by the existing `levelAppliedError`.
* `buchstab_abs_le_applied` and `buchstab_applied_le_rowError`
  use the selected strict Buchstab source, both polarities, the literal
  original prime ceiling and the old-array integral profile, then bound
  signed value error by the pre-existing coefficientwise absolute row
  error. The local `Coherent` instance is supplied by
  `rootHistory_coherent` for each actual generated occurrence.
* `generationValue_as_actual` retains the exact three-way winner
  partition of `RequestedAllChoice`, keeping retention exactly equal
  to its old specified-cell value; no new epsilon charge.
* `generated_difference` identifies the actual-minus-ideal value with
  ONLY the selected bank and Buchstab differences.
* `generated_abs_le_combined` gives
  `|generationValue - generatedIdeal| <= combinedError`, combining
  the original bank `level_applied_error_le` with the strict-prime
  `requested_buchstab_applied_le` on actual requested positions.
* `uniform_generated_signed_step` selects ONE threshold before
  N, precision, root kind, root prime and generation; for the original
  root hypotheses, its conclusions are
      generatedIdeal - epsilon*combinedTheta <= generationValue
      generationValue <= generatedIdeal + epsilon*combinedTheta
      combinedTheta=0 -> generationValue=generatedIdeal.
  The epsilon-Theta result is inherited from the existing COMMON
  `uniform_combined_feedback` supply. No extra 5+12 or 106-fold
  payment is made. The value at Theta=0 is an exact equality, not
  a division by zero.

## Boundaries; do not promote this to full count closure

This is a signed bound on the **generated feedback request history**.
It is NOT an identification with the original U3/U4 arithmetic
prime/sifted count, original root count weights or the manuscript's
closed-cell arithmetic recurrence. In particular, `generationValue`
uses actual selected child rows at one prior generation; it cannot
replace the original signed prime/PP count without proving an explicit
count-source bridge. All positive-mass root sources, multiplicities,
full/selected/inherited filters, rejection lanes, ceiling equality and
native-history proper/equality/inherit costs must be preserved.

Still manuscript-INTERNAL and open:

1. Genuine original U3/U4 arithmetic-source-to-generated-state
   closed-cell one-step comparison with correct sign, original root
   weights, owner multiplicities, filters and rejection lanes.
2. Original ordinary/fixed/switched base, genuine seed and exact
   integer floor/rounding payments, without postulating a count licence.
3. Manuscript-local same-rho/PP realization, moving source interfaces,
   feedback integrals and single threshold order.
4. All native proper/equality/inherit masses, outer integral/Theta/count
   normalization and ONE shared causal nested 430+11 refinement
   respecting reserve order.
5. P0-controlled source installation, Lean compilation, kernel replay,
   full type/axiom audit and eventual root integration.

No code or proof of PNT/Mertens/BV or other genuinely external
analytic inputs is introduced; existing suppliers are recorded in
`EXTERNAL_INPUTS.md`. The original c/K, root norm 7/2, row norm 12,
strict prime ceilings, actual alpha and same-Q root geometry remain
unchanged. No P1.4/P3.6 changes, CI dispatch, toolchain upgrade or
default-branch merge.

## Verification / next checkpoint

This packet is UNCOMPILED, and all newly written proof bodies and
inherited finite guards remain UNEVALUATED by Lean. Source text / diff
and Git object readback checks are *not* kernel evidence. No actual
Lean parser, elaborator, Lake build, proof replay, transitive axiom
audit or numerical430 replay is claimed.

Installation order: stage earlier requested modules in their archived
order, then this file as
`ImbalancedChen/Part5OriginalH430RequestedSignedStep.lean`.

Next independent proof target: prove the original **arithmetic**
source-count-to-request transition with the correct signs and fixed/
switched/seed/floor costs, using the signed feedback inequality here.
Do not encode that missing count inequality as a new premise or
reclassify it as external.
