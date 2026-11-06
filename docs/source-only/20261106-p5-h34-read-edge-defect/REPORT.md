# P5.6 → h34 — actual requested read / selected-edge defect ledger

**PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED**

- Branch: `chatgpt/p5-h34-request-admission-20261105`.
- Verified preceding remote HEAD: `f59d3e9e88164dc15cb4a80b5adc593ac80b41ed`.
- New source commit: `15752ca83b6f700835536dcfa322cf12cf57b4ab` (one additive source file; commit message [skip ci]).
- Source: `Part5OriginalH430ActualReadEdgeDefect.lean`, 290 lines, 13 theorem proof candidates, 6 definitions; Git blob `826d7df44b7ac33493c94d1cc9bae06428499c17`.
- Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. No version or parameter changes.
- No changes to production, P1.4/P3.6, root targets, dependencies, toolchain, CI configuration or the default branch.

## Previously supplied work checked, not repeated

The earlier `20261105-p5-h34-requested-nonbank` packet already contains
`uniform_requested_buchstab_local`, `uniform_level_buchstab_supply`
and `retained_level_exact`; the earlier `all-choice` and `signed-step`
packets already have the selected-edge feedback decomposition and the
12-Theta signed row estimate. They are source-only and uncompiled.
The immediately previous `AllActionOccurrenceSource` provides a
different object: the chosen **new-table request read** at the genuine
generation-(g+1) parent list position, rather than its OLD-table
selected-child edge mass.

## Exact new manuscript-internal source candidates

The new module introduces `readTerm` as the ORIGINAL `thetaAtom`
times `requestValue (iterate (g+1))`; `childTerm` is the actual
`edgeValue` of `children N Q g` on `iterate g`. Both are evaluated
at the same physical `Index N n root tau p g` list positions, with
each occurrence's original positive `levelMark`, true root Q, real
read mode and unchanged requested action.

1. `level_mass_difference` is the exact finite sum of the signed
   local read-minus-edge defects.
2. `unresolved_request_gap_zero` and `level_defect_partition`
   retain the exterior scalar positions but prove their defect is
   zero before applying the exact three-way selected-action split.
3. `retained_request_gap_zero`, `retained_level_total_zero`
   and `level_defect_nonretained` show that retention contributes
   **exactly zero** to the Theta-scaled discrepancy, not epsilon-Theta.
   This uses the SAME chosen specified old cell and retains occurrences.
4. `selected_buchstab_gap_exact` and
   `buchstab_level_gap_exact` write the actual Buchstab term as
   `thetaAtom * (integer buchstabValue / 2^80)` minus the true
   strict-prime OLD-table sum, with actual upper/lower flag, ceiling,
   Q, physical parent and selected index. The difference remains
   UNPAID; the theorem never asserts equality of suffix and prime sum.
5. `bank_level_defect_le_candidate` combines the actual chosen-bank
   `selected_bank_candidate_upper` with `thetaAtom_nonneg` derived
   from the actual `rootHistory_support`; no arbitrary Theta
   positivity hypothesis or count licence is inserted.
6. `actual_one_generation_candidate_upper` concludes the finite,
   one-sided **read-minus-selected-edge** inequality in terms of the
   unpaid Buchstab gap and the ORIGINAL bank base/fixed/feedback
   candidate gaps. It does NOT imply the original U3/U4 count
   inequality or close CLOSED-CELL by itself.

This closes a local algebraic wiring gap between the existing *read*
and *child-edge* suppliers, without pretending that either is the
complete original U3/U4 selected-count. The exact candidate inequality
is entirely under actual root hypotheses, with positive marks and
no quotient by repeated prime products or physical catalog labels.

## Boundaries and real next step

The remaining manuscript-internal obligations are:
- Pay the literal Buchstab integer-suffix versus strict-prime discrepancy
  in the correct directional closed-cell count comparison; connect the
  bank base/fixed/feedback candidate to integer floor/rounding and seed,
  without assuming a count recurrence.
- Complete the actual full original U3/U4 selected-count identity,
  original root count weights, complete full/selected/inherited owner,
  rejection lanes and non-injective occurrence/fibre multiplicity.
  The conditional `omega<=a` initial-presieve obstruction is still
  only a stage compatibility issue: it is not a fixed omega fact.
- Finish manuscript-local PP/same-rho, native-history quality,
  outer integral—Theta—count source and a **single common** nested
  430+11 causal refinement with prescribed reserve order.
- Install the complete held dependency closure, elaborate, kernel
  replay, audit all transitive axioms and replay finite certificates.

Original c/K, root norm 7/2, row norm 12, actual alpha, same-Q,
closed cells, strict Buchstab ceiling, specified-cell/scalar read
difference, true occurrence counts and 430+11 budget are unchanged.

## Actual validation

Authenticated repository push access and dedicated branch were
verified before writing. GitHub readback verified the source commit,
source blob and its one-file additive diff relative to `f59d3e9e88164dc15cb4a80b5adc593ac80b41ed`.
Source text had no forbidden proof placeholders, and a nested-comment-
aware delimiter balance check passed. These are **text checks only**,
not Lean parsing, elaboration or proof verification.

No Lean/Lake compile, heavy CI or new workflow run, kernel replay,
transitive-axiom review or numerical430 finite replay was performed.
All new proof bodies and finite guards remain **UNEVALUATED**. No
node is promoted green.

**Complete manuscript-internal h34 remains OPEN.**
