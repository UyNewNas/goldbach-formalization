# P5.6/h34 actual bank-surplus physical split — external boundary

Fixed original manuscript: `ba6ec11d800eccc54406490631895e174de85766`.
New genuinely external analytic inputs: **none**. No new axiom,
PNT/Mertens/BV proof or target-equivalent licence is implemented.

Reused manuscript-local statements at the pinned proof/source-only chain:

- `Part5OriginalH430RequestedLocalBankSupply.children_eq_bank`:
  actual `Selected g r i (.bank k)` identifies the **exact** chosen
  `children N Q g r` with `bankEdges N Q r (actionOfSlot k)`.
  Consumed in `selected_bank_physical_minus_raw_eq_child_drift`.
- `Part5OriginalH430PhysicalRequestDefectBridge.physical_step_eq_raw_plus_drift`:
  selected original `edgeValue` is unweighted raw request predecessor
  sum plus its genuine child-Theta drift, with same physical Q and iterate.
  Consumed in the same declaration.
- `Part5OriginalH430RequestedLevelBankSupply.levelAppliedError`:
  already-defined original selected-position absolute difference between
  physical old-row value and same-Q idealCellProfile. Consumed in
  `bank_candidate_surplus_le_ideal_plus_applied_and_drift`.
- `Part5OriginalH430ActualSelectedRowBudget.uniform_actual_selected_error_row_budget`:
  for epsilon>0, supplies one T>=4, uniform N>=T, root/prime conditions,
  0<=tau<=1/12, 1/((n:Real)+1)<=11/384, all g:Fin 430; in
  particular `actualBankAppliedError <= epsilon*actualBankTheta`.
  Consumed in `uniform_bank_candidate_surplus_open_remainder`.
- `Part5OriginalH430ActualQ80CandidateSurplus.bankCandidateSurplus`:
  already-selected original winning-bank literal candidate minus RAW old
  predecessor; is the LHS, not an external count source.
- Mathlib finite sums, real absolute value, `max` order and linear arithmetic:
  elementary formal arithmetic, not new analytic number theory.

The root U3/U4 count-source equality, full/selected/inherited owner matching,
Q80 seed/base/floor and the uniform positive overshoot/Theta drift payment,
PP/same-rho and common 430+11 refinement are **manuscript-internal**.
They have NOT been treated as external, imported as fictional hypotheses,
or shown closed. Inherited source-only dependencies remain uncompiled and
finite guards UNEVALUATED.
