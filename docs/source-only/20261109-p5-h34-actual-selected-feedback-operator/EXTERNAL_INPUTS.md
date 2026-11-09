# h34 external-input ledger — selected feedback operator

2026-11-09. **No new genuinely external analytic input.**

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
source `paper/source/manuscript-body.tex`, blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Pinned Lean: `v4.33.0-rc1`.
Pinned Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## Reused results / exact call locations

- Mathlib real absolute-value triangle for finite sums (`Finset.abs_sum_le_sum_abs`),
  finite sum distributivity (`Finset.sum_add_distrib`, `Finset.sum_mul`,
  `Finset.sum_comm`, `Finset.mul_sum`, `Finset.sum_le_sum`), monotone
  multiplication and finite sum equality. Called inside the five new
  local proofs; these are elementary Mathlib primitives, not analytic inputs.
- Manuscript-internal (currently UNCOMPILED)
  `Part5OriginalH430ActualSelectedRowBudget.actual_selected_row_eq_positions`:
  invoked by `actual_selected_old_read_eq_winning_positions` to identify
  actual selected Fin occurrences.
- Manuscript-internal (currently UNCOMPILED)
  `Part5OriginalH430ActualSelectedRowBudget.uniform_actual_selected_error_row_budget`:
  invoked in `uniform_actual_selected_old_read_operator` to provide the
  actual nonnegative row, the 12*bankTheta+5*BuchstabTheta row norm,
  and the existing selected/bank error bounds.
- The preceding feedback array comes literally from
  `oldAtomValue (precedingH g) (precedingh g) b`. The bound `|oldAtomValue| <= M`
  is **explicit**, not asserted without a hypothesis; proving M in the genuine
  induction remains a manuscript-internal obligation.

## Boundary

The original U3/U4 selected-count owner/source identity, 430-generation
arithmetic CLOSED-CELL base/successor, root count weights, six rejection lanes,
H430 signed Euler payment, actual feedback-to-integral, PP/same-rho and common
430+11 causal refinement remain internal. No PNT/Mertens/BV theorem, new
axiom, h34 conclusion, or count-equivalent licence is introduced.

All imported Lean material is unverified in this source-only packet.
No kernel replay, transitive axiom audit or numerical certificate replay.
