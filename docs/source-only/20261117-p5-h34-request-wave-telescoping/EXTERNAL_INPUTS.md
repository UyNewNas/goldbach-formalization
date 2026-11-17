# P5.6/h34 — request-wave telescoping external input register

Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean: `v4.33.0-rc1`; Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**New external analytic inputs: NONE.**

## Exact reused interfaces and invocation sites

* Pinned Lean/Mathlib `List.map`, `List.sum`, additive/distributive
  ring algebra, `max` order, and real inequality arithmetic:
  `weighted_map_sum_add`, `waveAccount_mono`,
  `root_eq_terminal_plus_defects`,
  `root_le_terminal_plus_unpaid_defects`. No number-theoretic
  PNT/Mertens/BV/prime distribution assertion is added.
* Manuscript-local source-only candidates:
  `Part5OriginalH430ActualRequestAllActionWave.wave_zero` and
  `wave_successor`, invoked at `root_eq_terminal_plus_defects`.
  `Part5OriginalH430RequestedHistory.mark_pos`, used in
  `waveAccount_mono`. The literal `children`, `nextRequest`,
  `edgeWeight`, `Selected`, `bankEdges` and strict `singleChildren`
  are consumed in the three selected-action defect equations.

## Non-external manuscript obligations retained

True request-level quantitative Buchstab/retention suppliers,
`positiveDefect` payment, all-action CLOSED-CELL count induction,
correct actual count diagnostic, full/selected/inherited U3/U4 source,
original root norm7/2 receipts, same-rho/PP, base/switched/seed/floor,
signed Euler/native-history and 430+11 outer refinement remain OPEN.

No new `sorry`/`admit`, custom axiom, unsafe/native proof bypass or
target-equivalent asserted count licence is included. **No Lean proof
verification** is claimed; fixed earlier analytic interfaces are reused
but their transitive axiom closure has not been independently audited.
