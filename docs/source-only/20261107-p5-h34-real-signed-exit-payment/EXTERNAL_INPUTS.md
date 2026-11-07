# P5.6 / h34 — real signed exit ledger: external-input boundary

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex`.
Source parent: `00b30d9838d0f90dc5e178b99958ee29849ef91a`.
New Lean source: `c53946bdc67f9579ec9e00f628b78263cc035d69`.

**NEW genuinely external analytic input: NONE.**
No PNT, Mertens, BV, sieve analytic estimate or external
number-theory statement is reproduced or reclassified.

## Pinned reusable foundations

- Lean toolchain `leanprover/lean4:v4.33.0-rc1` from repository
  `lean-toolchain`; Mathlib git revision
  `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`
  from `lake-manifest.json`. No upgrades.
- Mathlib `List.mem_filter`, `List.length_cons`, `Finset.mem_union`,
  `Finset.sum_union_inter`, `Finset.sum_add_distrib`, finite
  sums and elementary ring/omega tactics. Only foundational finite
  combinatorics are used; no numerical certificate has been evaluated.

## Fixed-version manuscript-INTERNAL declarations called

- `Part5OriginalH430HistoricalRejectedExitLedger.historicalRejectedEvents`
  and `historicalExitValue`: used in `actualRankTwoHistory`,
  `actualRankTwoSignedExit`, and the signed-Euler exact theorem.
  Their actual selected prefix, sign, mass, and remaining suffix
  are preserved.
- `Part5OriginalH430ReceiverEventFibreWeights.frozen_fail_key_has_historical_event`
  and `rejected_frozen_fail_key_has_historical_event`: used in
  `original_fourth_lane_key_unique_signed_event` with literal
  `z0 ≤ cap`, source membership and original bad maps.
- `Part5OriginalH430EventOccurrenceCapacity.frozen_fail_key_exactly_one_rank_two_event`
  and `rejected_frozen_fail_key_exactly_one_rank_two_event`: used
  for literal one-event count in the same theorem.
- `Part5OriginalH430ReceiverEventFibreWeights.signed_source_one_event_plus_excess`,
  `eventKeys`, `receiverEventKey`, `originalEventMass`,
  `excessReceipts` and source `ownPolicyFail`, `frozenOnly`,
  `rejectedFrozen`, `frozenOnlyBad`, `rejectedFrozenBad`:
  used unchanged in `two_source_signed_history_gap_ledger`
  and `original_fourth_lanes_signed_history_gap_ledger`.

None of these prior manuscripts' theorem bodies was kernel-replayed in this run.
The root-gate/cap, actual signed Euler-product payment, source
multiplicities, full/selected/inherited owner, count-source match,
PP/same-rho and 430+11 refinement remain INTERNAL.
No target-equivalent input assumption was introduced.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
