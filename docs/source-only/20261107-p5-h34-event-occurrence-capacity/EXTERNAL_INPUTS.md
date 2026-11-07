# P5.6 / h34 external input boundary — event occurrence capacity

Pinned fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Source-only parent: `92b29ef0261a52aff8d107edaacb716437564aa1`.
New source commit: `938dc74f26533d9c60cadd464d3cdde3327fa139`.

**New genuinely external analytic inputs: NONE.**
No PNT/Mertens/BV or other classical number-theory input has been
implemented, upgraded or independently audited here.

## Existing exact declarations consumed

- `Part5OriginalH430HistoricalRejectedExitLedger.historicalRejectedEvents`:
  literal recursively enumerated rejected first-exit states; invoked in
  `rejected_prefix_strict_growth`, `immediate_rejected_event_occurrence_count`,
  `actual_rank_two_event_capacity_le_one` and both per-key exact-count
  theorems. This is a manuscript-local implementation, not external.
- `roughPrimeUniverse_nodup N cap 0 (p:ℝ)`: existing prime-carrier
  distinctness proof, used in `actual_rank_two_event_capacity_le_one`;
  remains at the fixed repository dependency/version.
- `Part5OriginalH430ReceiverEventFibreWeights.frozen_fail_key_has_historical_event`
  and `rejected_frozen_fail_key_has_historical_event`: original
  conditional receiver-specific historical event witnesses. Their
  `z0 ≤ cap` prerequisite remains explicit in exact-one consumers.
- `Part5OriginalH430ReceiverEventFibreWeights.eventKeys`,
  `eventFibre`, `receiverEventKey`, `originalEventMass` and
  `key_weighted_fibre_sum`, plus original source `ownPolicyFail`,
  `frozenOnlyBad`, `rejectedFrozenBad`, `frozenOnly` and
  `rejectedFrozen`. Used unchanged in the shared-key signed ledger.
- Mathlib List induction, List.filter, List.Nodup, Finset.image/filter,
  finite sums, `Finset.sum_union_inter`, natural subtraction,
  casts, and ring arithmetic: foundational reusable tools only.

These names are source-level imports/calls. Their transitive proof
chain has NOT been kernel-replayed or axiom-audited in this run.

## Manuscript-internal NOT reclassified as external

One genuine rank-two event has bare mass `1/(p-1)/(ell-1)`, but the
actual signed correction is `historicalExitValue` and includes a
remaining Euler product. Exact selected/full/inherited owner matching,
q/tag surplus payment, cross-lane shared-key overlap, original
U3/U4 source/count bridge, PP/same-rho compatibility, base/seed
and common 430+11 causality remain INTERNAL. No assumed count licence.

Verification: SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
