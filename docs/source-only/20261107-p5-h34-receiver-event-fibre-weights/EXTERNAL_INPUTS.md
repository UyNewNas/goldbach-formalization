# P5.6 / h34 — external input boundary for event-fibre multiplicities

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Source-only parent: `0980a27fac7f065a0b223613851d28df2684fb10`.

**New analytic external inputs: none. No external proofs implemented.**

## Exact already-existing local declarations reused

- `Part5OriginalH430ReceiverRootGateAccounting.ownPolicyFail`:
  the real per-receipt root-licensed and failed-next-Rosser fourth lane.
  Used in both `*_fail_event_mass_by_fibres`, both
  `*_fail_key_has_historical_event`, and
  `original_two_fail_lanes_signed_fibre_sum`.
- `Part5OriginalH430ReceiverRootGateAccounting.frozen_own_root_fail_has_event`
  and `rejected_own_root_fail_has_event`: *conditional* event witness
  with true root p, corresponding bad ell, sign and mass. Each requires
  `z0 ≤ (cap : ℝ)`, retained explicitly in our key-event consumers.
  These are manuscript-local proofs, NOT moved to the external boundary.
- `Part5OriginalH430TaggedArithmeticReceivers.TaggedReceiver`,
  `frozenOnly`, and `Part5OriginalH430TaggedSourceRejections.rejectedFrozen`,
  `frozenOnlyBad`, `rejectedFrozenBad`, `arithmeticPrime`: the
  original U3/U4 tagged arithmetic `(p,q)` source and two distinct
  bad-prime cutoff rules. Used without new normalization.

## Foundational library reuse

- Mathlib `Finset.filter`, `Finset.image`, `Finset.sum_filter`,
  `Finset.sum_comm`, finite cardinality and arithmetic casts.
  Used in `sum_by_event_fibres`, `key_weighted_fibre_sum` and their
  original-lane instances. No new axiomatic computational backend.

All existing externally sourced PNT/Mertens/BV/prime-distribution
dependencies remain at their pinned historical interfaces, unchanged
and **not reverified** here. Their exact transitive dependency audit
is pending; do not treat `EXTERNAL_INPUTS.md` as a replay report.

## Manuscript-internal obligations deliberately not outsourced

Original complete U3/U4 selected-count identification, original count
root weights, event-owner *occurrence* map and its noninjective payment,
full/selected/inherited policy correspondence, blocked and non-event
rejections, actual arithmetic CLOSED-CELL predecessor induction,
base/switched/seed/floor and integral payments, manuscript-local
PP/same-rho compatibility, native-history mass and one common430+11
causal refinement. No target-equivalent count assumption is introduced.

**Validation:** SOURCE ONLY / UNCOMPILED / UNEVALUATED. No kernel replay,
transitive axiom audit, finite certificate evaluation or CI dispatch.
