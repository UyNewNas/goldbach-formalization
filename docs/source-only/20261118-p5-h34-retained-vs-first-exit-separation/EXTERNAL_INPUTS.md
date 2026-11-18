# External inputs — frozen boundary

This increment is manuscript-internal only. No new external
number-theory theorem, custom axiom, sorry, admit or unsafe
proof mechanism has been introduced.

Fixed manuscript: ba6ec11d800eccc54406490631895e174de85766.
Fixed Lean: v4.33.0-rc1. Fixed Mathlib:
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Existing library inputs: Mathlib Finset.filter/union/disjoint
membership, finite additive sums, and ordered real arithmetic.
The above are invoked through the frozen Mathlib interface,
not restated as new analytic axioms.

Existing MANUSCRIPT-LOCAL declarations reused (not external):
- Part5OriginalH430ActualRetainedPrefixFibres:
  mem_stage_retained_original, stageRetainedOriginal,
  actualRetainedPrefixFibre, stagePrefixKeys,
  exact_retained_source_by_prefix.
- Part5OriginalH430TaggedReceiverFibres:
  original_tagged_subset_frozen at the original precise
  N/tau/n cutoff threshold assumptions.
- Part5OriginalH430TaggedSourceRejections:
  originalTagged, frozenOnly, rejectedFrozen.
- Part5OriginalH430ActualQFirstExitReceipts:
  frozenFailAtActualQ and rejectedFailAtActualQ.
- Part5OriginalH430ActualQUniqueExitLedger:
  actualQFailSource, actualQExitKeys, actualQExitFibre,
  actualRankTwoSignedExit and the real signed source ledger.
- Part5OriginalH430FirstCompatibleFrontierFactor:
  genuine original q-compatible rank-two frontier context.

No proof of PNT/Mertens/BV is reimplemented. The original
manuscript's own first-forbidden owner matching, full/selected/
inherited filters, q/tag capacity, signed Euler payments,
PP/same-rho and common430+11 refinement stay INTERNAL.
No transitive audit of external input dependencies was run.
