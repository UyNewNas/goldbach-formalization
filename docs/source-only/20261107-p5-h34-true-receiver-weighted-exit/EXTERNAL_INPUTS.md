# P5.6 h34 true tagged receiver weight — external input boundary

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`.
Source parent: `2763aff366e832b2176c86b5442ed11150321c9b`.
New source commit: `147a6600cfb0f9a90bae98dc42021bebb9b98a17`.

**NEW EXTERNAL ANALYTIC RESULTS: NONE.**

Existing dependencies (unchanged, with no proof expansion):
- Lean `leanprover/lean4:v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` as recorded in the previous packet.
- Mathlib finite Finset image/filter/union/monadic sums, `Finset.sum_subset`, `Finset.sum_add_distrib` and elementary ring arithmetic. These are mathematical library operations, not a new PNT/Mertens/BV input.

Fixed manuscript-internal code reused with exact call locations:
- `Part5OriginalH430ReceiverEventFibreWeights.eventFibre`, `eventKeys`, `mem_eventFibre_iff`, `sum_by_event_fibres` in `fibre_empty_of_key_outside` and `two_source_true_weight_sum_by_keys`. These preserve actual tagged (p,q) receiver multiplicities.
- `Part5OriginalH430RealSignedExitPayment.actualRankTwoSignedExit` in `two_source_true_weight_signed_exit_gap` and `original_U34_rejected_weighted_signed_exit_gap`, preserving literal signed remaining Euler product from `historicalExitValue`.
- `Part5OriginalH430ReceiverRootGateAccounting.original_rejected_eight_lane_signed`, `gateBlocked`, `ownCarrierOutside`, `ownPolicyPass`, `ownPolicyFail`, used in `original_U34_rejected_weighted_signed_exit_gap`; the original `N,n,tau,z0,Q,lower` hypotheses remain explicit.
- `Part5OriginalH430TaggedSourceRejections.frozenOnly`, `rejectedFrozen`, `rejectedOriginal`, and the two distinct original bad-factor functions.

Still INTERNAL: complete original selected U3/U4 count and root weights, full/selected/inherited historical owner, signed Euler directional payment and q/tag fibre surplus, six root exceptions, CLOSED-CELL and base/seed/floor, PP/same-rho, native-history mass and 430+11 causal refinement. No assumed target-equivalent input is introduced.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED. No Lean execution or external theorem verification.
