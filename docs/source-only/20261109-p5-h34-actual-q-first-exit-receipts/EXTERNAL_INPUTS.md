# h34 external-input boundary — actual-Q first-excluded original receipts

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` (blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`). Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**New external analytic inputs: NONE.** No new PNT, Mertens, BV, numerical estimate, external axiom or target-level licence. The new source only composes old manuscript-local finite interfaces.

## Exact existing manuscript-local interfaces used

- `frozenOnly`, `rejectedFrozen`, `frozenOnlyBad`, `rejectedFrozenBad`, and `frozen_only_disjoint_rejected` from the existing tagged arithmetic rejection source. These preserve the original U3/U4 labels, the real q receiver and both different cutoff rejection causes. Used in the two `*FailAtActualQ` definitions and `actual_Q_two_fail_sources_disjoint`.
- `originalPhysicalQ` from `Part5OriginalH430PhysicalSelectedRootQFibres`: `(N,precision,tau,z) ↦ rootQ N precision tag tau p`. It is constant in q only for fixed tag,p; no U3/U4 equality is assumed. Used in both finite filters and the two signed first-exit candidate theorems.
- `ownPolicyFail` and `receiverEventKey` / `eventKeys` at the original per-receipt physical Q. The actual member is promoted via `Finset.mem_image`, not by assuming event-key injectivity.
- `original_fourth_lane_key_unique_signed_event` and the existing definitions `actualRankTwoHistory`, `actualRankTwoSignedExit`, `historicalExitValue`, `originalEventMass`: applied to exactly the real `z0 ≤ cap` and the `key` of each original rejected receipt. The correction includes the original event's remaining Euler product and negative sign.
- `physical_upper_first_excluded_suffix_nonneg` (from the immediately preceding source-only packet) at `1 < originalPhysicalQ`, reused only for the sign of the entire finite UPPER physical Euler correction, not to pay an individual arithmetic rejection.
- Mathlib's `Finset.mem_filter`, `Finset.mem_image`, finite union/disjointness and signed summation laws, as core library facts rather than reconstructed analytic results.

## Internal obligations NOT outsourced

The actual-Q matching here is at the **receipt/event witness** level only. Event-key multiplicity and signed cross-Q aggregation, actual owner of the full/selected/inherited history, six-lane unpaid rejections and quantitative H430 source bound, all-action CLOSED-CELL, correct seed/base/floor/feedback, the original manuscript's own PP/same-rho instantiation, native-history and the shared 430+11 realization remain manuscript-internal. No finite sign fact implies that these are proved.

Every imported source-only proof and finite certification is still UNCOMPILED or UNEVALUATED; there has been no kernel replay or transitive axiom audit.
