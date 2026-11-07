# P5.6/h34 quotient bad physical carrier — input ledger

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, body `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Goldbach source baseline: `18eb768aa82e34dc4be578d85eec7552fe140076`.
New source commit: `0de3aeee71ff5a05baad97765106102eb423c9ab`.

No new classical analytic input is introduced or proved. PNT, Mertens and BV remain unchanged. No substitute axiom or target-equivalent global premise is introduced.

## Actual pre-existing proof sources used

- `Part5OriginalH430TaggedSourceRejections.raw_quotient_data`: for each `receiver ∈ rawTagged N`, `0 < arithmeticQuotientPrime receiver`, `arithmeticQuotientPrime receiver ≤ N`, `Nat.Coprime (arithmeticQuotientPrime receiver) N`. This source-only predecessor is **not kernel certified**.
- `Part5OriginalH430TaggedSourceRejections.frozen_tagged_subset_raw`: existing injection of frozen-tagged receivers into literal raw quotient source.
- `Part5OriginalH430TaggedFirstBadPrimeOwner.BadPrime`, `frozen_only_tagged_first_bad` and `rejected_frozen_tagged_first_bad`: exact smallest-rejected-prime source, with original `(N:ℝ)^a` versus the root-dependent physical frozen cutoff. These are source-only predecessors, not formally verified.
- `ImbalancedChen.RoughPrimeUniverse.mem_roughPrimeUniverse`: exact capped and N-excluding prime carrier membership with lower 0 and strict upper z0. This is an original project theorem, not an external analytic oracle.
- `Part5OriginalH430HistoricalCandidateOrder.actual_next_candidate_iff`: exact original root/next-selection enumerator, source-only predecessor.
- Standard Lean/Mathlib `Nat.dvd_gcd`, `Nat.le_of_dvd`, `Nat.Prime.one_lt`, real/natural cast order, finite-list candidate membership. No Mathlib version change or external theorem construction.

## Exact new consumers and hypotheses

- `raw_quotient_factor_not_target`: raw membership, a prime factor `ell ∣ q`. Derives `¬ell ∣ N`, using the actual source gcd=1; no cap assumption.
- `raw_quotient_factor_le_target`: raw membership and `ell ∣ q`. Derives `ell ≤ N`; no cap assumption.
- `raw_bad_in_initial_historical_universe`: additionally requires `BadPrime q cut ell`, **`N < cap`** and **`cut ≤ z0`**, and yields only the initial literal prime universe membership.
- `frozen_only_bad_in_initial_historical_universe`: `cut = (N:ℝ)^a`, fixed U3/U4 tagged frozenOnly source.
- `rejected_frozen_bad_in_initial_historical_universe`: `cut = frozenPrimeCutoff N n tau (arithmeticBand receiver) (arithmeticPrime receiver)`, fixed tagged rejectedFrozen source.
- `frozen_only_bad_root_enumerated` and `rejected_frozen_bad_root_enumerated`: actual **empty root** next selection only, original reciprocal-prime weight. No retained policy is assumed or concluded.

## Manuscript-internal, explicitly NOT external

Prove actual physical cap and cutoff dominance at the call sites, root-to-post-root history carrier transport, retained-policy decisions, the real full/selected/inherited owner, occurrence/sign/root-weight correspondence, both rejection-lane payments, request-level Buchstab/retention plus closed-cell induction, correct base/seed/floor, manuscript-local PP/same-rho, native outer mass/Theta/count and common 430+11 refinement. No finite certification has been executed; all such checks remain UNEVALUATED.
