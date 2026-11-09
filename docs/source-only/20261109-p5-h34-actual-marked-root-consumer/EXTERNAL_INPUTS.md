# P5.6/h34 — external-input ledger for actual resolved marked root consumer

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex`. Fixed Lean `v4.33.0-rc1`, fixed
Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**No new external analytic input, custom axiom or replacement theorem is
added in this packet.**

## Existing analytic input reused without proving it

- `P2EnhancedTwentyOneSourceComparison.twentyOne_source_comparison`,
  consumed **through**
  `Part5OriginalH430TrueCountMarkedGap.original_q_count_le_positive_marked_with_unpaid_gap`
  at `Part5OriginalH430ActualMarkedRootConsumer.original_q_le_actual_resolved_marked_budget`.
  Uniform threshold `T` precedes the even target `N`, all roots and
  actual marked products. At each physical `Q = rootQ N n root tau p`,
  the existing positive-source result requires `Q <= N`, `d > 0`,
  `sigma d >= 0`, `Q/d > 1`, primes dividing every mark product
  above `N^eta`, and the literal cutoff at least `N^eta`.
  Its substantive conclusion is `5*Phi <= weightedQuotient + epsilon*Theta`.
  The intermediate original-count consumer retains a distinct
  positive-part gap `max(card(originalReceiver N p) - 5*Phi,0)`.
  It is NOT a pointwise original-count upper without that gap.
  Earlier PNT/Mertens/BV dependencies remain upstream, unchanged,
  and have NOT been newly replayed or independently audited.

- Mathlib finite `Finset.image` membership, sums, integer/natural casts,
  and standard logic. They are reused in indexed support witnesses and
  finite U3/U4 root sums, not introduced as new analytic licences.

## Manuscript-internal results reused as SOURCE, not as external inputs

- `Part5OriginalH430TaggedArithmeticReceivers.original_band_prime`,
  `original_band_geometry`, `original_U34_eq_tagged_card`, and
  `original_tagged_card`: the real root-prime and original U3/U4
  two-label arithmetic counts.
- `Part5OriginalH430ActualResolvedMarkedPushforward.activePositions`,
  `activeProductSupport`, `activeProductSigma_nonneg` and the
  collision-preserving occurrence pushforward.
- `Part5OriginalH430ActualResolvedPhysicalGates.actual_level_parent_product_pos`
  and `actual_level_quotient_gt_one`: actual root-history geometry.
- `Part5OriginalH430ActualEmptyLevelUnpaidReceipts.empty_resolved_finite_upper_eq_original_count`:
  real empty resolved history leaves the whole original q debt.

## Still INTERNAL and not outsourced

Actual upper-H430 selected-count owner, full/selected/inherited rejection
filters, historic q/tag payment injection/capacity, Q upper gate and primitive
roughness/cutoff for the chosen owner, **unpaid original q minus 5 Phi**
gap bound, literal feedback/base/seed/floor and PP/same-rho, native history,
and common causal 430+11 refinement. This packet does not license a new
external count estimate or any target-equivalent assumption.

All certificates remain UNEVALUATED, and no local Lean compilation,
kernel replay or transitive axiom audit has been performed.
