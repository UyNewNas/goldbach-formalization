# Saving16 manuscript display adapter

Status: source only, uncompiled, zero new formal acceptance credit.

The 20261106 manuscript at commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`,
`paper/release-20261106/en/numerical-appendix.tex`, `num:upper-table`,
certificate field `/upper_saving_bounds/15`, displays
`G16 >= 1543640141 / 10^14`. The manuscript/source cross-check and prior
precise deduplication search are recorded in
`../20261126-p2-5-final-obligations/DEPENDENCY_BOUNDARIES.md`.
This task reused that search; only the subsequently added round8 candidates
were checked for an existing display adapter, and none was found there.

This module adds exactly two closed theorems:

1. `displayed_bound_le_historical_endpoint` compares the two exact rational
   expressions in the real numbers using `norm_num`.
2. `displayed_bound_le_source_integral` applies transitivity to the existing
   `P2OriginalSaving16OwnedIntegral.historical_endpoint_le_source_integral`.

The Q96 expression is copied from that theorem's statement as
`(1222997719565324892497827 : ℝ) / (2 : ℝ)^96`. No new Q96 definition, source
region, density, witness data, or analytic hypothesis is introduced. The
production OwnedIntegral file and its original 30o source package have the
same SHA256:
`5aa1cfb7b3080e4bc3ff0152901ac234d7451da4788fee364a7d5bcc1aeb8047`.

An integer cross-product check gives
`1222997719565324892497827 * 10^14 - 1543640141 * 2^96 =
1842572655612915813639962624 > 0`. This host-side check is preparatory
arithmetic only; the Lean proof remains pending ordinary compilation,
independent replay and the complete owned-declaration audit.

No compiler was run for this package. Production files and their acceptance
state were unchanged. This adapter inherits the existing OwnedIntegral
dependency obligations: all14 original cells, their finite simplex and
geometric checks, and the integral ownership proof must be accepted. A
candidate display bound does not complete P2.5 or supply the separate
same-policy quantitative distribution-error estimate.
