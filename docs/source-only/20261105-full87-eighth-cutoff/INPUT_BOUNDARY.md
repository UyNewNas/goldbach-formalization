# External inputs — rank-eight source cutoff

**Manuscript pinned:** UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b, paper/source/manuscript-body.tex blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79, §4 eq:current-raw-density and the square-test paragraph (lines 393–408).

**Internal exact sources:** ImbalancedChen/PrimeHistoryLogCoordinates.lean `primeHistoryLogCoordinates_frontier`, original87 `states_eq_owner_filter`, `retainedOwner_some_iff`, `trim_subset_source`, `source_coordinate_lower` and immediately preceding `target_deletion_power_gap_sandwich`. These are existing project candidate sources, not new imported classical analytic assertions. The new proof applies them to the same original owner and state; it does not alter the actual parent or policy.

**External registered ONLY, not implemented or asserted:** (1) ordinary upper-parity exit-series positive convergence and finite-rank sandwich in the manuscript §4 and upper appendix (must match original parity and normalization); (2) PNT/Mertens for V_N and singular normalization, with N-uniform error at y=N^u; (3) actual moving-residue AP/BV or stronger full-q distribution for the same rho, support and target deletion. No fixed compatible Lean declarations with matching complete types have been accepted here, and no new axioms are introduced.

**Internal unproved:** deeper-rank square-test exponent and cutoff, uniform ordinary-continuation density-to-residual integral; signed beta error, primitive/centre correction, sixth filtering; saved numerical archive and compiler/density reserves. Distinct source proof/acceptance remains necessary.
