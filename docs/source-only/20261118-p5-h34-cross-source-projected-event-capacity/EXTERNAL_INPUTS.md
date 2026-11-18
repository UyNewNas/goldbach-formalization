# P5.6 → h34 — external input boundary (2026-11-18)

Pinned manuscript: ba6ec11d800eccc54406490631895e174de85766.
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

No new external analytic input or custom axiom. This packet proves only
manuscript-internal finite-fibre and historical-label compatibility
statements using pre-existing declarations.

Existing library interfaces actually called:
- `Option.map` and injectivity of `Option.some`;
- `Finset.filter`, `Finset.disjoint_left`, `Finset.sum_union`,
  `Finset.card_pos`, `Finset.sum`, and `omega`.

Manuscript-local dependencies (NOT external axioms):
- `Part5OriginalH430ActualRetainedPrefixFibres.actual_second_prefix_witness`
  and `actualSecondPrefixKey` on genuine original q/tag receipts;
- `Part5OriginalH430FirstCompatibleFrontierFactor.
  frontier_eligible_iff_actual_second` at the receipt's literal
  `originalPhysicalQ`, prime divisor, and ordinary Rosser frontier;
- `Part5OriginalH430RetainedVsFirstExitSeparation.
  retained_not_actual_Q_fail`, with exact N≥2, 0≤tau≤1/12 and
  1/(n+1)≤11/384 manuscript cutoff hypotheses;
- `Part5OriginalH430ActualQUniqueExitLedger.
  mem_actual_Q_exit_fibre_iff`,
  `actual_Q_fibre_preserves_physical_Q` and
  `actual_Q_key_has_original_receipt`.

No PNT/Mertens/BV result is reimplemented. The exact literal selected
history `Fin` owner, signed Euler payment, PP/same-rho consumer,
root normalization and common 430+11 refinement remain manuscript-
internal obligations. There is no successful compiler, kernel, or
transitive-axiom verification record for this packet.
