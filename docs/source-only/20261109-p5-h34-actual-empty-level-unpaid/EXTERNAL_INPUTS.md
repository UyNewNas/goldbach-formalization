# P5.6 / h34 — external-input boundary for actual empty resolved generation

Fixed source manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`;
fixed Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; Lean `v4.33.0-rc1`.

No new external analytic input, axiom, PNT, Mertens or Bombieri–Vinogradov
proof is introduced. No source gap is reclassified as external.

## Exact reused local declarations and call sites

- `Part5OriginalH430ActualResolvedMarkedPushforward.activePositions`,
  `activeProductSupport`, `activeProductSigma`,
  `activeProduct_Phi_exact`, `activeProduct_Theta_exact`:
  in `empty_resolved_product_support`, `empty_resolved_product_sigma`,
  `empty_resolved_Phi`, `empty_resolved_Theta`.
- `Part5OriginalH430ActualResolvedPhysicalGates.activeProduct_Theta_pos_from_root_geometry`:
  used in `actual_Theta_zero_iff_no_resolved` with its actual N, tau,
  precision, prime and physical-band premises. Those gates are
  manuscript-internal geometry, not new external licenses.
- `Part5OriginalH430TrueCountMarkedGap.unpaidOriginalMarkedGap`,
  `originalMarkedDiscrepancy`, `markedFiniteUpperWithGap`:
  in the exact unpaid q-fibre and finite-budget equalities.
- `Part5OriginalH430TaggedArithmeticReceivers.originalReceiver` and
  `P2EnhancedTwentyOneSameQWeighted.Phi`, `Theta`,
  `weightedQuotient`: unchanged original arithmetic-count and physical
  same-Q finite marked definitions.
- Mathlib's finite sums, natural-to-real casts, `max_eq_left`, and
  real linear arithmetic are used as ordinary trusted library results.

No transitive dependency or finite certificate has been independently
audited; source compilation and numerical430 replay remain UNEVALUATED.

## Still manuscript-internal

Real selected-count source, q/tag historical owner and full/selected/
inherited gates, nonempty-generation q-versus-marked source coverage,
signed Euler and rejection payments, closed-cell feedback/count
induction, PP/same-rho, outer integrals and common 430+11 refinement
remain open and cannot be substituted with external axioms.
