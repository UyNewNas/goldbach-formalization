# External-input boundary (2026-11-19 D8 second-affine increment)

No new external analytic input, conditional hypothesis, custom axiom
or target-equivalent licence is added.

The candidate reuses:
- `ImbalancedChen.Certificates.RationalLogCertificate.check_sound`,
  the existing Mathlib odd logarithm series soundness theorem, through
  `rational_log_six_fifths` for argument 6/5, terms=2.
- Mathlib continuity/interval integrability, nonnegative set integrals,
  and rational arithmetic, in `actual_d8_second_integral_ge_1_over_25`
  and `actual_d8Logs_ge_1_over_25`.
- Fixed manuscript-local D8 piece-domain equalities
  `P2EnhancedSeedPairD8Integral.second_affine_piece` and
  `P2EnhancedSeedPairD8PieceSum.continuousOn_outerSlice`;
  the exact seven-piece identity `lambda_exact_seven_logs`;
  earlier candidate singleton/D6 positive sources.

These are reused at the pinned repository dependency versions, not
reproved as new external analytic theorems. Their transitive assumptions
have NOT been audited. Original PP/same-rho, seed intercept, full source
count and common causal430+11 remain manuscript-internal obligations.
