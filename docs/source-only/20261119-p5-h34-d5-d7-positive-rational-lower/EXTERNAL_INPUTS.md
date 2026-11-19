# External inputs (D5 and D7 positive rational lower packet)

No new external analytic input or custom axiom is introduced.
External foundational library results reused as already pinned:
- Mathlib ordered-real arithmetic, interval integrability and additivity,
  integral monotonicity, nonnegative integrals.
- ImbalancedChen.Certificates.RationalLogCertificate.check_sound for
  exact 2-term lower logarithm series at 5/4 and 6/5, used in the two
  private rational_log_* proofs in the new candidate source.
- Existing P2EnhancedSeedD5PlusLogFubini feedback_three_affine_logs,
  feedback_outer_log and slice geometry on true D5 support.
- Existing P2EnhancedSeedPairD7Integral continuousOn_outerSlice,
  endpoint_geometry and P2EnhancedSeedPairD7AffinePieces
  first_intervalIntegrable on the full true D7 support.
- Existing P2EnhancedSeedActualSevenLogIdentity.lambda_exact_seven_logs
  and candidate singleton/D6/D8 lower sources on the same pinned branch.

The inherited interfaces and their transitive axiom closure have NOT been
compiled or audited in this packet. These are reused results, not claims
of independent verification. No PNT/Mertens/BV proof is added.
The original PP/same-rho, analytic intercept, full selected counts,
true seed/CLOSED-CELL induction and common 430+11 causal refinement remain
manuscript-INTERNAL and are not relabelled external.
