# P5.6 h34 — external boundary, no new external proofs

Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766.
Inherited external inputs remain those recorded in
`docs/source-only/20261105-p5-h34-request-admission/EXTERNAL_INPUTS.md`
and in the intervening source-only packets. This increment introduces
**zero** additional analytic number-theory inputs, axioms or external
theorem implementations.

The new source invokes existing local lemma signatures:
- `actual_one_generation_fixed_upper` in
  `Part5OriginalH430ActualFixedClosedCell`, conditional on the
  actual preceding fixed-cell comparison.
- `bank_ideal_feedback_exact`, `feedbackRoundingLoss_nonneg`,
  `feedbackRoundingLoss_le_length` in
  `Part5OriginalH430ActualFeedbackQuotientRemainders`.
- `rootHistory_support`, `thetaAtom_nonneg` and `mark_pos`
  at the actual request-history indices.

The original U3/U4 count correspondence, base/seed applications,
native-history/Theta-count matching and PP/same-rho are manuscript-local
obligations, **not** new external inputs. The earlier source-only
dependencies are not independently compiled or replayed here.
