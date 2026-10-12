import ImbalancedChen.CurrentChenSummedBridge
import ImbalancedChen.CurrentNumericalTransfer

/-!
# Finite lower-count budgets on the current Chen scale

The actual paired prime sum is bounded above by `4 * D12`, with the
already proved squareful-receiver and unit loss. Consequently its target
leading coefficient is `4 * currentC = 49044063/6250000`.

This file only records finite consequences of a displayed weight value
and a displayed error budget. It supplies no estimate for any of the
eleven means, no adopted pair selector, and no eventual `hLower`. The
existing negligibility theorem in `CurrentChenSummedBridge` can supply
the count-error budget uniformly in the selector once the actual mean
estimate has been proved separately. That theorem is not reproved here.
-/

namespace ImbalancedChen

noncomputable section

/-- The exact leading coefficient required on the weight scale. -/
theorem currentChen_four_currentC :
    4 * currentC = (49044063 : ℝ) / 6250000 := by
  norm_num [currentC]

/-- A finite lower value of the actual current paired sum gives a finite
count bound, with the coefficient and both exception costs divided by
four. In particular the receiver-one loss is exactly one at this scale.
The displayed `hweight` is a finite premise, not an analytic supplier. -/
theorem currentChen_lower_scale_from_finite_weight_bound
    {N : ℕ} (E : ℕ × ℕ → Prop) {etaMean : ℝ}
    (hN : 1 ≤ (N : ℝ))
    (hA : 1 < (N : ℝ) ^ (417 / 5000 : ℝ))
    (hweight : (4 * currentC - etaMean) * singularNormalization N ≤
      currentChenPairedPrimeSum N E) :
    (currentC - etaMean / 4) * singularNormalization N -
      ((123 : ℝ) / 2 *
        ((N : ℝ) / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1)) + 1) ≤
      (D12 N : ℝ) := by
  have hcount := currentChenPairedPrimeSum_le_four_D12_add_error N E hN hA
  nlinarith only [hweight, hcount]

/-- Finite error allocation for the current scale. Mean loss `etaMean`
and count loss `etaCount` are measured against the same normalization.
Their sum must be at most `4 * epsilon` to obtain a count loss `epsilon`.

The count premise is supplied on sufficiently large targets by the
already proved uniform-selector normalized-error bridge. Both inputs
here are ordinary inequalities at this one value of `N`; no whole-mean
asymptotic is introduced as a placeholder hypothesis. -/
theorem currentChen_lower_scale_of_finite_budgets
    {N : ℕ} (E : ℕ × ℕ → Prop) {epsilon etaMean etaCount : ℝ}
    (hbudget : etaMean + etaCount ≤ 4 * epsilon)
    (hweight : (4 * currentC - etaMean) * singularNormalization N ≤
      currentChenPairedPrimeSum N E)
    (hcount : currentChenPairedPrimeSum N E -
      etaCount * singularNormalization N ≤ 4 * (D12 N : ℝ)) :
    (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ) := by
  have hH : 0 ≤ singularNormalization N := by
    exact div_nonneg
      (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have hbudgetH := mul_le_mul_of_nonneg_right hbudget hH
  nlinarith only [hweight, hcount, hbudgetH]

/-- The balanced finite allocation uses `2 * epsilon` for each loss,
giving the exact target count coefficient `currentC - epsilon`.
This records the allocation only; neither inequality is asserted here
for the adopted policy on all sufficiently large even targets. -/
theorem currentChen_lower_scale_of_equal_finite_budgets
    {N : ℕ} (E : ℕ × ℕ → Prop) {epsilon : ℝ}
    (hweight : (4 * currentC - 2 * epsilon) * singularNormalization N ≤
      currentChenPairedPrimeSum N E)
    (hcount : currentChenPairedPrimeSum N E -
      (2 * epsilon) * singularNormalization N ≤ 4 * (D12 N : ℝ)) :
    (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ) := by
  exact currentChen_lower_scale_of_finite_budgets E
    (by linarith : 2 * epsilon + 2 * epsilon ≤ 4 * epsilon) hweight hcount

end

end ImbalancedChen
