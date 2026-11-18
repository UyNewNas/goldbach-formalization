import ImbalancedChen.Part5OriginalH430ActualD6RationalLower
import ImbalancedChen.P2EnhancedSeedInheritedCellBounds

/-!
P5.6 / h34 — two ACTUAL rational Darboux cells for the unchanged D6
untruncated outer integral. This is a manuscript-INTERNAL quantitative
increment. It does not assume the desired D6 integral value, the
seven-piece 0.65 target, a fixed analytic intercept, or a CLOSED-CELL
licence. Each cell consumes the existing rational-log check_sound theorem.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualD6BisectedRational

noncomputable section
open Set MeasureTheory
open scoped Interval
open P2EnhancedSeedInheritedCellBounds
open P2EnhancedSeedActualSevenLogIdentity
open P2EnhancedSeedActualFeedbackAssembly

/-- The exact rational midpoint of the ORIGINAL D6 outer interval. -/
private def d6Mid : ℚ := 20175 / 80131

theorem midpoint_within_true_d6 :
    (50 / 227 : ℚ) ≤ d6Mid ∧ d6Mid ≤ (100 / 353 : ℚ) := by
  norm_num [d6Mid]

/-- For ANY internal rational split, add two true interval-integral
soundness bounds. All numerical content is contained in the two
unchanged d6CellLower calls; the split identity is analytic, not
a new axiom or floating-point quadrature. -/
theorem d6_two_cell_integral_lower (m : ℚ)
    (hmL : (50 / 227 : ℚ) ≤ m)
    (hmR : m ≤ (100 / 353 : ℚ)) :
    (((m - (50 / 227 : ℚ)) *
       d6CellLower 2 (50 / 227) m +
       ((100 / 353 : ℚ) - m) *
       d6CellLower 2 m (100 / 353) : ℚ) : ℝ) ≤ d6Log := by
  have hL := d6_rational_cell_integral_lower
    2 (50 / 227 : ℚ) m (by norm_num) hmL hmR
  have hR := d6_rational_cell_integral_lower
    2 m (100 / 353 : ℚ) hmL hmR (by norm_num)
  have hmLR : (50 / 227 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmL
  have hmRR : (m : ℝ) ≤ (100 / 353 : ℝ) := by exact_mod_cast hmR
  have hContinuousL : ContinuousOn d6OuterSlice
      (Icc (50 / 227 : ℝ) (m : ℝ)) :=
    continuousOn_d6OuterSlice.mono (by
      intro u hu
      exact ⟨hu.1, hu.2.trans hmRR⟩)
  have hContinuousR : ContinuousOn d6OuterSlice
      (Icc (m : ℝ) (100 / 353 : ℝ)) :=
    continuousOn_d6OuterSlice.mono (by
      intro u hu
      exact ⟨hmLR.trans hu.1, hu.2⟩)
  have hIntL : IntervalIntegrable d6OuterSlice volume
      (50 / 227 : ℝ) (m : ℝ) :=
    hContinuousL.intervalIntegrable_of_Icc hmLR
  have hIntR : IntervalIntegrable d6OuterSlice volume
      (m : ℝ) (100 / 353 : ℝ) :=
    hContinuousR.intervalIntegrable_of_Icc hmRR
  have hSplit :
      (∫ u in (50 / 227 : ℝ)..(m : ℝ), d6OuterSlice u) +
      (∫ u in (m : ℝ)..(100 / 353 : ℝ), d6OuterSlice u) =
      (∫ u in (50 / 227 : ℝ)..(100 / 353 : ℝ), d6OuterSlice u) :=
    intervalIntegral.integral_add_adjacent_intervals hIntL hIntR
  have hFull :
      (∫ u in (50 / 227 : ℝ)..(100 / 353 : ℝ),
        d6OuterSlice u) = d6Log := by
    unfold d6Log
    rw [integral_Ioo_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le
        (by norm_num : (50 / 227 : ℝ) ≤ 100 / 353)]
    rfl
  calc
    (((m - (50 / 227 : ℚ)) *
       d6CellLower 2 (50 / 227) m +
       ((100 / 353 : ℚ) - m) *
       d6CellLower 2 m (100 / 353) : ℚ) : ℝ) =
      (((m - (50 / 227 : ℚ)) *
        d6CellLower 2 (50 / 227) m : ℚ) : ℝ) +
      ((((100 / 353 : ℚ) - m) *
        d6CellLower 2 m (100 / 353) : ℚ) : ℝ) := by
        exact Rat.cast_add _ _
    _ ≤
      (∫ u in (50 / 227 : ℝ)..(m : ℝ), d6OuterSlice u) +
      (∫ u in (m : ℝ)..(100 / 353 : ℝ), d6OuterSlice u) :=
        add_le_add hL hR
    _ = (∫ u in (50 / 227 : ℝ)..(100 / 353 : ℝ),
      d6OuterSlice u) := hSplit
    _ = d6Log := hFull

/-- Independently checked rational arithmetic:
the two two-term cells total approximately 0.1100301554036517.
The Lean goal itself is entirely exact; no decimal bound is assumed. -/
theorem two_cell_rational_arithmetic :
    (11 / 100 : ℝ) ≤
      (((d6Mid - (50 / 227 : ℚ)) *
        d6CellLower 2 (50 / 227) d6Mid +
        ((100 / 353 : ℚ) - d6Mid) *
        d6CellLower 2 d6Mid (100 / 353) : ℚ) : ℝ) := by
  norm_num [d6Mid, d6CellLower, d6RationalArgument,
    ImbalancedChen.Certificates.logSeriesLower,
    ImbalancedChen.Certificates.logParameter, Finset.sum_range_succ]

/-- Two cells replace the previous single-cell D6 >= 103/1000
candidate by a sharper actual lower bound >= 11/100. -/
theorem actual_d6Log_ge_11_over_100 :
    (11 / 100 : ℝ) ≤ d6Log := by
  exact two_cell_rational_arithmetic.trans
    (d6_two_cell_integral_lower d6Mid
      midpoint_within_true_d6.1 midpoint_within_true_d6.2)

/-- Still only a PARTIAL lower bound for the unchanged seven-piece
coefficient. The other six domains are merely used as nonnegative;
lambda >= 13/100 remains OPEN. -/
theorem actual_lambda_ge_11_over_500 :
    (11 / 500 : ℝ) ≤ lambda := by
  have hD6 := actual_d6Log_ge_11_over_100
  have hLambda :=
    Part5OriginalH430ActualD6RationalLower.actual_lambda_ge_d6_over_five
  linarith

theorem actual_feedback_one_fiftieth_ge_11_over_25000 :
    (11 / 25000 : ℝ) ≤ actualFeedback (1 / 50) := by
  rw [actualFeedback_one_fiftieth]
  have h := actual_lambda_ge_11_over_500
  linarith

end
end ImbalancedChen.Part5OriginalH430ActualD6BisectedRational
