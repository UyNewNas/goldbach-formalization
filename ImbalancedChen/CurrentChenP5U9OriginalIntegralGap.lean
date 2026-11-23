import ImbalancedChen.CurrentChenUpsilon9HarmonicIntegral
import ImbalancedChen.CurrentNumericalTransfer

/-!
# A concrete positive mass behind the original U9 coefficient gap

The integrand and endpoints are the actual U9 logarithmic integral, not an
enclosure assumed from saved numerical output.  Its value is bounded below
by `(21/250)*log 2`.  Thus changing eight to the original `currentK` demands
a strictly positive leading saving on this same integral.

All estimates below are exact real inequalities.  There is no floating
point computation, saved quadrature premise, or U9 upper-mean premise.
-/

namespace ImbalancedChen

noncomputable section

open MeasureTheory Set

/-- The original one-dimensional U9 integrand is continuous on the entire
closed interval, including both actual half-open arithmetic endpoints. -/
theorem currentChenP5U9LogIntegrand_continuousOn :
    ContinuousOn (fun x : ℝ =>
      Real.log ((1 - x - 59 / 250) / (59 / 250)) / (x * (1 - x)))
      (Icc (19 / 125 : ℝ) (59 / 250 : ℝ)) := by
  have harg : ∀ x ∈ Icc (19 / 125 : ℝ) (59 / 250 : ℝ),
      0 < (1 - x - 59 / 250) / (59 / 250) := by
    intro x hx
    apply div_pos _ (by norm_num)
    linarith only [hx.2]
  have hden : ∀ x ∈ Icc (19 / 125 : ℝ) (59 / 250 : ℝ),
      x * (1 - x) ≠ 0 := by
    intro x hx
    apply ne_of_gt
    apply mul_pos <;> linarith only [hx.1, hx.2]
  exact ((((continuousOn_const.sub continuousOn_id).sub continuousOn_const).div_const
    (59 / 250 : ℝ)).log (fun x hx => (harg x hx).ne')).div
      (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)) hden

/-- A strictly positive pointwise floor on the literal integrand.
The logarithm argument is at least two and `x*(1-x)` is at most one. -/
theorem currentChenP5U9LogIntegrand_ge_log_two {x : ℝ}
    (hx : x ∈ Icc (19 / 125 : ℝ) (59 / 250 : ℝ)) :
    Real.log (2 : ℝ) ≤
      Real.log ((1 - x - 59 / 250) / (59 / 250)) / (x * (1 - x)) := by
  have hden : 0 < x * (1 - x) := by
    apply mul_pos <;> linarith only [hx.1, hx.2]
  have hden1 : x * (1 - x) ≤ 1 := by
    nlinarith only [sq_nonneg (x - 1 / 2)]
  have hratio : (2 : ℝ) ≤ (1 - x - 59 / 250) / (59 / 250) := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 59 / 250)).mpr
    linarith only [hx.2]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio
  have hlog0 : 0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  apply (le_div_iff₀ hden).mpr
  exact (mul_le_of_le_one_right hlog0 hden1).trans hlog

/-- An explicit positive lower mass for the genuine original J.  This
also supplies a simple exact sanity bound for future quadrature proofs. -/
theorem currentChenP5U9HarmonicIntegral_ge_log_two :
    (21 / 250 : ℝ) * Real.log (2 : ℝ) ≤ currentChenUpsilon9HarmonicIntegral := by
  have hab : (19 / 125 : ℝ) ≤ 59 / 250 := by norm_num
  have hint := currentChenP5U9LogIntegrand_continuousOn.intervalIntegrable_of_Icc (μ := volume) hab
  rw [currentChenUpsilon9HarmonicIntegral_eq_logIntegral,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  calc
    (21 / 250 : ℝ) * Real.log (2 : ℝ) =
        ∫ _x in (19 / 125 : ℝ)..(59 / 250 : ℝ), Real.log (2 : ℝ) := by
      rw [intervalIntegral.integral_const]
      norm_num [smul_eq_mul]
    _ ≤ ∫ x in (19 / 125 : ℝ)..(59 / 250 : ℝ),
        Real.log ((1 - x - 59 / 250) / (59 / 250)) / (x * (1 - x)) := by
      apply intervalIntegral.integral_mono_on hab intervalIntegrable_const hint
      intro x hx
      exact currentChenP5U9LogIntegrand_ge_log_two hx

theorem currentChenP5U9HarmonicIntegral_pos :
    0 < currentChenUpsilon9HarmonicIntegral := by
  exact lt_of_lt_of_le
    (mul_pos (by norm_num : (0 : ℝ) < 21 / 250)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    currentChenP5U9HarmonicIntegral_ge_log_two

/-- The adopted coefficient is used literally, from CurrentNumericalTransfer. -/
theorem currentChenP5U9_eight_sub_originalK :
    8 - currentK = (1547829 / 1250000 : ℝ) := by
  norm_num [currentK]

/-- Exact mass of the outstanding leading coefficient saving. -/
theorem currentChenP5U9_ordinary_sub_original_integral_cost :
    8 * currentChenUpsilon9HarmonicIntegral - currentK * currentChenUpsilon9HarmonicIntegral =
      (1547829 / 1250000 : ℝ) * currentChenUpsilon9HarmonicIntegral := by
  rw [← sub_mul, currentChenP5U9_eight_sub_originalK]

/-- The genuine integral makes the original adopted cost strictly smaller
than the proved ordinary cost.  This theorem asserts no count upper bound. -/
theorem currentChenP5U9_original_integral_cost_lt_ordinary :
    currentK * currentChenUpsilon9HarmonicIntegral <
      8 * currentChenUpsilon9HarmonicIntegral := by
  exact mul_lt_mul_of_pos_right (by norm_num [currentK])
    currentChenP5U9HarmonicIntegral_pos

/-- A concrete positive lower bound for the missing leading saving. -/
theorem currentChenP5U9_ordinary_sub_original_integral_cost_ge :
    (1547829 / 1250000 : ℝ) * ((21 / 250 : ℝ) * Real.log (2 : ℝ)) ≤
      8 * currentChenUpsilon9HarmonicIntegral - currentK * currentChenUpsilon9HarmonicIntegral := by
  rw [currentChenP5U9_ordinary_sub_original_integral_cost]
  exact mul_le_mul_of_nonneg_left currentChenP5U9HarmonicIntegral_ge_log_two (by norm_num)

end

end ImbalancedChen
