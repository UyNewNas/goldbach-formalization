import ImbalancedChen.Part3ActualKZeroGlobalLogBound
import ImbalancedChen.Part3ImaginaryKExponentialOrderBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# An order-dependent contour bound for the actual K integral

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The proved contour shift is used at theta = pi/2 - 1/(1+abs(tau)).
The shrinking cosine costs only log(1+abs(tau)), by the global integral
bound for K0. All constants are uniform for q >= a > 0. This is an
analytic bound for the actual integral, not a spectral measure theorem.
-/

namespace ImbalancedChen.Part3.ImaginaryKAdaptiveContourBound20261025a

noncomputable section
open Complex
open RealOrderKExceptionalSourceOnly ComplexOrderKBridgeSourceOnly
open ImaginaryOrderKBesselSourceOnly
open ActualKZeroGlobalLogBound20261025a ImaginaryKExponentialOrderBound20261025a

def adaptiveDelta (tau : ℝ) : ℝ := 1 / (1 + |tau|)
def adaptiveTheta (tau : ℝ) : ℝ := Real.pi / 2 - adaptiveDelta tau

theorem adaptiveDelta_pos (tau : ℝ) : 0 < adaptiveDelta tau := by
  unfold adaptiveDelta
  positivity

theorem adaptiveDelta_le_one (tau : ℝ) : adaptiveDelta tau ≤ 1 := by
  unfold adaptiveDelta
  apply (div_le_iff₀ (by positivity : 0 < 1 + |tau|)).mpr
  nlinarith [abs_nonneg tau]

theorem adaptiveDelta_mul_one_add_abs (tau : ℝ) :
    adaptiveDelta tau * (1 + |tau|) = 1 := by
  unfold adaptiveDelta
  field_simp [ne_of_gt (show 0 < 1 + |tau| by positivity)]

theorem adaptiveDelta_mul_abs_le_one (tau : ℝ) : adaptiveDelta tau * |tau| ≤ 1 := by
  have he := adaptiveDelta_mul_one_add_abs tau
  have hp := adaptiveDelta_pos tau
  nlinarith

theorem adaptiveTheta_pos (tau : ℝ) : 0 < adaptiveTheta tau := by
  unfold adaptiveTheta
  linarith [adaptiveDelta_le_one tau, Real.pi_gt_three]

theorem adaptiveTheta_lt_pi_div_two (tau : ℝ) : adaptiveTheta tau < Real.pi / 2 := by
  unfold adaptiveTheta
  linarith [adaptiveDelta_pos tau]

/-- The approach to the edge of the holomorphic strip is quantitatively
controlled, including tau = 0. -/
theorem cos_adaptiveTheta_lower (tau : ℝ) :
    adaptiveDelta tau / 2 ≤ Real.cos (adaptiveTheta tau) := by
  rw [adaptiveTheta, Real.cos_pi_div_two_sub]
  have hd := adaptiveDelta_pos tau
  have hdpi : adaptiveDelta tau ≤ Real.pi / 2 := by
    linarith [adaptiveDelta_le_one tau, Real.pi_gt_three]
  have hs := Real.mul_le_sin hd.le hdpi
  have hconst : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_four]
  have hm := mul_le_mul_of_nonneg_right hconst hd.le
  nlinarith

theorem argument_adaptiveTheta_lower {a q : ℝ} (ha : 0 < a) (haq : a ≤ q)
    (tau : ℝ) : a / (2 * (1 + |tau|)) ≤ q * Real.cos (adaptiveTheta tau) := by
  have hc := cos_adaptiveTheta_lower tau
  have hd := adaptiveDelta_pos tau
  have hq : 0 < q := ha.trans_le haq
  have h1 := mul_le_mul_of_nonneg_left hc hq.le
  have h2 := mul_le_mul_of_nonneg_right haq (div_nonneg hd.le (by norm_num))
  have he : a / (2 * (1 + |tau|)) = a * (adaptiveDelta tau / 2) := by
    unfold adaptiveDelta
    field_simp [ne_of_gt (show 0 < 1 + |tau| by positivity)]
  rw [he]
  exact h2.trans h1

/-- The logarithmic cutoff pays only one logarithm in the order, with an
explicit constant depending on the lower argument cutoff. -/
theorem zeroOrderCutoff_le_log_order {a x T : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hT : 0 ≤ T) (hax : a / (2 * (1 + T)) ≤ x) :
    max 0 (Real.log (2 / x)) ≤ Real.log (1 + T) + max 0 (Real.log (4 / a)) := by
  have hTpos : 0 < 1 + T := by linarith
  have hden : 0 < a / (2 * (1 + T)) := by positivity
  have hr : 2 / x ≤ (4 / a) * (1 + T) := by
    calc
      _ ≤ 2 / (a / (2 * (1 + T))) :=
        div_le_div_of_nonneg_left (by norm_num) hden hax
      _ = _ := by field_simp [ne_of_gt ha, ne_of_gt hTpos] <;> ring
  have hl := Real.log_le_log (div_pos (by norm_num) hx) hr
  rw [Real.log_mul (ne_of_gt (div_pos (by norm_num) ha)) (ne_of_gt hTpos)] at hl
  apply max_le
  · exact add_nonneg (Real.log_nonneg (by linarith)) (le_max_left _ _)
  · linarith [le_max_right (0 : ℝ) (Real.log (4 / a))]

theorem realOrderK_zero_adaptive_le {a q : ℝ} (ha : 0 < a) (haq : a ≤ q)
    (tau : ℝ) :
    realOrderK 0 (q * Real.cos (adaptiveTheta tau)) ≤
      Real.log (1 + |tau|) + max 0 (Real.log (4 / a)) + 1 := by
  have hq : 0 < q := ha.trans_le haq
  have hc : 0 < Real.cos (adaptiveTheta tau) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [adaptiveTheta_pos tau, Real.pi_pos],
      adaptiveTheta_lt_pi_div_two tau⟩
  have hx : 0 < q * Real.cos (adaptiveTheta tau) := mul_pos hq hc
  have hk := realOrderK_zero_le_log hx
  have hl := zeroOrderCutoff_le_log_order ha hx (abs_nonneg tau)
    (argument_adaptiveTheta_lower ha haq tau)
  have he : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  linarith

/-- Choosing the contour height after fixing tau recovers the full
exp(-pi*abs(tau)/2) decay at a uniform logarithmic cost. -/
theorem complexOrderK_imaginary_norm_le_adaptive {a q : ℝ}
    (ha : 0 < a) (haq : a ≤ q) (tau : ℝ) :
    ‖complexOrderK ((tau : ℂ) * I) q‖ ≤
      Real.exp 1 * Real.exp (-Real.pi * |tau| / 2) *
        (Real.log (1 + |tau|) + max 0 (Real.log (4 / a)) + 1) := by
  have hq : 0 < q := ha.trans_le haq
  have hcontour := complexOrderK_imaginary_norm_le_exp_abs hq
    (adaptiveTheta_pos tau) (adaptiveTheta_lt_pi_div_two tau) tau
  have hk := realOrderK_zero_adaptive_le ha haq tau
  have hexp : Real.exp (-adaptiveTheta tau * |tau|) ≤
      Real.exp 1 * Real.exp (-Real.pi * |tau| / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold adaptiveTheta
    nlinarith [adaptiveDelta_mul_abs_le_one tau]
  have hbracket : 0 ≤ Real.log (1 + |tau|) + max 0 (Real.log (4 / a)) + 1 := by
    have hlog := Real.log_nonneg (show 1 ≤ 1 + |tau| by linarith [abs_nonneg tau])
    have hm := le_max_left (0 : ℝ) (Real.log (4 / a))
    linarith
  calc
    _ ≤ Real.exp (-adaptiveTheta tau * |tau|) *
        realOrderK 0 (q * Real.cos (adaptiveTheta tau)) := hcontour
    _ ≤ Real.exp (-adaptiveTheta tau * |tau|) *
        (Real.log (1 + |tau|) + max 0 (Real.log (4 / a)) + 1) :=
      mul_le_mul_of_nonneg_left hk (Real.exp_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp hbracket

/-- Literal original convention tau=2*t: exp(-pi*abs(t)), with the
logarithmic factor log(1+2*abs(t)). Every factor two is explicit. -/
theorem imaginaryOrderK_abs_le_adaptive {a q : ℝ}
    (ha : 0 < a) (haq : a ≤ q) (t : ℝ) :
    |imaginaryOrderK t q| ≤
      Real.exp 1 * Real.exp (-Real.pi * |t|) *
        (Real.log (1 + 2 * |t|) + max 0 (Real.log (4 / a)) + 1) := by
  have h := complexOrderK_imaginary_norm_le_adaptive ha haq (2 * t)
  rw [complexOrderK_imaginary, Complex.norm_real, Real.norm_eq_abs] at h
  have ht : |2 * t| = 2 * |t| := by rw [abs_mul]; norm_num
  have he : -Real.pi * (2 * |t|) / 2 = -Real.pi * |t| := by ring
  simpa only [ht, he] using h

end
end ImbalancedChen.Part3.ImaginaryKAdaptiveContourBound20261025a
