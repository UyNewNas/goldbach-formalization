import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace ImbalancedChen.P3OriginalPrimeRoughThreshold

/-- The original pre-HB roughness function is strictly above 2 on the
entire physical chart-argument range. This uniform lower bound also
applies to the very first dyadic chart. -/
theorem two_lt_rough_threshold {x : ℝ} (hx : 4 ≤ x) :
    2 < x^(1/(Real.log (Real.log x))^3) := by
  have hx0 : 0 < x := by linarith
  have hl : 1 < Real.log x := (Real.lt_log_iff_exp_lt hx0).mpr
    (Real.exp_one_lt_three.trans (by linarith))
  let s := Real.log (Real.log x)
  have hs : 0 < s := Real.log_pos hl
  have hsmall : (8/3 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hlin : (8/3 : ℝ)*(s/3) ≤ Real.exp (s/3) := by
    calc
      _ ≤ Real.exp 1*(s/3) := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ ≤ Real.exp 1*Real.exp (s/3-1) := mul_le_mul_of_nonneg_left
        (by linarith only [Real.add_one_le_exp (s/3-1)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hcube := pow_le_pow_left₀ (by positivity : 0 ≤ (8/3 : ℝ)*(s/3)) hlin 3
  have hid : Real.exp (s/3)^3 = Real.log x := by
    rw [← Real.exp_nat_mul, show ((3 : ℕ) : ℝ) * (s / 3) = s by push_cast; ring]
    exact Real.exp_log (by linarith)
  rw [hid] at hcube
  have hlog : Real.log 2 < (7/10 : ℝ) := by linarith only [Real.log_two_lt_d9]
  have hmin : (7/10 : ℝ)*s^3 < ((8/3 : ℝ)*(s/3))^3 := by
    nlinarith only [pow_pos hs 3]
  have hfinal : Real.log 2 < Real.log x / s^3 := (lt_div_iff₀ (pow_pos hs 3)).mpr
    ((mul_lt_mul_of_pos_right hlog (pow_pos hs 3)).trans_le (hmin.le.trans hcube))
  rw [Real.rpow_def_of_pos hx0]
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mp
  simpa only [div_eq_mul_inv, one_mul] using hfinal

end ImbalancedChen.P3OriginalPrimeRoughThreshold
