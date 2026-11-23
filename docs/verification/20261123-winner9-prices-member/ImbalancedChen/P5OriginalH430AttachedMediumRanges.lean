import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A whole upper-endpoint assignment admits the manuscript's third-group
beta attachment. The residue is still measured at its actual exponent q;
the medium parameter is U=A*x^z and sigma=z/2000. -/
namespace ImbalancedChen.P5OriginalH430AttachedMediumRanges
noncomputable section

theorem attached_medium_ranges {x z q alpha A a b c M : ℝ} (hx : 1<x) (hz : 0<z)
    (hq : q≤alpha) (hA : 0<A) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hM : 0<M)
    (hbeta : M≤x^(z/8)) (h1 : a≤A) (h2 : A^2*b*c^2 ≤ x^(1-3*z))
    (h3 : x^(7*alpha/32)*A*a*b^5*c^2 ≤ x^(2-4*z))
    (h4 : (A*c/b)^(7/16:ℝ)*A*a*b^5*c^2 ≤ x^(2-39*z/8)) :
    let U := A*x^z
    let Q3 := M*c
    let sigma := z/2000
    a < U*x^(-sigma) ∧
    U^2*b*Q3^2 < x^(1-8*sigma) ∧
    (x^q)^(7/32:ℝ)*U*a*b^5*Q3^2 < x^(2-15*sigma) ∧
    U^(1+7/16:ℝ)*a*b^(5-7/16:ℝ)*Q3^(2+7/16:ℝ) < x^(2-15*sigma) := by
  dsimp only
  have hx0 := zero_lt_one.trans hx
  have hL := Real.log_pos hx
  have hzL := mul_pos hz hL
  have hqL := mul_le_mul_of_nonneg_right hq hL.le
  have hbL := (Real.le_rpow_iff_log_le hM hx0).mp hbeta
  have haL := Real.log_le_log ha h1
  have A2 := (Real.le_rpow_iff_log_le (by positivity) hx0).mp h2
  have A3 := (Real.le_rpow_iff_log_le (by positivity) hx0).mp h3
  have A4 := (Real.le_rpow_iff_log_le (by positivity) hx0).mp h4
  simp (disch := positivity) only [Real.log_mul,Real.log_rpow,Real.log_div,Real.log_pow,Nat.cast_ofNat] at A2 A3 A4
  refine ⟨?_,?_,?_,?_⟩
  · apply (Real.log_lt_log_iff ha (by positivity)).mp
    simp (disch := positivity) only [Real.log_mul,Real.log_rpow]
    nlinarith only [haL,hzL]
  · apply (Real.lt_rpow_iff_log_lt (by positivity) hx0).mpr
    simp (disch := positivity) only [Real.log_mul,Real.log_rpow,Real.log_pow,Nat.cast_ofNat]
    nlinarith only [A2,hbL,hzL]
  · apply (Real.lt_rpow_iff_log_lt (by positivity) hx0).mpr
    simp (disch := positivity) only [Real.log_mul,Real.log_rpow,Real.log_pow,Nat.cast_ofNat]
    nlinarith only [A3,hbL,hzL,hqL]
  · apply (Real.lt_rpow_iff_log_lt (by positivity) hx0).mpr
    simp (disch := positivity) only [Real.log_mul,Real.log_rpow,Real.log_pow,Nat.cast_ofNat]
    nlinarith only [A4,hbL,hzL]

end
end ImbalancedChen.P5OriginalH430AttachedMediumRanges
