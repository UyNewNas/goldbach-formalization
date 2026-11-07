import ImbalancedChen.Part3ActualRoughContourIntegrandBounds
import ImbalancedChen.Part3ActualRoughContourParameters

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The actual moving height is log(x)^C+abs(tau). Its literal natural-floor
ORIGINAL modulus cutoff, the actual rough width and actual rough-prime
ceiling have uniform scalar bounds before q/tau. No analytic norm bound,
zero-free rectangle, contour identity or saving is assumed here.
-/
namespace ImbalancedChen.Part3.ActualMovingRoughHeight20261026b
noncomputable section
open RoughQuadraticLowRectangle20261026b ActualRoughContourParameters20261026b

theorem moving_rectangleLog_bound {B C L x:ℝ} (hB:0≤B) (hC:0≤C) (hL:0≤L)
    (hLC:L≤C) (hlog:2≤Real.log x) (hll:1≤Real.log (Real.log x))
    (q:ℕ) [NeZero q] (hq:(q:ℝ)≤(Real.log x)^B) (tau:ℝ)
    (htau:|tau|≤(Real.log x)^L) :
    rectangleLog q (contourT C x+|tau|)≤heightConstant B (C+1)*Real.log x:=by
  have hell:0<Real.log x:=by linarith
  have hlog1:1≤Real.log x:=by linarith
  have hT:1≤contourT C x:=Real.one_le_rpow hlog1 hC
  have htaut:|tau|≤contourT C x:=htau.trans (Real.rpow_le_rpow_of_exponent_le hlog1 hLC)
  change |tau|≤(Real.log x)^C at htaut
  have hheight:contourT C x+|tau|≤contourT (C+1) x:=by
    unfold contourT
    rw [Real.rpow_add hell,Real.rpow_one]
    have hbase:0≤(Real.log x)^C:=Real.rpow_nonneg hell.le _
    nlinarith
  have hcut:rectangleCutoff q (contourT C x+|tau|)≤heightCutoff q (C+1) x:=by
    unfold rectangleCutoff heightCutoff
    exact Nat.mul_le_mul_left q (Nat.add_le_add_right (Nat.floor_mono (add_le_add_right hheight 1)) 1)
  have hD:rectangleLog q (contourT C x+|tau|)≤heightLog q (C+1) x:=by
    unfold rectangleLog heightLog
    exact add_le_add_left (Real.log_le_log (by exact_mod_cast rectangleCutoff_pos q _)
      (by exact_mod_cast hcut)) 1
  have hq1:1≤q:=NeZero.pos q
  have hH:=heightLog_bound hB (by linarith:0≤C+1) hlog1 hll.le q hq1 hq
  have hloglog:1+Real.log (Real.log x)≤Real.log x:=by
    linarith [Real.log_le_sub_one_of_pos hell]
  have hK:0≤heightConstant B (C+1):=by
    unfold heightConstant
    nlinarith [abs_nonneg (Real.log 3)]
  exact (hD.trans hH.2).trans (mul_le_mul_of_nonneg_left hloglog hK)

theorem actual_delta_inverse_bound {d x:ℝ} (hd:0<d) (hx:1<x)
    (hll:1≤Real.log (Real.log x)) :
    0<roughDelta d x ∧ 1/roughDelta d x≤Real.log x/d:=by
  have hlog:0<Real.log x:=Real.log_pos hx
  have hll0:0<Real.log (Real.log x):=zero_lt_one.trans_le hll
  have hc:1≤(Real.log (Real.log x))^3:=one_le_pow₀ hll
  have heq:=roughDelta_eq d hx hll0
  have hpos:0<roughDelta d x:=by rw [heq];positivity
  have hlo:d/Real.log x≤roughDelta d x:=by
    rw [heq]
    exact div_le_div_of_nonneg_right (by nlinarith) hlog.le
  have hi:=one_div_le_one_div_of_le (div_pos hd hlog) hlo
  exact ⟨hpos,by simpa only [one_div_div] using hi⟩

theorem actual_rough_log_ceiling {x:ℝ} (hx:2≤x)
    (hll:1≤Real.log (Real.log x)) :
    1+Real.log (max 2 (roughZ x))≤1+Real.log x:=by
  have hx1:1<x:=by linarith
  have hc:1≤(Real.log (Real.log x))^3:=one_le_pow₀ hll
  have hexp:1/(Real.log (Real.log x))^3≤1:=(div_le_one (by linarith:0<(Real.log (Real.log x))^3)).mpr hc
  have hz:roughZ x≤x:=by
    unfold roughZ
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1.le hexp
  have hmax:max 2 (roughZ x)≤x:=max_le hx hz
  have hmaxpos:0<max 2 (roughZ x):=lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  exact add_le_add_left (Real.log_le_log hmaxpos hmax) 1

end
end ImbalancedChen.Part3.ActualMovingRoughHeight20261026b
