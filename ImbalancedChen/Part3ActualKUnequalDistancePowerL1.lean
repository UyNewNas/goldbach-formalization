import ImbalancedChen.Part3ActualKUnequalHyperbolicDistance
import ImbalancedChen.Part3RealOrderKMellinReduction
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Absolute convergence of the literal unequal hyperbolic-distance power
integral on Re(s)>2*|Re(nu)|. The squared distance is bounded below by
2*a*b*cosh(v). Its negative real power is therefore dominated by a
constant times the already proved real cosh Mellin density at exponent
Re(s)/2. Positive square roots and principal complex powers are related
by an explicit logarithm identity. This supplies the outer L1 input for
the genuine scaled-K0 Mellin Fubini argument; no final transform is a
hypothesis and no hypergeometric function is introduced.
-/

namespace ImbalancedChen.Part3.ActualKUnequalDistancePowerL120261026b

noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly
open ActualKUnequalHyperbolicDistance20261026b
open RealOrderKMellinReduction20261025a (mellinDensity mellinDensity_integrable)

def squaredDistance (a b v : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 + 2 * a * b * Real.cosh v

theorem squaredDistance_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (v : ℝ) :
    0 < squaredDistance a b v := by
  unfold squaredDistance
  have hcosh := Real.cosh_pos v
  positivity

/-- The exact scaling of the actual square-root distance. -/
theorem hyperbolicDistance_mul (a b v : ℝ) {q : ℝ} (hq : 0 < q) :
    hyperbolicDistance (a * q) (b * q) v = hyperbolicDistance a b v * q := by
  have hp : (a * q) ^ 2 + (b * q) ^ 2 + 2 * (a * q) * (b * q) * Real.cosh v =
      q ^ 2 * (a ^ 2 + b ^ 2 + 2 * a * b * Real.cosh v) := by ring
  unfold hyperbolicDistance
  rw [hp, Real.sqrt_mul (sq_nonneg q), Real.sqrt_sq hq.le]
  ring

theorem distance_negative_rpow_bound {a b sigma : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hsigma : 0 < sigma) (v : ℝ) :
    hyperbolicDistance a b v ^ (-sigma) ≤
      (2 * a * b) ^ (-sigma / 2) * (1 / Real.cosh v) ^ (sigma / 2) := by
  have hR := squaredDistance_pos ha hb v
  have hbase : 0 < 2 * a * b * Real.cosh v :=
    mul_pos (mul_pos (mul_pos (by norm_num) ha) hb) (Real.cosh_pos v)
  have hlower : 2 * a * b * Real.cosh v ≤ squaredDistance a b v := by
    unfold squaredDistance
    nlinarith [sq_nonneg a, sq_nonneg b]
  have hp : hyperbolicDistance a b v ^ (-sigma) = squaredDistance a b v ^ (-sigma / 2) := by
    change (Real.sqrt (squaredDistance a b v)) ^ (-sigma) = _
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [hp]
  calc
    _ ≤ (2 * a * b * Real.cosh v) ^ (-sigma / 2) :=
      Real.rpow_le_rpow_of_nonpos hbase hlower (by linarith)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 2 * a * b) (Real.cosh_pos v).le]
      congr 1
      rw [show -sigma / 2 = -(sigma / 2) by ring, Real.rpow_neg_eq_inv_rpow, one_div]

def distancePowerNorm (nu : ℂ) (sigma a b v : ℝ) : ℝ :=
  ‖Complex.cosh (nu * (v : ℂ))‖ * hyperbolicDistance a b v ^ (-sigma)

theorem distancePowerNorm_nonneg (nu : ℂ) (sigma a b v : ℝ) :
    0 ≤ distancePowerNorm nu sigma a b v := by
  unfold distancePowerNorm
  exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

/-- Comparison with an existing genuine cosh Mellin convergence theorem. -/
theorem distancePowerNorm_le_mellinDensity (nu : ℂ) {sigma a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hsigma : 0 < sigma) (v : ℝ) :
    distancePowerNorm nu sigma a b v ≤
      (2 * a * b) ^ (-sigma / 2) * mellinDensity nu.re (sigma / 2) v := by
  have hcosh : ‖Complex.cosh (nu * (v : ℂ))‖ ≤ Real.cosh (nu.re * v) := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
      norm_complex_cosh_le_real_cosh (nu * (v : ℂ))
  have hpower := distance_negative_rpow_bound ha hb hsigma v
  unfold distancePowerNorm
  calc
    _ ≤ Real.cosh (nu.re * v) *
        ((2 * a * b) ^ (-sigma / 2) * (1 / Real.cosh v) ^ (sigma / 2)) :=
      mul_le_mul hcosh hpower (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
        (Real.cosh_pos _).le
    _ = _ := by unfold mellinDensity; ring

theorem distancePowerNorm_integrable {nu : ℂ} {sigma a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : 2 * |nu.re| < sigma) :
    IntegrableOn (distancePowerNorm nu sigma a b) (Ioi 0) := by
  have hsigma : 0 < sigma := by linarith [abs_nonneg nu.re]
  have hgap : |nu.re| < sigma / 2 := by linarith
  have hm : Measurable (distancePowerNorm nu sigma a b) := by
    unfold distancePowerNorm hyperbolicDistance
    fun_prop
  apply ((mellinDensity_integrable hgap).const_mul ((2 * a * b) ^ (-sigma / 2))).mono'
    hm.aestronglyMeasurable
  exact Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (distancePowerNorm_nonneg nu sigma a b v)]
    exact distancePowerNorm_le_mellinDensity nu ha hb hsigma v

def distancePowerKernel (nu s : ℂ) (a b v : ℝ) : ℂ :=
  Complex.cosh (nu * (v : ℂ)) * (hyperbolicDistance a b v : ℂ) ^ (-s)

theorem distancePowerKernel_norm (nu s : ℂ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (v : ℝ) :
    ‖distancePowerKernel nu s a b v‖ = distancePowerNorm nu s.re a b v := by
  unfold distancePowerKernel distancePowerNorm
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hyperbolicDistance_pos ha hb v),
    Complex.neg_re]

theorem distancePowerKernel_integrable {nu s : ℂ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : 2 * |nu.re| < s.re) :
    IntegrableOn (distancePowerKernel nu s a b) (Ioi 0) := by
  have hm : Measurable (distancePowerKernel nu s a b) := by
    unfold distancePowerKernel hyperbolicDistance
    fun_prop
  apply (distancePowerNorm_integrable ha hb hs).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun v => le_of_eq (distancePowerKernel_norm nu s ha hb v)

/-- Positive square roots use the real logarithm, so this principal
complex power has no branch ambiguity. -/
theorem hyperbolicDistance_cpow (s : ℂ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (v : ℝ) :
    (hyperbolicDistance a b v : ℂ) ^ (-s) = (squaredDistance a b v : ℂ) ^ (-s / 2) := by
  have hD := hyperbolicDistance_pos ha hb v
  have hR := squaredDistance_pos ha hb v
  have hlog : Complex.log (hyperbolicDistance a b v : ℂ) =
      Complex.log (squaredDistance a b v : ℂ) / 2 := by
    rw [← Complex.ofReal_log hD.le, ← Complex.ofReal_log hR.le]
    change ((Real.log (Real.sqrt (squaredDistance a b v)) : ℝ) : ℂ) = _
    rw [Real.log_sqrt hR.le]
    push_cast
    ring
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne'), hlog]
  congr 1
  ring

end
end ImbalancedChen.Part3.ActualKUnequalDistancePowerL120261026b
