import ImbalancedChen.Part3RealOrderKExceptional
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Positive-axis Laplace realization of the actual real-order K integral

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual realOrderK is the integral of exp(-q*cosh u)*cosh(alpha*u)
over u>0. An elementary Gaussian bound proves convergence of both tilted
exponential terms for every real order. The substitution t=exp u and
reflection of the negative half-line then produce the positive-axis
Laplace integral. No Bessel Fourier formula is assumed.
-/

namespace ImbalancedChen.Part3.RealOrderKPositiveLaplace

noncomputable section
open Set MeasureTheory
open RealOrderKExceptionalSourceOnly

def tiltedCoshDensity (α q u : ℝ) : ℝ := Real.exp (-q * Real.cosh u + α * u)

def positiveLaplaceDensity (α q t : ℝ) : ℝ :=
  t ^ (α - 1) * Real.exp (-(q / 2) * (t + t⁻¹))

private theorem cosh_quadratic (u : ℝ) : u ^ 2 / 8 ≤ Real.cosh u := by
  have hu : 0 ≤ |u| := abs_nonneg u
  have he := Real.add_one_le_exp (|u| / 2)
  have hs : (|u| / 2 + 1) ^ 2 ≤ (Real.exp (|u| / 2)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he)
      (add_nonneg (Real.exp_nonneg (|u| / 2)) (by linarith : 0 ≤ |u| / 2 + 1))]
  have hexp : Real.exp |u| = (Real.exp (|u| / 2)) ^ 2 := by
    calc
      Real.exp |u| = Real.exp (|u| / 2 + |u| / 2) := by congr 1 <;> ring
      _ = Real.exp (|u| / 2) * Real.exp (|u| / 2) := Real.exp_add _ _
      _ = _ := by ring
  have hcosh : |u| ^ 2 / 8 ≤ Real.cosh |u| := by
    rw [Real.cosh_eq, hexp]
    nlinarith [Real.exp_pos (-|u|)]
  simpa only [sq_abs, Real.cosh_abs] using hcosh

theorem tiltedCoshDensity_integrable (α : ℝ) {q : ℝ} (hq : 0 < q) :
    Integrable (tiltedCoshDensity α q) := by
  have hgC := integrable_cexp_quadratic
    (b := ((q / 8 : ℝ) : ℂ))
    (by simpa only [Complex.ofReal_re] using (div_pos hq (by norm_num : (0 : ℝ) < 8)))
    (α : ℂ) 0
  have hg : Integrable (fun u : ℝ => Real.exp (-(q / 8) * u ^ 2 + α * u)) := by
    convert hgC.re using 1
    funext u
    simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
  have hc : Continuous (tiltedCoshDensity α q) := by
    unfold tiltedCoshDensity
    fun_prop
  apply hg.mono' hc.aestronglyMeasurable
  filter_upwards [] with u
  change ‖Real.exp (-q * Real.cosh u + α * u)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left (cosh_quadratic u) hq.le
  nlinarith only [hmul]

theorem tiltedCoshDensity_reflect (α q u : ℝ) :
    tiltedCoshDensity α q (-u) = tiltedCoshDensity (-α) q u := by
  unfold tiltedCoshDensity
  rw [Real.cosh_neg]
  congr 1
  ring

theorem tiltedCoshDensity_pair (α q u : ℝ) :
    tiltedCoshDensity (-α) q u + tiltedCoshDensity α q u =
      2 * realOrderIntegrand α q u := by
  unfold tiltedCoshDensity realOrderIntegrand
  rw [Real.exp_add, Real.exp_add, Real.cosh_eq]
  have he : -α * u = -(α * u) := by ring
  rw [he]
  ring

theorem tiltedCoshDensity_integral (α : ℝ) {q : ℝ} (hq : 0 < q) :
    (∫ u : ℝ, tiltedCoshDensity α q u) = 2 * realOrderK α q := by
  have hf := tiltedCoshDensity_integrable α hq
  have hn := tiltedCoshDensity_integrable (-α) hq
  calc
    _ = (∫ u in Iic (0 : ℝ), tiltedCoshDensity α q u) +
        ∫ u in Ioi (0 : ℝ), tiltedCoshDensity α q u :=
      (intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn).symm
    _ = (∫ u in Ioi (0 : ℝ), tiltedCoshDensity (-α) q u) +
        ∫ u in Ioi (0 : ℝ), tiltedCoshDensity α q u := by
      congr 1
      simpa only [neg_zero, tiltedCoshDensity_reflect] using
        (integral_comp_neg_Ioi (0 : ℝ) (tiltedCoshDensity α q)).symm
    _ = ∫ u in Ioi (0 : ℝ),
        (tiltedCoshDensity (-α) q u + tiltedCoshDensity α q u) :=
      (integral_add hn.integrableOn hf.integrableOn).symm
    _ = _ := by
      simp_rw [tiltedCoshDensity_pair]
      rw [integral_const_mul]
      rfl

theorem positiveLaplaceDensity_exp_pullback (α q u : ℝ) :
    Real.exp u * positiveLaplaceDensity α q (Real.exp u) =
      tiltedCoshDensity α q u := by
  unfold positiveLaplaceDensity tiltedCoshDensity
  rw [← Real.exp_mul, ← Real.exp_neg, Real.cosh_eq]
  rw [← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The actual K definition evaluated as a positive Laplace integral,
valid for every real order and every positive argument. -/
theorem positiveLaplaceDensity_integral (α : ℝ) {q : ℝ} (hq : 0 < q) :
    (∫ t in Ioi (0 : ℝ), positiveLaplaceDensity α q t) = 2 * realOrderK α q := by
  have hsub := integral_image_eq_integral_abs_deriv_smul
    (s := (Set.univ : Set ℝ)) measurableSet_univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ huv => Real.exp_injective huv) (positiveLaplaceDensity α q)
  have h : (∫ t in Ioi (0 : ℝ), positiveLaplaceDensity α q t) =
      ∫ u : ℝ, Real.exp u * positiveLaplaceDensity α q (Real.exp u) := by
    simpa only [Set.image_univ, Real.range_exp, integral_univ, smul_eq_mul,
      abs_of_pos (Real.exp_pos _)] using hsub
  rw [h]
  simp_rw [positiveLaplaceDensity_exp_pullback]
  exact tiltedCoshDensity_integral α hq

/-- Scaling t by c gives the exact reciprocal Gaussian Laplace identity.
This parameterization avoids hiding square-root sign choices in A and B. -/
theorem scaled_positive_laplace_integral (α : ℝ) {q c : ℝ}
    (hq : 0 < q) (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ), t ^ (α - 1) *
      Real.exp (-(q / (2 * c)) * t - (q * c / 2) / t)) =
      2 * c ^ α * realOrderK α q := by
  let f : ℝ → ℝ := fun t => t ^ (α - 1) *
    Real.exp (-(q / (2 * c)) * t - (q * c / 2) / t)
  have hpoint {u : ℝ} (hu : 0 < u) :
      f (c * u) = c ^ (α - 1) * positiveLaplaceDensity α q u := by
    dsimp [f, positiveLaplaceDensity]
    rw [Real.mul_rpow hc.le hu.le]
    have he : -(q / (2 * c)) * (c * u) - (q * c / 2) / (c * u) =
        -(q / 2) * (u + u⁻¹) := by
      field_simp [hc.ne', hu.ne']
      <;> ring
    rw [he]
    ring
  have hscale : (∫ u in Ioi (0 : ℝ), f (c * u)) =
      c⁻¹ * ∫ t in Ioi (0 : ℝ), f t := by
    simpa only [mul_zero, smul_eq_mul] using
      integral_comp_mul_left_Ioi f 0 (b := c) hc
  have hp : c * c ^ (α - 1) = c ^ α := by
    calc
      c * c ^ (α - 1) = c ^ (1 : ℝ) * c ^ (α - 1) := by rw [Real.rpow_one]
      _ = c ^ ((1 : ℝ) + (α - 1)) := (Real.rpow_add hc _ _).symm
      _ = c ^ α := by congr 1 <;> ring
  change (∫ t in Ioi (0 : ℝ), f t) = _
  calc
    _ = c * (c⁻¹ * ∫ t in Ioi (0 : ℝ), f t) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    _ = c * ∫ u in Ioi (0 : ℝ), f (c * u) := by rw [hscale]
    _ = c * ∫ u in Ioi (0 : ℝ), c ^ (α - 1) * positiveLaplaceDensity α q u := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact hpoint hu
    _ = _ := by
      rw [integral_const_mul, positiveLaplaceDensity_integral α hq]
      calc
        c * (c ^ (α - 1) * (2 * realOrderK α q)) =
            2 * (c * c ^ (α - 1)) * realOrderK α q := by ring
        _ = _ := by rw [hp]

end

end ImbalancedChen.Part3.RealOrderKPositiveLaplace
