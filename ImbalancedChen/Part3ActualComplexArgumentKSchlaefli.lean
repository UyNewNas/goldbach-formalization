import ImbalancedChen.Part3ActualComplexArgumentKLaplace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The actual complex-z K model has full-line tilted and positive-axis
Schlaefli representations on Re(z)>0, at every complex order. The tilted
density has exactly the real positive-argument damping norm, proving
absolute convergence. Reflection proves its literal K value. The real
change t=exp(u), with its positive Jacobian and principal power on a
positive base, then proves the Schlaefli representation and its L1.

There is no complex change of contour, assumed analytic continuation,
complex product formula, or claim in the large sectors of DLMF 10.32.18.
-/

namespace ImbalancedChen.Part3.ActualComplexArgumentKSchlaefli20261026b

noncomputable section
open Set MeasureTheory Filter
open ActualComplexArgumentKLaplace20261026b
open RealOrderKPositiveLaplace

def tiltedComplexDensity (nu z : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-z * (Real.cosh u : ℂ) + nu * (u : ℂ))

def positiveComplexDensity (nu z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (nu - 1) * Complex.exp (-(z / 2) * ((t : ℂ) + (t : ℂ)⁻¹))

theorem tiltedComplexDensity_norm (nu z : ℂ) (u : ℝ) :
    ‖tiltedComplexDensity nu z u‖ = tiltedCoshDensity nu.re z.re u := by
  simp only [tiltedComplexDensity, tiltedCoshDensity, Complex.norm_exp, Complex.add_re,
    Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]

/-- Actual full-line absolute convergence for every complex order. -/
theorem tiltedComplexDensity_integrable (nu : ℂ) {z : ℂ} (hz : 0 < z.re) :
    Integrable (tiltedComplexDensity nu z) := by
  have hc : Continuous (tiltedComplexDensity nu z) := by unfold tiltedComplexDensity; fun_prop
  apply (tiltedCoshDensity_integrable nu.re hz).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun u => le_of_eq (tiltedComplexDensity_norm nu z u)

theorem tiltedComplexDensity_reflect (nu z : ℂ) (u : ℝ) :
    tiltedComplexDensity nu z (-u) = tiltedComplexDensity (-nu) z u := by
  unfold tiltedComplexDensity
  rw [Real.cosh_neg, Complex.ofReal_neg]
  congr 1
  ring

theorem tiltedComplexDensity_pair (nu z : ℂ) (u : ℝ) :
    tiltedComplexDensity (-nu) z u + tiltedComplexDensity nu z u =
      2 * argumentMomentIntegrand 0 nu z u := by
  unfold tiltedComplexDensity argumentMomentIntegrand
  simp only [pow_zero, one_mul, Complex.exp_add, neg_mul]
  rw [Complex.cosh]
  ring

/-- The full-line tilted actual K representation. -/
theorem tiltedComplexDensity_integral (nu : ℂ) {z : ℂ} (hz : 0 < z.re) :
    (∫ u : ℝ, tiltedComplexDensity nu z u) = 2 * complexArgumentK nu z := by
  have hp := tiltedComplexDensity_integrable nu hz
  have hn := tiltedComplexDensity_integrable (-nu) hz
  calc
    _ = (∫ u in Iic (0 : ℝ), tiltedComplexDensity nu z u) +
        ∫ u in Ioi (0 : ℝ), tiltedComplexDensity nu z u :=
      (intervalIntegral.integral_Iic_add_Ioi hp.integrableOn hp.integrableOn).symm
    _ = (∫ u in Ioi (0 : ℝ), tiltedComplexDensity (-nu) z u) +
        ∫ u in Ioi (0 : ℝ), tiltedComplexDensity nu z u := by
      congr 1
      simpa only [neg_zero, tiltedComplexDensity_reflect] using
        (integral_comp_neg_Ioi (0 : ℝ) (tiltedComplexDensity nu z)).symm
    _ = ∫ u in Ioi (0 : ℝ),
        (tiltedComplexDensity (-nu) z u + tiltedComplexDensity nu z u) :=
      (integral_add hn.integrableOn hp.integrableOn).symm
    _ = _ := by
      simp_rw [tiltedComplexDensity_pair]
      rw [integral_const_mul]
      rfl

/-- The exact positive exponential Jacobian and principal-power identity. -/
theorem positiveComplexDensity_exp_jacobian (nu z : ℂ) (u : ℝ) :
    (Real.exp u : ℂ) * positiveComplexDensity nu z (Real.exp u) =
      tiltedComplexDensity nu z u := by
  have heC : (Real.exp u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)
  have hlog : Complex.log (Real.exp u : ℂ) = (u : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
  have hcosh : (Real.exp u : ℂ) + (Real.exp u : ℂ)⁻¹ = 2 * (Real.cosh u : ℂ) := by
    rw [← Complex.ofReal_inv, ← Real.exp_neg, Real.cosh_eq]
    push_cast
    ring
  unfold positiveComplexDensity tiltedComplexDensity
  rw [Complex.cpow_def_of_ne_zero heC, hlog, hcosh, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- Full absolute convergence of the actual complex-argument positive
Schlaefli integral, transported by a real exponential substitution. -/
theorem positiveComplexDensity_integrable (nu : ℂ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (positiveComplexDensity nu z) (Ioi (0 : ℝ)) := by
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := (univ : Set ℝ)) measurableSet_univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ huv => Real.exp_injective huv) (positiveComplexDensity nu z)
  rw [image_univ, Real.range_exp, integrableOn_univ] at hchange
  apply hchange.mpr
  simpa only [abs_of_pos (Real.exp_pos _), Complex.real_smul,
    positiveComplexDensity_exp_jacobian] using tiltedComplexDensity_integrable nu hz

/-- The actual complex-argument Schlaefli representation on Re(z)>0.
Every integration variable and every complex-power base is real positive. -/
theorem positiveComplexDensity_integral (nu : ℂ) {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ), positiveComplexDensity nu z t) =
      2 * complexArgumentK nu z := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := (univ : Set ℝ)) measurableSet_univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ huv => Real.exp_injective huv) (positiveComplexDensity nu z)
  have hrepresentation : (∫ t in Ioi (0 : ℝ), positiveComplexDensity nu z t) =
      ∫ u : ℝ, tiltedComplexDensity nu z u := by
    simpa only [image_univ, Real.range_exp, integral_univ,
      abs_of_pos (Real.exp_pos _), Complex.real_smul,
      positiveComplexDensity_exp_jacobian] using hchange
  rw [hrepresentation, tiltedComplexDensity_integral nu hz]

end
end ImbalancedChen.Part3.ActualComplexArgumentKSchlaefli20261026b
