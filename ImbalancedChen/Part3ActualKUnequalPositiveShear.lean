import ImbalancedChen.Part3ComplexOrderKPositiveLaplace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Two independently positive arguments in the literal complex-order K
integral. The actual Schlaefli factors are transported by u=t*r on the
positive quadrant. The factor t is the real Jacobian. Joint absolute
convergence is proved directly: the integral of the norm along each
positive r-fiber is exactly the first norm times the second L1 norm.
Consequently both orders of the double integral are justified by Fubini.

This is a positive double-integral change of variables, not Macdonald's
single-integral formula. DLMF 10.32.18, checked on the primary page
https://dlmf.nist.gov/10.32.E18 on 2026-10-26, is
  K_nu(z) K_nu(zeta) = (1/2) integral_0^infty
    exp(-t/2-(z^2+zeta^2)/(2t)) K_nu(z*zeta/t) dt/t,
with printed domain |ph z|<pi, |ph zeta|<pi,
|ph(z+zeta)|<pi/4. That formula remains OPEN here.
The stopped unfrozen unequal-product draft is not imported or assumed.
-/

namespace ImbalancedChen.Part3.ActualKUnequalPositiveShear20261026b

noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly ComplexOrderKPositiveLaplace20261025a

abbrev positiveMeasure : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

/-- Absolute convergence of the literal positive Schlaefli density,
transported from its proved full-line exponential pullback. -/
theorem laplaceDensity_integrable (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    Integrable (laplaceDensity nu q) positiveMeasure := by
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := (univ : Set ℝ)) measurableSet_univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ huv => Real.exp_injective huv) (laplaceDensity nu q)
  rw [image_univ, Real.range_exp, integrableOn_univ] at hchange
  apply hchange.mpr
  simpa only [abs_of_pos (Real.exp_pos _), Complex.real_smul,
    laplaceDensity_exp_pullback] using tiltedDensity_integrable nu hq

/-- The actual unequal-argument density after the positive change u=t*r. -/
def shearDensity (nu mu : ℂ) (x y t r : ℝ) : ℂ :=
  (t : ℂ) * (laplaceDensity nu x t * laplaceDensity mu y (t * r))

theorem shearDensity_measurable (nu mu : ℂ) (x y : ℝ) :
    Measurable (fun p : ℝ × ℝ => shearDensity nu mu x y p.1 p.2) := by
  unfold shearDensity laplaceDensity
  fun_prop

/-- Exact L1 fiber transport. No product-integrability hypothesis is used. -/
theorem shearDensity_norm_fiber (nu mu : ℂ) (x y : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ r in Ioi (0 : ℝ), ‖shearDensity nu mu x y t r‖) =
      ‖laplaceDensity nu x t‖ * ∫ u in Ioi (0 : ℝ), ‖laplaceDensity mu y u‖ := by
  have hscale := integral_comp_mul_left_Ioi'
    (fun u : ℝ => ‖laplaceDensity mu y u‖) 0 ht
  rw [mul_zero, smul_eq_mul] at hscale
  simp only [shearDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht, integral_const_mul]
  calc
    _ = ‖laplaceDensity nu x t‖ *
        (t * ∫ r in Ioi (0 : ℝ), ‖laplaceDensity mu y (t * r)‖) := by ring
    _ = _ := by rw [hscale]

/-- Joint absolute convergence on the actual positive quadrant, before
the two integrations are interchanged. The arguments need not coincide. -/
theorem shearDensity_integrable (nu mu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    Integrable (fun p : ℝ × ℝ => shearDensity nu mu x y p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
  apply (integrable_prod_iff (shearDensity_measurable nu mu x y).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hscaled : IntegrableOn (fun r : ℝ => laplaceDensity mu y (t * r))
        (Ioi (0 : ℝ)) := by
      apply (integrableOn_Ioi_comp_mul_left_iff (laplaceDensity mu y) 0 ht).mpr
      simpa only [mul_zero] using laplaceDensity_integrable mu hy
    exact (hscaled.const_mul (laplaceDensity nu x t)).const_mul (t : ℂ)
  · apply ((laplaceDensity_integrable nu hx).norm.mul_const
      (∫ u in Ioi (0 : ℝ), ‖laplaceDensity mu y u‖)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (shearDensity_norm_fiber nu mu x y ht).symm

/-- The positive r-fiber has its actual Jacobian and literal K value. -/
theorem shearDensity_fiber (nu mu : ℂ) (x : ℝ) {y t : ℝ}
    (hy : 0 < y) (ht : 0 < t) :
    (∫ r in Ioi (0 : ℝ), shearDensity nu mu x y t r) =
      laplaceDensity nu x t * (2 * complexOrderK mu y) := by
  have hscale := integral_comp_mul_left_Ioi' (laplaceDensity mu y) 0 ht
  rw [mul_zero, Complex.real_smul] at hscale
  simp only [shearDensity, integral_const_mul]
  calc
    _ = laplaceDensity nu x t *
        ((t : ℂ) * ∫ r in Ioi (0 : ℝ), laplaceDensity mu y (t * r)) := by ring
    _ = _ := by rw [hscale, laplaceDensity_integral mu hy]

/-- The true unequal-argument positive double-integral transform.
Both arguments and both complex orders are independent. -/
theorem actual_K_unequal_positive_double_integral (nu mu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    complexOrderK nu x * complexOrderK mu y =
      (1 / 4 : ℂ) * ∫ r in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
        shearDensity nu mu x y t r := by
  have hshear := shearDensity_integrable nu mu hx hy
  have heval : (∫ t in Ioi (0 : ℝ), ∫ r in Ioi (0 : ℝ),
      shearDensity nu mu x y t r) =
        4 * (complexOrderK nu x * complexOrderK mu y) := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), laplaceDensity nu x t * (2 * complexOrderK mu y) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact shearDensity_fiber nu mu x hy ht
      _ = _ := by
        rw [integral_mul_const, laplaceDensity_integral nu hx]
        ring
  have hswap : (∫ t in Ioi (0 : ℝ), ∫ r in Ioi (0 : ℝ),
      shearDensity nu mu x y t r) =
        ∫ r in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), shearDensity nu mu x y t r :=
    integral_integral_swap hshear
  rw [← hswap, heval]
  ring

end
end ImbalancedChen.Part3.ActualKUnequalPositiveShear20261026b
