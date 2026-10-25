import ImbalancedChen.Part3ComplexOrderKEntire
import ImbalancedChen.Part3RealOrderKPositiveLaplace
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The complex positive-Laplace representation of the literal K integral.
Every power has a positive real base and the principal complex logarithm.
The scaled identity is the exact input for small-q Gamma normalization.
-/

namespace ImbalancedChen.Part3.ComplexOrderKPositiveLaplace20261025a
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ComplexOrderKBridgeSourceOnly

def tiltedDensity (ν : ℂ) (q u : ℝ) : ℂ :=
  Complex.exp ((-q * Real.cosh u : ℝ) + ν * (u : ℂ))

def laplaceDensity (ν : ℂ) (q t : ℝ) : ℂ :=
  (t : ℂ) ^ (ν - 1) * (Real.exp (-(q / 2) * (t + t⁻¹)) : ℂ)

def dampedGammaDensity (ν : ℂ) (q t : ℝ) : ℂ :=
  (Real.exp (-t) : ℂ) * (t : ℂ) ^ (ν - 1) *
    (Real.exp (-(q ^ 2 / (4 * t))) : ℂ)

theorem tiltedDensity_integrable (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    Integrable (tiltedDensity ν q) := by
  have hc : Continuous (tiltedDensity ν q) := by unfold tiltedDensity; fun_prop
  apply (RealOrderKPositiveLaplace.tiltedCoshDensity_integrable ν.re hq).mono'
    hc.aestronglyMeasurable
  exact Eventually.of_forall (fun u => by
    simp [tiltedDensity, Complex.norm_exp, RealOrderKPositiveLaplace.tiltedCoshDensity])

theorem tiltedDensity_reflect (ν : ℂ) (q u : ℝ) :
    tiltedDensity ν q (-u) = tiltedDensity (-ν) q u := by
  unfold tiltedDensity
  rw [Real.cosh_neg, Complex.ofReal_neg]
  congr 1
  ring

theorem tiltedDensity_pair (ν : ℂ) (q u : ℝ) :
    tiltedDensity (-ν) q u + tiltedDensity ν q u = 2 * complexOrderIntegrand ν q u := by
  unfold tiltedDensity complexOrderIntegrand
  simp only [Complex.exp_add, ← Complex.ofReal_exp]
  rw [Complex.cosh]
  have hneg : -ν * (u : ℂ) = -(ν * (u : ℂ)) := by ring
  rw [hneg]
  ring

theorem tiltedDensity_integral (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    (∫ u : ℝ, tiltedDensity ν q u) = 2 * complexOrderK ν q := by
  have hf := tiltedDensity_integrable ν hq
  have hn := tiltedDensity_integrable (-ν) hq
  calc
    _ = (∫ u in Iic (0 : ℝ), tiltedDensity ν q u) +
        ∫ u in Ioi (0 : ℝ), tiltedDensity ν q u :=
      (intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn).symm
    _ = (∫ u in Ioi (0 : ℝ), tiltedDensity (-ν) q u) +
        ∫ u in Ioi (0 : ℝ), tiltedDensity ν q u := by
      congr 1
      simpa only [neg_zero, tiltedDensity_reflect] using
        (integral_comp_neg_Ioi (0 : ℝ) (tiltedDensity ν q)).symm
    _ = ∫ u in Ioi (0 : ℝ), (tiltedDensity (-ν) q u + tiltedDensity ν q u) :=
      (integral_add hn.integrableOn hf.integrableOn).symm
    _ = _ := by
      simp_rw [tiltedDensity_pair]
      rw [integral_const_mul]
      rfl

theorem laplaceDensity_exp_pullback (ν : ℂ) (q u : ℝ) :
    (Real.exp u : ℂ) * laplaceDensity ν q (Real.exp u) = tiltedDensity ν q u := by
  have he : (Real.exp u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hlog : Complex.log (Real.exp u : ℂ) = (u : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
  unfold laplaceDensity tiltedDensity
  rw [Complex.cpow_def_of_ne_zero he, hlog, ← Real.exp_neg]
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Real.cosh_eq]
  push_cast
  ring

theorem laplaceDensity_integral (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    (∫ t in Ioi (0 : ℝ), laplaceDensity ν q t) = 2 * complexOrderK ν q := by
  have hsub := integral_image_eq_integral_abs_deriv_smul
    (s := (Set.univ : Set ℝ)) measurableSet_univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ huv => Real.exp_injective huv) (laplaceDensity ν q)
  have h : (∫ t in Ioi (0 : ℝ), laplaceDensity ν q t) =
      ∫ u : ℝ, (Real.exp u : ℂ) * laplaceDensity ν q (Real.exp u) := by
    simpa only [Set.image_univ, Real.range_exp, integral_univ, Complex.real_smul,
      abs_of_pos (Real.exp_pos _)] using hsub
  rw [h]
  simp_rw [laplaceDensity_exp_pullback]
  exact tiltedDensity_integral ν hq

theorem dampedGammaDensity_scaled (ν : ℂ) {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    dampedGammaDensity ν q ((q / 2) * u) =
      ((q / 2 : ℝ) : ℂ) ^ (ν - 1) * laplaceDensity ν q u := by
  have hc : 0 < q / 2 := half_pos hq
  unfold dampedGammaDensity laplaceDensity
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le hu.le]
  have hexp : -((q / 2) * u) - q ^ 2 / (4 * ((q / 2) * u)) =
      -(q / 2) * (u + u⁻¹) := by
    field_simp [hq.ne', hu.ne'] <;> ring
  have he : (Real.exp (-((q / 2) * u)) : ℂ) *
      (Real.exp (-(q ^ 2 / (4 * ((q / 2) * u)))) : ℂ) =
        (Real.exp (-(q / 2) * (u + u⁻¹)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    exact hexp
  calc
    _ = ((q / 2 : ℝ) : ℂ) ^ (ν - 1) * (u : ℂ) ^ (ν - 1) *
        ((Real.exp (-((q / 2) * u)) : ℂ) *
          (Real.exp (-(q ^ 2 / (4 * ((q / 2) * u)))) : ℂ)) := by ring
    _ = _ := by rw [he]; ring

/-- Exact scaled Gamma integral for the actual K, before taking any limit. -/
theorem dampedGammaDensity_integral (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    (∫ t in Ioi (0 : ℝ), dampedGammaDensity ν q t) =
      2 * ((q / 2 : ℝ) : ℂ) ^ ν * complexOrderK ν q := by
  have hc : 0 < q / 2 := half_pos hq
  have hcC : ((q / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hp : ((q / 2 : ℝ) : ℂ) * ((q / 2 : ℝ) : ℂ) ^ (ν - 1) =
      ((q / 2 : ℝ) : ℂ) ^ ν := by
    calc
      _ = ((q / 2 : ℝ) : ℂ) ^ (1 : ℂ) * ((q / 2 : ℝ) : ℂ) ^ (ν - 1) := by
        rw [Complex.cpow_one]
      _ = ((q / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (ν - 1)) :=
        (Complex.cpow_add _ _ hcC).symm
      _ = _ := by congr 1; ring
  have hscale := integral_comp_mul_left_Ioi' (dampedGammaDensity ν q) 0 hc
  rw [mul_zero, Complex.real_smul] at hscale
  rw [← hscale]
  have hpoint : (∫ u in Ioi (0 : ℝ), dampedGammaDensity ν q ((q / 2) * u)) =
      ∫ u in Ioi (0 : ℝ), ((q / 2 : ℝ) : ℂ) ^ (ν - 1) * laplaceDensity ν q u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact dampedGammaDensity_scaled ν hq hu
  rw [hpoint, integral_const_mul, laplaceDensity_integral ν hq]
  calc
    _ = 2 * (((q / 2 : ℝ) : ℂ) * ((q / 2 : ℝ) : ℂ) ^ (ν - 1)) *
        complexOrderK ν q := by ring
    _ = _ := by rw [hp]

end
end ImbalancedChen.Part3.ComplexOrderKPositiveLaplace20261025a
