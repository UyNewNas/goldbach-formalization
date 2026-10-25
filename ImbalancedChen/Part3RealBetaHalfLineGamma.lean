import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Real Euler Beta integrals on the compact interval and positive halfline.
The compact integral is transferred from the pinned complex Beta theorem.
The map t / (1 + t) is proved to carry (0,infinity) bijectively onto (0,1),
with its actual derivative. The Jacobian theorem supplies integrability as
well as the integral identity. No Beta evaluation or convergence is a premise.

This analytic supplier does not construct a spectral decomposition or supply
the original dispersion estimate. Those original obligations remain open.
-/

namespace ImbalancedChen.Part3RealBetaHalfLineGamma

noncomputable section
open Set MeasureTheory

def compactKernel (a b x : ℝ) : ℝ := x ^ (a - 1) * (1 - x) ^ (b - 1)

theorem complex_kernel_eq_ofReal (a b : ℝ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1) =
      (compactKernel a b x : ℂ) := by
  unfold compactKernel
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx0,
    Complex.ofReal_cpow (sub_nonneg.mpr hx1)]
  simp only [Complex.ofReal_sub, Complex.ofReal_one]

/-- The compact real kernel is integrable, including both singular endpoints. -/
theorem integrableOn_compactKernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (compactKernel a b) (Ioo 0 1) := by
  have hC := Complex.betaIntegral_convergent
    (u := (a : ℂ)) (v := (b : ℂ)) ha hb
  have hCI : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ ((a : ℂ) - 1) *
        (1 - (x : ℂ)) ^ ((b : ℂ) - 1)) (Ioo 0 1) :=
    hC.1.mono_set Ioo_subset_Ioc_self
  have hR : IntegrableOn
      (fun x : ℝ => ((x : ℂ) ^ ((a : ℂ) - 1) *
        (1 - (x : ℂ)) ^ ((b : ℂ) - 1)).re) (Ioo 0 1) := hCI.re
  refine hR.congr_fun (fun x hx => ?_) measurableSet_Ioo
  rw [complex_kernel_eq_ofReal a b hx.1.le hx.2.le]
  rfl

theorem complex_beta_eq_real_compact (a b : ℝ) :
    Complex.betaIntegral (a : ℂ) (b : ℂ) =
      ((∫ x in Ioo (0 : ℝ) 1, compactKernel a b x) : ℂ) := by
  unfold Complex.betaIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  calc
    (∫ x in Ioo (0 : ℝ) 1,
        (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)) =
        ∫ x in Ioo (0 : ℝ) 1, (compactKernel a b x : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      exact complex_kernel_eq_ofReal a b hx.1.le hx.2.le
    _ = _ := integral_ofReal

theorem integral_compactKernel_eq_gamma {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioo (0 : ℝ) 1, compactKernel a b x) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have hC := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (a : ℂ)) (t := (b : ℂ)) ha hb
  rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, complex_beta_eq_real_compact] at hC
  have hR : Real.Gamma a * Real.Gamma b = Real.Gamma (a + b) *
      (∫ x in Ioo (0 : ℝ) 1, compactKernel a b x) := by
    exact_mod_cast hC
  apply (eq_div_iff (Real.Gamma_pos_of_pos (add_pos ha hb)).ne').2
  simpa only [mul_comm] using hR.symm

def halflineToUnit (t : ℝ) : ℝ := t / (1 + t)

theorem halflineToUnit_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt halflineToUnit (1 / (1 + t) ^ 2) t := by
  have hn : 1 + t ≠ 0 := by linarith
  have h := (hasDerivAt_id t).div
    ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)) hn
  convert h using 1 <;> simp only [halflineToUnit, id_eq] <;> ring

theorem halflineToUnit_injOn : InjOn halflineToUnit (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hxden : 1 + x ≠ 0 := by linarith [hx]
  have hyden : 1 + y ≠ 0 := by linarith [hy]
  have h := (div_eq_div_iff hxden hyden).mp hxy
  nlinarith only [h]

theorem halflineToUnit_image : halflineToUnit '' Ioi (0 : ℝ) = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hden : 0 < 1 + t := by linarith [ht]
    exact ⟨div_pos ht hden, (div_lt_one hden).2 (by linarith)⟩
  · intro hx
    have hden : 0 < 1 - x := sub_pos.mpr hx.2
    have ht : 0 < x / (1 - x) := div_pos hx.1 hden
    refine ⟨x / (1 - x), ht, ?_⟩
    unfold halflineToUnit
    have hbig : 1 + x / (1 - x) ≠ 0 := by linarith
    field_simp [hden.ne', hbig]
    <;> ring

/-- The complete transformed integrand, including the absolute Jacobian. -/
theorem halfline_jacobian_kernel (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    |1 / (1 + t) ^ 2| • compactKernel a b (halflineToUnit t) =
      t ^ (a - 1) / (1 + t) ^ (a + b) := by
  have hd : 0 < 1 + t := by linarith
  have hsub : 1 - t / (1 + t) = 1 / (1 + t) := by
    field_simp [hd.ne']
    <;> ring
  have hpow : (1 + t) ^ (a + b) =
      (1 + t) ^ 2 * (1 + t) ^ (a - 1) * (1 + t) ^ (b - 1) := by
    calc
      (1 + t) ^ (a + b) = (1 + t) ^ ((2 : ℝ) + (a - 1) + (b - 1)) := by
        congr 1
        ring
      _ = _ := by rw [Real.rpow_add hd, Real.rpow_add hd, Real.rpow_two]
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (1 + t) ^ 2)]
  simp only [smul_eq_mul, compactKernel, halflineToUnit]
  rw [hsub, Real.div_rpow ht.le hd.le,
    Real.div_rpow zero_le_one hd.le, Real.one_rpow, hpow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Euler's positive-halfline kernel is integrable for positive parameters. -/
theorem integrableOn_beta_halfline {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) / (1 + t) ^ (a + b)) (Ioi 0) := by
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun t ht => (halflineToUnit_hasDerivAt ht).hasDerivWithinAt)
    halflineToUnit_injOn (compactKernel a b)
  rw [halflineToUnit_image] at hchange
  have h := hchange.mp (integrableOn_compactKernel ha hb)
  exact h.congr_fun (fun t ht => halfline_jacobian_kernel a b ht) measurableSet_Ioi

/-- The actual positive-halfline Beta integral, evaluated without a
convergence or evaluation premise. -/
theorem integral_beta_halfline_eq_gamma {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), t ^ (a - 1) / (1 + t) ^ (a + b)) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun t ht => (halflineToUnit_hasDerivAt ht).hasDerivWithinAt)
    halflineToUnit_injOn (compactKernel a b)
  rw [halflineToUnit_image] at hchange
  calc
    (∫ t in Ioi (0 : ℝ), t ^ (a - 1) / (1 + t) ^ (a + b)) =
        ∫ t in Ioi (0 : ℝ), |1 / (1 + t) ^ 2| •
          compactKernel a b (halflineToUnit t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact (halfline_jacobian_kernel a b ht).symm
    _ = ∫ x in Ioo (0 : ℝ) 1, compactKernel a b x := hchange.symm
    _ = _ := integral_compactKernel_eq_gamma ha hb

end
end ImbalancedChen.Part3RealBetaHalfLineGamma
