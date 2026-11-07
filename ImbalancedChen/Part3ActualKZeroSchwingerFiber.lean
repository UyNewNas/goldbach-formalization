import ImbalancedChen.Part3ActualKUnequalPositiveShear
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The missing inner primitive for the positive-real Macdonald transform:
the actual K_0(q) Schwinger density exp(-t/2-q^2/(2t))/t. Its positive
scaling t=q*u is proved with its actual Jacobian and reduces to the
already proved literal order-zero Schlaefli density. This gives its
absolute convergence and integral 2*K_0(q), without assuming a product
formula. Positivity also gives the exact integral of its complex norm,
which will justify the subsequent two-variable Fubini interchange.
-/

namespace ImbalancedChen.Part3.ActualKZeroSchwingerFiber20261026b

noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly ComplexOrderKPositiveLaplace20261025a
open ActualKUnequalPositiveShear20261026b

def zeroSchwingerDensity (q t : ℝ) : ℝ :=
  t⁻¹ * Real.exp (-t / 2 - q ^ 2 / (2 * t))

theorem zeroSchwingerDensity_pos (q : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < zeroSchwingerDensity q t :=
  mul_pos (inv_pos.mpr ht) (Real.exp_pos _)

/-- The actual positive scaling t=q*u and its real Jacobian q. -/
theorem zeroSchwingerDensity_scaled {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    (q : ℂ) * (zeroSchwingerDensity q (q * u) : ℂ) = laplaceDensity 0 q u := by
  have he : -(q * u) / 2 - q ^ 2 / (2 * (q * u)) =
      -(q / 2) * (u + u⁻¹) := by
    field_simp [hq.ne', hu.ne'] <;> ring
  unfold zeroSchwingerDensity laplaceDensity
  simp only [zero_sub, Complex.cpow_neg_one]
  rw [he]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hq.ne', Complex.ofReal_ne_zero.mpr hu.ne'] <;> ring

/-- Absolute convergence, transported through the positive dilation.
It holds for every positive q, including the order-zero endpoint. -/
theorem zeroSchwingerDensity_complex_integrable {q : ℝ} (hq : 0 < q) :
    Integrable (fun t => (zeroSchwingerDensity q t : ℂ)) positiveMeasure := by
  have hjac : Integrable (fun u => (q : ℂ) *
      (zeroSchwingerDensity q (q * u) : ℂ)) positiveMeasure := by
    apply (laplaceDensity_integrable 0 hq).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (zeroSchwingerDensity_scaled hq hu).symm
  have hcomp : Integrable (fun u => (zeroSchwingerDensity q (q * u) : ℂ))
      positiveMeasure := by
    apply (hjac.const_mul (q : ℂ)⁻¹).congr
    exact Eventually.of_forall fun u => by
      rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hq.ne'), one_mul]
  have hbase := (integrableOn_Ioi_comp_mul_left_iff
    (fun t => (zeroSchwingerDensity q t : ℂ)) 0 hq).mp hcomp
  simpa only [mul_zero] using hbase

theorem zeroSchwingerDensity_integrable {q : ℝ} (hq : 0 < q) :
    Integrable (zeroSchwingerDensity q) positiveMeasure := by
  simpa only [Complex.ofReal_re] using (zeroSchwingerDensity_complex_integrable hq).re

/-- The actual order-zero Schwinger integral. No K product theorem is used. -/
theorem zeroSchwingerDensity_complex_integral {q : ℝ} (hq : 0 < q) :
    (∫ t in Ioi (0 : ℝ), (zeroSchwingerDensity q t : ℂ)) =
      2 * complexOrderK 0 q := by
  have hscale := integral_comp_mul_left_Ioi'
    (fun t => (zeroSchwingerDensity q t : ℂ)) 0 hq
  rw [mul_zero, Complex.real_smul] at hscale
  rw [← hscale, ← integral_const_mul]
  calc
    _ = ∫ u in Ioi (0 : ℝ), laplaceDensity 0 q u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact zeroSchwingerDensity_scaled hq hu
    _ = _ := laplaceDensity_integral 0 hq

/-- The positive real density removes all cancellation from its integral.
This exact norm identity supplies the later joint-L1 proof. -/
theorem zeroSchwingerDensity_norm_integral {q : ℝ} (hq : 0 < q) :
    (∫ t in Ioi (0 : ℝ), ‖(zeroSchwingerDensity q t : ℂ)‖) =
      2 * ‖complexOrderK 0 q‖ := by
  have hnonneg : 0 ≤ ∫ t in Ioi (0 : ℝ), zeroSchwingerDensity q t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (zeroSchwingerDensity_pos q ht).le
  have heval := congrArg norm (zeroSchwingerDensity_complex_integral hq)
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hnonneg, norm_mul] at heval
  norm_num at heval
  calc
    _ = ∫ t in Ioi (0 : ℝ), zeroSchwingerDensity q t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (zeroSchwingerDensity_pos q ht)]
    _ = _ := heval

end
end ImbalancedChen.Part3.ActualKZeroSchwingerFiber20261026b
