import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Genuine complex-rate Gamma-Laplace integral: convergence and native
parameter differentiation in Re(z)>0, for Re(a)>0. The derivative majorant
is a proved real Gamma density with one extra q factor. No Laplace formula,
analyticity supplier, or domination hypothesis is assumed.
-/

namespace ImbalancedChen.Part3.ActualComplexRateGammaLaplaceAnalytic20261026b

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology

def rateHalfPlane : Set ℂ := {z | 0 < z.re}

def gammaLaplaceIntegrand (a z : ℂ) (q : ℝ) : ℂ :=
  (q : ℂ) ^ (a - 1) * Complex.exp (-z * (q : ℂ))

def gammaLaplaceDerivative (a z : ℂ) (q : ℝ) : ℂ :=
  -(q : ℂ) * gammaLaplaceIntegrand a z q

def gammaLaplaceIntegral (a z : ℂ) : ℂ :=
  ∫ q in Ioi (0 : ℝ), gammaLaplaceIntegrand a z q

def gammaDensityMajorant (sigma c q : ℝ) : ℝ :=
  q ^ sigma * Real.exp (-c * q)

theorem gammaDensityMajorant_integrable {sigma c : ℝ}
    (hs : -1 < sigma) (hc : 0 < c) :
    IntegrableOn (gammaDensityMajorant sigma c) (Ioi 0) := by
  simpa only [gammaDensityMajorant, Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) hs (by norm_num) hc)

theorem gammaLaplaceIntegrand_norm (a z : ℂ) {q : ℝ} (hq : 0 < q) :
    ‖gammaLaplaceIntegrand a z q‖ = gammaDensityMajorant (a.re - 1) z.re q := by
  rw [gammaLaplaceIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq,
    Complex.norm_exp]
  simp [gammaDensityMajorant, Complex.mul_re]

theorem gammaLaplaceIntegrand_measurable (a z : ℂ) :
    Measurable (gammaLaplaceIntegrand a z) := by
  unfold gammaLaplaceIntegrand
  fun_prop

theorem gammaLaplaceDerivative_measurable (a z : ℂ) :
    Measurable (gammaLaplaceDerivative a z) := by
  have hi := gammaLaplaceIntegrand_measurable a z
  unfold gammaLaplaceDerivative
  fun_prop

theorem gammaLaplaceIntegrand_integrable {a z : ℂ}
    (ha : 0 < a.re) (hz : 0 < z.re) :
    IntegrableOn (gammaLaplaceIntegrand a z) (Ioi 0) := by
  apply (gammaDensityMajorant_integrable (by linarith : -1 < a.re - 1) hz).mono'
    (gammaLaplaceIntegrand_measurable a z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  exact (gammaLaplaceIntegrand_norm a z hq).le

theorem gammaLaplaceDerivative_norm_le (a : ℂ) {z : ℂ} {c q : ℝ}
    (hc : c ≤ z.re) (hq : 0 < q) :
    ‖gammaLaplaceDerivative a z q‖ ≤ gammaDensityMajorant a.re c q := by
  have he : Real.exp (-z.re * q) ≤ Real.exp (-c * q) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [gammaLaplaceDerivative, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hq, gammaLaplaceIntegrand_norm a z hq]
  unfold gammaDensityMajorant
  have hp : q * q ^ (a.re - 1) = q ^ a.re := by
    rw [← Real.rpow_one q, ← Real.rpow_add hq]
    congr 1
    ring
  calc
    q * (q ^ (a.re - 1) * Real.exp (-z.re * q)) =
        q ^ a.re * Real.exp (-z.re * q) := by rw [← mul_assoc, hp]
    _ ≤ q ^ a.re * Real.exp (-c * q) :=
      mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hq.le _)

theorem gammaLaplaceIntegrand_hasDerivAt (a z : ℂ) (q : ℝ) :
    HasDerivAt (fun w : ℂ => gammaLaplaceIntegrand a w q)
      (gammaLaplaceDerivative a z q) z := by
  have h := (((hasDerivAt_id z).neg.mul_const (q : ℂ)).cexp)
    .const_mul ((q : ℂ) ^ (a - 1))
  convert h using 1 <;> unfold gammaLaplaceIntegrand gammaLaplaceDerivative <;> ring

/-- Actual complex-rate derivative under the integral; all endpoint,
measurability, and local domination obligations are discharged. -/
theorem gammaLaplaceIntegral_hasDerivAt {a z : ℂ}
    (ha : 0 < a.re) (hz : 0 < z.re) :
    HasDerivAt (gammaLaplaceIntegral a)
      (∫ q in Ioi (0 : ℝ), gammaLaplaceDerivative a z q) z := by
  let U : Set ℂ := {w | z.re / 2 < w.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hzU : z ∈ U := by dsimp [U]; linarith
  have hm : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (gammaLaplaceIntegrand a w)
      (volume.restrict (Ioi 0)) :=
    Eventually.of_forall (fun w => (gammaLaplaceIntegrand_measurable a w).aestronglyMeasurable)
  have hb : ∀ᵐ q ∂volume.restrict (Ioi (0 : ℝ)), ∀ w ∈ U,
      ‖gammaLaplaceDerivative a w q‖ ≤ gammaDensityMajorant a.re (z.re / 2) q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    exact fun w hw => gammaLaplaceDerivative_norm_le a hw.le hq
  have hd : ∀ᵐ q ∂volume.restrict (Ioi (0 : ℝ)), ∀ w ∈ U,
      HasDerivAt (fun v => gammaLaplaceIntegrand a v q) (gammaLaplaceDerivative a w q) w :=
    Eventually.of_forall (fun q w _ => gammaLaplaceIntegrand_hasDerivAt a w q)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun w q => gammaLaplaceIntegrand a w q)
    (F' := fun w q => gammaLaplaceDerivative a w q)
    (bound := gammaDensityMajorant a.re (z.re / 2))
    (hU.mem_nhds hzU) hm (gammaLaplaceIntegrand_integrable ha hz)
    (gammaLaplaceDerivative_measurable a z).aestronglyMeasurable hb
    (gammaDensityMajorant_integrable (by linarith : -1 < a.re)
      (by linarith : 0 < z.re / 2)) hd).2

theorem gammaLaplaceIntegral_analyticOnNhd {a : ℂ} (ha : 0 < a.re) :
    AnalyticOnNhd ℂ (gammaLaplaceIntegral a) rateHalfPlane := by
  have hdiff : DifferentiableOn ℂ (gammaLaplaceIntegral a) rateHalfPlane :=
    fun z hz => (gammaLaplaceIntegral_hasDerivAt ha hz).differentiableAt.differentiableWithinAt
  intro z hz
  exact hdiff.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)

end
end ImbalancedChen.Part3.ActualComplexRateGammaLaplaceAnalytic20261026b
