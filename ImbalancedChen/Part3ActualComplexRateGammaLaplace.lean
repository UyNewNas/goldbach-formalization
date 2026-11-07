import ImbalancedChen.Part3ActualComplexRateGammaLaplaceAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual complex-rate Gamma-Laplace evaluation, extending the pinned
positive-real-rate Euler integral by the identity theorem. Actual
parameter holomorphy was derived in the preceding source. The positive
real axis accumulates at the interior point 1 of the right half-plane.
No complex-rate Laplace identity is an assumption.
-/

namespace ImbalancedChen.Part3.ActualComplexRateGammaLaplace20261026b

noncomputable section
open Complex Set MeasureTheory
open ActualComplexRateGammaLaplaceAnalytic20261026b

theorem gammaLaplaceIntegral_real_rate {a : ℂ} (ha : 0 < a.re)
    {r : ℝ} (hr : 0 < r) :
    gammaLaplaceIntegral a (r : ℂ) = (r : ℂ) ^ (-a) * Gamma a := by
  calc
    gammaLaplaceIntegral a (r : ℂ) =
        ∫ q in Ioi (0 : ℝ), (q : ℂ) ^ (a - 1) *
          Complex.exp (-((r : ℂ) * (q : ℂ))) := by
      unfold gammaLaplaceIntegral
      apply setIntegral_congr_fun measurableSet_Ioi
      intro q hq
      unfold gammaLaplaceIntegrand
      rw [neg_mul]
    _ = (1 / (r : ℂ)) ^ a * Gamma a :=
      Complex.integral_cpow_mul_exp_neg_mul_Ioi ha hr
    _ = (r : ℂ) ^ (-a) * Gamma a := by
      rw [one_div, Complex.inv_cpow_ofReal_nonneg hr.le, ← Complex.cpow_neg]

theorem gammaLaplaceFormula_analyticOnNhd (a : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => z ^ (-a) * Gamma a) rateHalfPlane := by
  intro z hz
  exact (analyticAt_id.cpow analyticAt_const (Or.inl hz)).mul analyticAt_const

/-- Genuine actual Euler-Laplace formula for every complex rate with
positive real part, with the principal power and no branch alteration. -/
theorem gammaLaplaceIntegral_eq {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    gammaLaplaceIntegral a z = z ^ (-a) * Gamma a := by
  have hf := gammaLaplaceIntegral_analyticOnNhd ha
  have hg := gammaLaplaceFormula_analyticOnNhd a
  have hU : IsPreconnected rateHalfPlane :=
    (Complex.convex_halfSpace_re_gt (r := 0)).isPreconnected
  have h1 : (1 : ℂ) ∈ rateHalfPlane := by norm_num [rateHalfPlane]
  have hclosure : (1 : ℂ) ∈ closure
      ({w : ℂ | gammaLaplaceIntegral a w = w ^ (-a) * Gamma a} \ {1}) := by
    have hreal : (1 : ℝ) ∈ closure (Ioi (1 : ℝ)) := by simp
    have himage : (1 : ℂ) ∈ closure (Complex.ofReal '' Ioi (1 : ℝ)) :=
      mem_closure_image Complex.continuous_ofReal.continuousAt hreal
    apply (closure_mono ?_) himage
    rintro w ⟨r, hr, rfl⟩
    refine ⟨?_, ?_⟩
    · exact gammaLaplaceIntegral_real_rate ha (by linarith)
    · simp only [mem_singleton_iff]
      intro heq
      have hr1 : r = 1 := by exact_mod_cast heq
      linarith
  exact (hf.eqOn_of_preconnected_of_mem_closure hg hU h1 hclosure) z hz

/-- The actual rate needed by the oscillatory symmetric J Poisson
integrand; its real part is exactly the positive Abel parameter. -/
theorem gammaLaplaceIntegral_Abel_phase {a : ℂ} (ha : 0 < a.re)
    {epsilon : ℝ} (he : 0 < epsilon) (u : ℝ) :
    gammaLaplaceIntegral a ((epsilon : ℂ) - I * (u : ℂ)) =
      ((epsilon : ℂ) - I * (u : ℂ)) ^ (-a) * Gamma a := by
  apply gammaLaplaceIntegral_eq ha
  simpa using he

end
end ImbalancedChen.Part3.ActualComplexRateGammaLaplace20261026b
