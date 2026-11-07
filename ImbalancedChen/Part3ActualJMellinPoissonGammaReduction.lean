import ImbalancedChen.Part3ActualJFixedOrderAbelLimit
import ImbalancedChen.Part3ActualJCriticalLogBound
import ImbalancedChen.Part3ActualComplexRateGammaLaplace
import Mathlib.MeasureTheory.Integral.Prod

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual damped J_(2it) Mellin integral reduced to its literal angular
Poisson/Gamma integral. Product absolute integrability is proved from an
actual real Gamma density times the actual integrable order-zero Poisson
weight. Fubini is applied only after that proof. The radial integral is
then evaluated by the proved actual complex-rate Gamma-Laplace theorem.
No full Mellin/Gamma-ratio evaluation or angular Abel limit is assumed.
The held critical-quotient Mellin modules are not imported.
-/

namespace ImbalancedChen.Part3.ActualJMellinPoissonGammaReduction20261026b

noncomputable section
open Complex Set MeasureTheory
open ActualGeneralJBesselSourceOnly GeneralJSymmetricPoissonIntegralSourceOnly
open JBesselPoissonEvenMoments20261025a ActualJLocalOrderHolomorphic20261026a
open ActualJCriticalLogBound20261026a ActualJFixedOrderMellinL120261026b
open ActualJFixedOrderAbelLimit20261026b
open ActualComplexRateGammaLaplaceAnalytic20261026b ActualComplexRateGammaLaplace20261026b

def nativeOrderWeight (t u : ℝ) : ℂ := orderPoissonIntegrand (2 * I * (t : ℂ)) 0 u

def poissonMellinConstant (t : ℝ) : ℂ :=
  (2 : ℂ) ^ (-(2 * I * (t : ℂ))) * orderGammaFactor (2 * I * (t : ℂ))

def poissonMellinFiber (s : ℂ) (t epsilon q u : ℝ) : ℂ :=
  (q : ℂ) ^ (s + 2 * I * (t : ℂ) - 1) *
    Complex.exp (-((epsilon : ℂ) - I * (u : ℂ)) * (q : ℂ)) * nativeOrderWeight t u

private theorem nativeOrderWeight_norm (t : ℝ) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ‖nativeOrderWeight t u‖ = ‖poissonWeight 0 u‖ := by
  exact orderPoissonIntegrand_norm_imaginary (by simp) 0 hu

private theorem fiber_norm (s : ℂ) (t epsilon : ℝ) {q u : ℝ}
    (hq : 0 < q) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ‖poissonMellinFiber s t epsilon q u‖ =
      gammaDensityMajorant (s.re - 1) epsilon q * ‖poissonWeight 0 u‖ := by
  rw [poissonMellinFiber, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.norm_exp, nativeOrderWeight_norm t hu]
  simp [gammaDensityMajorant, Complex.mul_re, Complex.mul_im]

/-- Actual absolute product convergence before Poisson/Mellin Fubini. -/
theorem poissonMellinFiber_integrable {s : ℂ} (hs : 0 < s.re) (t : ℝ)
    {epsilon : ℝ} (he : 0 < epsilon) :
    Integrable (fun p : ℝ × ℝ => poissonMellinFiber s t epsilon p.1 p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-1 : ℝ) 1))) := by
  have hq := gammaDensityMajorant_integrable (by linarith : -1 < s.re - 1) he
  have hw := (poissonWeight_integrable (nu := (0 : ℂ)) (by norm_num)).norm
  have henv := hq.mul_prod hw
  have hm : Measurable (fun p : ℝ × ℝ => poissonMellinFiber s t epsilon p.1 p.2) := by
    unfold poissonMellinFiber nativeOrderWeight orderPoissonIntegrand
    fun_prop
  apply henv.mono' hm.aestronglyMeasurable
  have hmem : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioo (-1 : ℝ) 1)),
      p.1 ∈ Ioi 0 ∧ p.2 ∈ Ioo (-1 : ℝ) 1 := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)
  filter_upwards [hmem] with p hp
  exact (fiber_norm s t epsilon hp.1 hp.2).le

private theorem fiber_eq_poisson (s : ℂ) (t epsilon q u : ℝ) :
    poissonMellinFiber s t epsilon q u =
      ((q : ℂ) ^ (s + 2 * I * (t : ℂ) - 1) *
        (Real.exp (-epsilon * q) : ℂ)) * orderPoissonIntegrand (2 * I * (t : ℂ)) q u := by
  have he : -((epsilon : ℂ) - I * (u : ℂ)) * (q : ℂ) =
      ((-epsilon * q : ℝ) : ℂ) + I * (q : ℂ) * (u : ℂ) := by push_cast; ring
  rw [poissonMellinFiber, he, Complex.exp_add, ← Complex.ofReal_exp]
  simp only [nativeOrderWeight, orderPoissonIntegrand, Complex.ofReal_zero,
    mul_zero, zero_mul, Complex.exp_zero, one_mul]
  ring

private theorem actualAbel_eq_fiber_integral (s : ℂ) (t epsilon : ℝ)
    {q : ℝ} (hq : 0 < q) :
    actualJAbelIntegrand s t epsilon q = poissonMellinConstant t *
      ∫ u in Ioo (-1 : ℝ) 1, poissonMellinFiber s t epsilon q u := by
  have hn : -(1 / 2 : ℝ) < (2 * I * (t : ℂ)).re := by simp
  have hpower : (((q / 2 : ℝ) : ℂ) ^ (2 * I * (t : ℂ))) =
      (q : ℂ) ^ (2 * I * (t : ℂ)) * (2 : ℂ) ^ (-(2 * I * (t : ℂ))) := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.div_cpow_ofReal_nonneg hq.le (by norm_num : (0 : ℝ) ≤ 2),
      Complex.cpow_neg]
    rfl
  have hcombine : (q : ℂ) ^ (s - 1) * (q : ℂ) ^ (2 * I * (t : ℂ)) =
      (q : ℂ) ^ (s + 2 * I * (t : ℂ) - 1) := by
    rw [← Complex.cpow_add (s - 1) (2 * I * (t : ℂ))
      (Complex.ofReal_ne_zero.mpr hq.ne')]
    congr 1
    ring
  have hangular : (∫ u in Ioo (-1 : ℝ) 1, poissonMellinFiber s t epsilon q u) =
      ((q : ℂ) ^ (s + 2 * I * (t : ℂ) - 1) * (Real.exp (-epsilon * q) : ℂ)) *
        orderPoissonIntegral (2 * I * (t : ℂ)) q := by
    simp_rw [fiber_eq_poisson]
    rw [integral_const_mul]
    rfl
  rw [hangular, actualJAbelIntegrand, actualJMellinIntegrand,
    generalJ_eq_symmetric_poisson_integral hn hq, ← orderPoissonIntegral_eq,
    hpower]
  unfold poissonMellinConstant orderGammaFactor
  rw [div_eq_mul_inv]
  calc
    _ = (Real.exp (-epsilon * q) : ℂ) *
        ((q : ℂ) ^ (s - 1) * (q : ℂ) ^ (2 * I * (t : ℂ))) *
          (2 : ℂ) ^ (-(2 * I * (t : ℂ))) *
          ((Real.sqrt Real.pi : ℂ) * Gamma (2 * I * (t : ℂ) + 1 / 2))⁻¹ *
          orderPoissonIntegral (2 * I * (t : ℂ)) q := by ring
    _ = _ := by rw [hcombine]; ring

private theorem fiber_q_integral {s : ℂ} (hs : 0 < s.re) (t : ℝ)
    {epsilon : ℝ} (he : 0 < epsilon) (u : ℝ) :
    (∫ q in Ioi (0 : ℝ), poissonMellinFiber s t epsilon q u) =
      nativeOrderWeight t u *
        (((epsilon : ℂ) - I * (u : ℂ)) ^ (-(s + 2 * I * (t : ℂ))) *
          Gamma (s + 2 * I * (t : ℂ))) := by
  have ha : 0 < (s + 2 * I * (t : ℂ)).re := by simpa using hs
  change (∫ q in Ioi (0 : ℝ),
    gammaLaplaceIntegrand (s + 2 * I * (t : ℂ))
      ((epsilon : ℂ) - I * (u : ℂ)) q * nativeOrderWeight t u) = _
  rw [integral_mul_const]
  change gammaLaplaceIntegral (s + 2 * I * (t : ℂ))
    ((epsilon : ℂ) - I * (u : ℂ)) * nativeOrderWeight t u = _
  rw [gammaLaplaceIntegral_Abel_phase ha he]
  ring

/-- Exact actual damped J Mellin/Poisson/Gamma reduction. The remaining
angular integral and its Abel limit are deliberately explicit. -/
theorem actualJAbelIntegral_eq_poissonGamma {s : ℂ} (hs : 0 < s.re) (t : ℝ)
    {epsilon : ℝ} (he : 0 < epsilon) :
    actualJAbelIntegral s t epsilon = poissonMellinConstant t *
      ∫ u in Ioo (-1 : ℝ) 1, nativeOrderWeight t u *
        (((epsilon : ℂ) - I * (u : ℂ)) ^ (-(s + 2 * I * (t : ℂ))) *
          Gamma (s + 2 * I * (t : ℂ))) := by
  calc
    actualJAbelIntegral s t epsilon =
        ∫ q in Ioi (0 : ℝ), poissonMellinConstant t *
          ∫ u in Ioo (-1 : ℝ) 1, poissonMellinFiber s t epsilon q u := by
      unfold actualJAbelIntegral
      apply setIntegral_congr_fun measurableSet_Ioi
      intro q hq
      exact actualAbel_eq_fiber_integral s t epsilon hq
    _ = poissonMellinConstant t *
        ∫ q in Ioi (0 : ℝ), ∫ u in Ioo (-1 : ℝ) 1,
          poissonMellinFiber s t epsilon q u := integral_const_mul _ _
    _ = poissonMellinConstant t *
        ∫ u in Ioo (-1 : ℝ) 1, ∫ q in Ioi (0 : ℝ),
          poissonMellinFiber s t epsilon q u := by
      rw [integral_integral_swap (poissonMellinFiber_integrable hs t he)]
    _ = _ := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      exact fiber_q_integral hs t he u

end
end ImbalancedChen.Part3.ActualJMellinPoissonGammaReduction20261026b
