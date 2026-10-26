import ImbalancedChen.Part3ActualRealOrderJMellinL1
import ImbalancedChen.Part3ActualComplexRateGammaLaplace
import ImbalancedChen.Part3GeneralJSymmetricPoissonIntegral
import ImbalancedChen.Part3JBesselPoissonEvenMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual real-order J Abel removal and Poisson/Gamma reduction. Real orders
nu>-1/2 use their own actual Poisson weight, not an imaginary-order weight
identity. Product convergence uses Re(s)+nu>0; the real-order energy L1
strip supplies the honest undamped Abel limit. No Mellin formula is assumed.
-/

namespace ImbalancedChen.Part3.ActualRealOrderJAbelPoisson20261026b

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
open ActualGeneralJBesselSourceOnly GeneralJSymmetricPoissonIntegralSourceOnly
open JBesselPoissonEvenMoments20261025a ActualRealOrderJMellinL120261026b
open ActualComplexRateGammaLaplaceAnalytic20261026b ActualComplexRateGammaLaplace20261026b

def realJAbelIntegrand (s : ℂ) (nu epsilon q : ℝ) : ℂ :=
  (Real.exp (-epsilon * q) : ℂ) * realOrderJMellinIntegrand s nu q
def realJAbelIntegral (s : ℂ) (nu epsilon : ℝ) : ℂ :=
  ∫ q in Ioi (0 : ℝ), realJAbelIntegrand s nu epsilon q
def realPoissonMellinConstant (nu : ℝ) : ℂ :=
  (2 : ℂ) ^ (-(nu : ℂ)) / ((Real.sqrt Real.pi : ℂ) * Gamma ((nu : ℂ) + 1 / 2))
def realPoissonMellinFiber (s : ℂ) (nu epsilon q u : ℝ) : ℂ :=
  (q : ℂ) ^ (s + (nu : ℂ) - 1) *
    Complex.exp (-((epsilon : ℂ) - I * (u : ℂ)) * (q : ℂ)) * poissonWeight (nu : ℂ) u
def realAngularAbelIntegral (s : ℂ) (nu epsilon : ℝ) : ℂ :=
  ∫ u in Ioo (-1 : ℝ) 1, poissonWeight (nu : ℂ) u *
    (((epsilon : ℂ) - I * (u : ℂ)) ^ (-(s + (nu : ℂ))) * Gamma (s + (nu : ℂ)))

theorem realJAbelIntegral_tendsto_zero {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    {s : ℂ} (hsnu : 0 < s.re + nu) (hsHalf : s.re < 1 / 2) :
    Tendsto (realJAbelIntegral s nu) (𝓝[≥] (0 : ℝ)) (𝓝 (realOrderJMellinIntegral s nu)) := by
  have hI := integrableOn_realOrderJMellin hnu hsnu hsHalf
  unfold realJAbelIntegral realOrderJMellinIntegral
  apply tendsto_integral_filter_of_dominated_convergence (fun q => ‖realOrderJMellinIntegrand s nu q‖)
  · exact Eventually.of_forall (fun epsilon =>
      (by fun_prop : Measurable (fun q : ℝ => (Real.exp (-epsilon * q) : ℂ))).aestronglyMeasurable.mul
        hI.aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with epsilon he
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    rw [realJAbelIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr he) hq.le))
  · exact hI.norm
  · filter_upwards with q
    have hc : Continuous (fun epsilon : ℝ => (Real.exp (-epsilon * q) : ℂ) *
        realOrderJMellinIntegrand s nu q) := by fun_prop
    have h := hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : (𝓝[≥] (0 : ℝ)) ≤ 𝓝 0)
    simpa only [realJAbelIntegrand, neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using h

theorem realPoissonMellinFiber_integrable {nu : ℝ} (hnu : -(1 / 2 : ℝ) < nu)
    {s : ℂ} (hsnu : 0 < s.re + nu) {epsilon : ℝ} (he : 0 < epsilon) :
    Integrable (fun p : ℝ × ℝ => realPoissonMellinFiber s nu epsilon p.1 p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-1 : ℝ) 1))) := by
  have hq := gammaDensityMajorant_integrable (by linarith : -1 < s.re + nu - 1) he
  have hw := (poissonWeight_integrable (nu := (nu : ℂ)) (by simpa using hnu)).norm
  have hm : Measurable (fun p : ℝ × ℝ => realPoissonMellinFiber s nu epsilon p.1 p.2) := by
    unfold realPoissonMellinFiber poissonWeight
    fun_prop
  apply (hq.mul_prod hw).mono' hm.aestronglyMeasurable
  have hmem : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-1 : ℝ) 1)),
      p.1 ∈ Ioi 0 ∧ p.2 ∈ Ioo (-1 : ℝ) 1 := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)
  filter_upwards [hmem] with p hp
  rw [realPoissonMellinFiber, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hp.1, Complex.norm_exp]
  simp [gammaDensityMajorant, Complex.mul_re, Complex.mul_im]

private theorem realAbel_eq_fiber_integral (s : ℂ) {nu : ℝ} (hnu : -(1 / 2 : ℝ) < nu)
    (epsilon : ℝ) {q : ℝ} (hq : 0 < q) :
    realJAbelIntegrand s nu epsilon q = realPoissonMellinConstant nu *
      ∫ u in Ioo (-1 : ℝ) 1, realPoissonMellinFiber s nu epsilon q u := by
  have hrepr := generalJ_eq_symmetric_poisson_integral (nu := (nu : ℂ)) (by simpa using hnu) hq
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo] at hrepr
  have hJ : generalJ (nu : ℂ) q = (((q / 2 : ℝ) : ℂ) ^ (nu : ℂ)) /
      ((Real.sqrt Real.pi : ℂ) * Gamma ((nu : ℂ) + 1 / 2)) *
        ∫ u in Ioo (-1 : ℝ) 1, Complex.exp (I * (q : ℂ) * (u : ℂ)) * poissonWeight (nu : ℂ) u := by
    simpa only [poissonWeight, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using hrepr
  have hp : (((q / 2 : ℝ) : ℂ) ^ (nu : ℂ)) = (q : ℂ) ^ (nu : ℂ) * (2 : ℂ) ^ (-(nu : ℂ)) := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.div_cpow_ofReal_nonneg hq.le (by norm_num : (0 : ℝ) ≤ 2), Complex.cpow_neg]
    rfl
  have hcombine : (q : ℂ) ^ (s - 1) * (q : ℂ) ^ (nu : ℂ) = (q : ℂ) ^ (s + (nu : ℂ) - 1) := by
    rw [← Complex.cpow_add (s - 1) (nu : ℂ) (Complex.ofReal_ne_zero.mpr hq.ne')]
    congr 1
    ring
  have hF : (∫ u in Ioo (-1 : ℝ) 1, realPoissonMellinFiber s nu epsilon q u) =
      ((q : ℂ) ^ (s + (nu : ℂ) - 1) * (Real.exp (-epsilon * q) : ℂ)) *
        ∫ u in Ioo (-1 : ℝ) 1, Complex.exp (I * (q : ℂ) * (u : ℂ)) * poissonWeight (nu : ℂ) u := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    have he : -((epsilon : ℂ) - I * (u : ℂ)) * (q : ℂ) =
      ((-epsilon * q : ℝ) : ℂ) + I * (q : ℂ) * (u : ℂ) := by push_cast; ring
    rw [realPoissonMellinFiber, he, Complex.exp_add, ← Complex.ofReal_exp]
    ring
  rw [hF, realJAbelIntegrand, realOrderJMellinIntegrand, hJ, hp]
  unfold realPoissonMellinConstant
  simp only [div_eq_mul_inv]
  calc
    _ = (Real.exp (-epsilon * q) : ℂ) * ((q : ℂ) ^ (s - 1) * (q : ℂ) ^ (nu : ℂ)) *
      (2 : ℂ) ^ (-(nu : ℂ)) * (((Real.sqrt Real.pi : ℂ) * Gamma ((nu : ℂ) + 1 / 2))⁻¹) *
        (∫ u in Ioo (-1 : ℝ) 1, Complex.exp (I * (q : ℂ) * (u : ℂ)) * poissonWeight (nu : ℂ) u) := by ring
    _ = _ := by rw [hcombine]; ring

theorem realJAbelIntegral_eq_poissonGamma {nu : ℝ} (hnu : -(1 / 2 : ℝ) < nu)
    {s : ℂ} (hsnu : 0 < s.re + nu) {epsilon : ℝ} (he : 0 < epsilon) :
    realJAbelIntegral s nu epsilon = realPoissonMellinConstant nu * realAngularAbelIntegral s nu epsilon := by
  have ha : 0 < (s + (nu : ℂ)).re := by simpa using hsnu
  calc
    realJAbelIntegral s nu epsilon = ∫ q in Ioi (0 : ℝ), realPoissonMellinConstant nu *
        ∫ u in Ioo (-1 : ℝ) 1, realPoissonMellinFiber s nu epsilon q u := by
      unfold realJAbelIntegral
      apply setIntegral_congr_fun measurableSet_Ioi
      intro q hq
      exact realAbel_eq_fiber_integral s hnu epsilon hq
    _ = realPoissonMellinConstant nu * ∫ u in Ioo (-1 : ℝ) 1,
        ∫ q in Ioi (0 : ℝ), realPoissonMellinFiber s nu epsilon q u := by
      rw [integral_const_mul, integral_integral_swap (realPoissonMellinFiber_integrable hnu hsnu he)]
    _ = _ := by
      unfold realAngularAbelIntegral
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      change (∫ q in Ioi (0 : ℝ), gammaLaplaceIntegrand (s + (nu : ℂ))
        ((epsilon : ℂ) - I * (u : ℂ)) q * poissonWeight (nu : ℂ) u) = _
      rw [integral_mul_const]
      change gammaLaplaceIntegral (s + (nu : ℂ)) ((epsilon : ℂ) - I * (u : ℂ)) * poissonWeight (nu : ℂ) u = _
      rw [gammaLaplaceIntegral_Abel_phase ha he]
      ring

end
end ImbalancedChen.Part3.ActualRealOrderJAbelPoisson20261026b
