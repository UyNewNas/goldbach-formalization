import ImbalancedChen.Part3ActualJMellinPoissonGammaReduction
import ImbalancedChen.Part3ActualJAngularAbelRateBound
import ImbalancedChen.Part3PoissonComplexPowerMoment
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual angular Abel removal for the J Poisson/Gamma integral. The singular
majorant |u|^(-Re s) is genuinely integrated with the Poisson endpoint
weight; the single angular origin is excluded only from pointwise bounds.
Combining the actual radial and angular Abel limits identifies the actual
J Mellin integral with the literal imaginary-axis angular integral.
No imaginary-axis phase, Beta evaluation, or final Gamma ratio is assumed.
-/

namespace ImbalancedChen.Part3.ActualJMellinAngularAbelLimit20261026b

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
open ActualJLocalOrderHolomorphic20261026a ActualJCriticalLogBound20261026a
open ActualJMellinPoissonGammaReduction20261026b
open ActualJFixedOrderMellinL120261026b ActualJFixedOrderAbelLimit20261026b
open ActualJAngularAbelRateBound20261026b PoissonComplexPowerMoment20261026b

def angularAbelIntegrand (s : ℂ) (t epsilon u : ℝ) : ℂ :=
  nativeOrderWeight t u *
    (((epsilon : ℂ) - I * (u : ℂ)) ^ (-(s + 2 * I * (t : ℂ))) *
      Gamma (s + 2 * I * (t : ℂ)))

def angularBoundaryIntegrand (s : ℂ) (t u : ℝ) : ℂ :=
  nativeOrderWeight t u *
    ((-(I * (u : ℂ))) ^ (-(s + 2 * I * (t : ℂ))) * Gamma (s + 2 * I * (t : ℂ)))

def angularAbelIntegral (s : ℂ) (t epsilon : ℝ) : ℂ :=
  ∫ u in Ioo (-1 : ℝ) 1, angularAbelIntegrand s t epsilon u

def angularBoundaryIntegral (s : ℂ) (t : ℝ) : ℂ :=
  ∫ u in Ioo (-1 : ℝ) 1, angularBoundaryIntegrand s t u

def angularMajorantConstant (s : ℂ) (t : ℝ) : ℝ :=
  Real.exp (Real.pi * |(s + 2 * I * (t : ℂ)).im|) * ‖Gamma (s + 2 * I * (t : ℂ))‖

theorem angularAbelIntegrand_measurable (s : ℂ) (t epsilon : ℝ) :
    Measurable (angularAbelIntegrand s t epsilon) := by
  unfold angularAbelIntegrand nativeOrderWeight orderPoissonIntegrand
  fun_prop

private theorem angularAbelIntegrand_norm_le {s : ℂ} (hs : 0 < s.re)
    (t epsilon : ℝ) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (hu0 : u ≠ 0) :
    ‖angularAbelIntegrand s t epsilon u‖ ≤
      angularMajorantConstant s t * angularAbelEnvelope s.re u := by
  have ha : 0 < (s + 2 * I * (t : ℂ)).re := by simpa using hs
  have hrate := angularAbelRate_power_norm_le ha epsilon hu0
  have hw : ‖nativeOrderWeight t u‖ =
      ‖JBesselPoissonEvenMoments20261025a.poissonWeight 0 u‖ :=
    orderPoissonIntegrand_norm_imaginary (by simp) 0 hu
  rw [angularAbelIntegrand, norm_mul, norm_mul, hw]
  calc
    _ ≤ ‖JBesselPoissonEvenMoments20261025a.poissonWeight 0 u‖ *
        ((Real.exp (Real.pi * |(s + 2 * I * (t : ℂ)).im|) *
          |u| ^ (-(s + 2 * I * (t : ℂ)).re)) *
          ‖Gamma (s + 2 * I * (t : ℂ))‖) := by
      apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right hrate (norm_nonneg _)
    _ = angularMajorantConstant s t * angularAbelEnvelope s.re u := by
      have hre : (s + 2 * I * (t : ℂ)).re = s.re := by simp
      rw [hre]
      unfold angularMajorantConstant angularAbelEnvelope
      ring

theorem angularAbelIntegrand_integrable {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (t epsilon : ℝ) :
    IntegrableOn (angularAbelIntegrand s t epsilon) (Ioo (-1 : ℝ) 1) := by
  apply ((angularAbelEnvelope_integrable hs1).const_mul (angularMajorantConstant s t)).mono'
    (angularAbelIntegrand_measurable s t epsilon).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_neq (0 : ℝ)] with u hu hu0
  exact angularAbelIntegrand_norm_le hs0 t epsilon hu hu0

theorem angularBoundaryIntegrand_integrable {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (t : ℝ) :
    IntegrableOn (angularBoundaryIntegrand s t) (Ioo (-1 : ℝ) 1) := by
  simpa only [angularAbelIntegrand, angularBoundaryIntegrand, Complex.ofReal_zero, zero_sub] using
    angularAbelIntegrand_integrable hs0 hs1 t 0

/-- Genuine angular dominated convergence through u=0 and both endpoints. -/
theorem angularAbelIntegral_tendsto_zero {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (t : ℝ) :
    Tendsto (angularAbelIntegral s t) (𝓝 (0 : ℝ)) (𝓝 (angularBoundaryIntegral s t)) := by
  unfold angularAbelIntegral angularBoundaryIntegral
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u => angularMajorantConstant s t * angularAbelEnvelope s.re u)
  · exact Eventually.of_forall (fun epsilon =>
      (angularAbelIntegrand_measurable s t epsilon).aestronglyMeasurable)
  · exact Eventually.of_forall (fun epsilon => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_neq (0 : ℝ)] with u hu hu0
      exact angularAbelIntegrand_norm_le hs0 t epsilon hu hu0)
  · exact (angularAbelEnvelope_integrable hs1).const_mul (angularMajorantConstant s t)
  · filter_upwards [ae_neq (0 : ℝ)] with u hu0
    exact ((angularAbelRate_power_tendsto (s + 2 * I * (t : ℂ)) hu0)
      .mul_const (Gamma (s + 2 * I * (t : ℂ)))).const_mul (nativeOrderWeight t u)

/-- Actual undamped J Mellin integral identified with the still-literal
boundary angular integral, using two proved Abel limits and exact damped
Poisson/Gamma equality. No final Mellin evaluation is a premise. -/
theorem actualJMellinIntegral_eq_angularBoundary {s : ℂ}
    (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2) (t : ℝ) :
    actualJMellinIntegral s t = poissonMellinConstant t * angularBoundaryIntegral s t := by
  have hl : Tendsto (actualJAbelIntegral s t) (𝓝[>] (0 : ℝ))
      (𝓝 (actualJMellinIntegral s t)) :=
    (actualJAbelIntegral_tendsto_zero hs0 hsHalf t).mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hr : Tendsto (fun epsilon : ℝ => poissonMellinConstant t * angularAbelIntegral s t epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 (poissonMellinConstant t * angularBoundaryIntegral s t)) :=
    ((angularAbelIntegral_tendsto_zero hs0 (by linarith : s.re < 1) t)
      .const_mul (poissonMellinConstant t)).mono_left nhdsWithin_le_nhds
  have he : actualJAbelIntegral s t =ᶠ[𝓝[>] (0 : ℝ)]
      (fun epsilon => poissonMellinConstant t * angularAbelIntegral s t epsilon) := by
    filter_upwards [self_mem_nhdsWithin] with epsilon he
    exact actualJAbelIntegral_eq_poissonGamma hs0 t he
  exact tendsto_nhds_unique_of_eventuallyEq hl hr he

end
end ImbalancedChen.Part3.ActualJMellinAngularAbelLimit20261026b
