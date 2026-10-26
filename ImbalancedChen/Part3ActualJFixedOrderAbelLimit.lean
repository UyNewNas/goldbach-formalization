import ImbalancedChen.Part3ActualJFixedOrderMellinL1
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Honest Abel removal for the actual fixed-order J Mellin integral in the
strip 0<Re(s)<1/2. Actual full-integrand L1 supplies the majorant. No Gamma
evaluation or formula for a regularized integral is an assumption.
The critical opposite-order quotient's held near-zero chain stays unused.
-/

namespace ImbalancedChen.Part3.ActualJFixedOrderAbelLimit20261026b

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
open ActualJFixedOrderMellinL120261026b

def actualJAbelIntegrand (s : ℂ) (t epsilon q : ℝ) : ℂ :=
  (Real.exp (-epsilon * q) : ℂ) * actualJMellinIntegrand s t q

def actualJAbelIntegral (s : ℂ) (t epsilon : ℝ) : ℂ :=
  ∫ q in Ioi (0 : ℝ), actualJAbelIntegrand s t epsilon q

theorem actualJAbelIntegrand_zero (s : ℂ) (t q : ℝ) :
    actualJAbelIntegrand s t 0 q = actualJMellinIntegrand s t q := by
  simp [actualJAbelIntegrand]

theorem actualJAbelIntegrand_norm_le (s : ℂ) (t : ℝ)
    {epsilon q : ℝ} (he : 0 ≤ epsilon) (hq : 0 < q) :
    ‖actualJAbelIntegrand s t epsilon q‖ ≤ ‖actualJMellinIntegrand s t q‖ := by
  rw [actualJAbelIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-epsilon * q) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr he) hq.le)
  exact mul_le_of_le_one_left (norm_nonneg _) hexp

theorem actualJAbelIntegrand_aestronglyMeasurable (s : ℂ) (t epsilon : ℝ) :
    AEStronglyMeasurable (actualJAbelIntegrand s t epsilon) (volume.restrict (Ioi 0)) := by
  have hd : Measurable (fun q : ℝ => (Real.exp (-epsilon * q) : ℂ)) := by fun_prop
  exact hd.aestronglyMeasurable.mul
    ((actualJMellinIntegrand_continuousOn s t).aestronglyMeasurable measurableSet_Ioi)

theorem integrableOn_actualJAbel {s : ℂ}
    (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2) (t : ℝ)
    {epsilon : ℝ} (he : 0 ≤ epsilon) :
    IntegrableOn (actualJAbelIntegrand s t epsilon) (Ioi 0) := by
  apply (integrableOn_actualJMellin_norm hs0 hsHalf t).mono'
    (actualJAbelIntegrand_aestronglyMeasurable s t epsilon)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  exact actualJAbelIntegrand_norm_le s t he hq

/-- The actual damped integrals converge to the actual undamped integral.
This conclusion neither contains nor presupposes a Gamma quotient. -/
theorem actualJAbelIntegral_tendsto_zero {s : ℂ}
    (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2) (t : ℝ) :
    Tendsto (actualJAbelIntegral s t) (𝓝[≥] (0 : ℝ))
      (𝓝 (actualJMellinIntegral s t)) := by
  unfold actualJAbelIntegral actualJMellinIntegral
  apply tendsto_integral_filter_of_dominated_convergence
    (fun q => ‖actualJMellinIntegrand s t q‖)
  · exact Eventually.of_forall (fun epsilon =>
      actualJAbelIntegrand_aestronglyMeasurable s t epsilon)
  · filter_upwards [self_mem_nhdsWithin] with epsilon he
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    exact actualJAbelIntegrand_norm_le s t he hq
  · exact integrableOn_actualJMellin_norm hs0 hsHalf t
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    have hc : Continuous (fun epsilon : ℝ => actualJAbelIntegrand s t epsilon q) := by
      unfold actualJAbelIntegrand
      fun_prop
    have h := hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : (𝓝[≥] (0 : ℝ)) ≤ 𝓝 0)
    simpa only [actualJAbelIntegrand_zero] using h

end
end ImbalancedChen.Part3.ActualJFixedOrderAbelLimit20261026b
