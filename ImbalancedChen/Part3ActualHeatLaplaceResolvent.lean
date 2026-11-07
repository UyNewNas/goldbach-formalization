import ImbalancedChen.Part3ActualFriedrichsHeatSemigroup
import ImbalancedChen.Part3ActualShiftedFriedrichsResolvents
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The genuine Bochner Laplace transform of the actual heat semigroup equals
the actual shifted Friedrichs resolvent. Positive-time continuity is proved
in the Banach space of continuous functions on the actual compact spectrum.
The actual multipliers have norm at most one, so exponential damping proves
Bochner integrability. Point evaluation and the elementary exponential
integral give the literal shifted resolvent multiplier, including t=0.
The actual continuous linear CFC commutes with the Bochner integral.

No time-integrability, Laplace identity, semigroup or resolvent supplier is
assumed. There is no automorphic heat-kernel identification in this result.
-/

namespace ImbalancedChen.Part3.ActualHeatLaplaceResolvent20261025a

noncomputable section

open MeasureTheory Set Filter Topology
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
open ImbalancedChen.Part3.ActualResolventZeroAtomPushforward20261025a
open ImbalancedChen.Part3.ActualFriedrichsHeatSemigroup20261025a
open ImbalancedChen.Part3.ActualShiftedFriedrichsResolvents20261025a

/-- Actual positive-time continuity in the scalar CFC Banach space.
Compactness of the actual spectrum converts joint continuity to this norm
topology; no uniform derivative at time zero is asserted. -/
theorem continuousOn_heatScalar_positive : ContinuousOn heatScalar (Ioi (0 : ℝ)) := by
  have hc : Continuous (fun s : Ioi (0 : ℝ) => positiveHeatScalar (s : ℝ)) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : Ioi (0 : ℝ) × ResolventSpectrum =>
      Real.exp (p.1 : ℝ) * expNegInvGlue ((p.2 : ℝ) / (p.1 : ℝ)))
    have htime : Continuous (fun p : Ioi (0 : ℝ) × ResolventSpectrum => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hcoord : Continuous (fun p : Ioi (0 : ℝ) × ResolventSpectrum => (p.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    exact (Real.continuous_exp.comp htime).mul
      ((expNegInvGlue.contDiff : ContDiff ℝ 0 expNegInvGlue).continuous.comp
        (hcoord.div htime (fun p => ne_of_gt p.1.property)))
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun s : Ioi (0 : ℝ) => heatScalar (s : ℝ))
  have heq : (fun s : Ioi (0 : ℝ) => heatScalar (s : ℝ)) =
      (fun s : Ioi (0 : ℝ) => positiveHeatScalar (s : ℝ)) :=
    funext fun s => heatScalar_of_pos s.property
  rw [heq]
  exact hc

def dampedHeatScalar (a s : ℝ) : C(ResolventSpectrum, ℝ) :=
  Real.exp (-a * s) • heatScalar s

theorem dampedHeatScalar_apply (a s : ℝ) (t : ResolventSpectrum) :
    dampedHeatScalar a s t = Real.exp (-a * s) * heatScalar s t := rfl

theorem dampedHeatScalar_norm_le (a s : ℝ) :
    ‖dampedHeatScalar a s‖ ≤ Real.exp (-a * s) := by
  have hh : ‖heatScalar s‖ ≤ (1 : ℝ) := by
    apply (ContinuousMap.norm_le _ zero_le_one).2
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (heatScalar_mem_unitInterval s t).1]
    exact (heatScalar_mem_unitInterval s t).2
  rw [dampedHeatScalar, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hh (Real.exp_pos (-a * s)).le

/-- Exponential damping gives genuine Bochner integrability before any
functional-calculus or integral identity is invoked. -/
theorem dampedHeatScalar_integrableOn (a : ℝ) (ha : 0 < a) :
    IntegrableOn (dampedHeatScalar a) (Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn (dampedHeatScalar a) (Ioi (0 : ℝ)) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (-a * s))).continuousOn.smul
      continuousOn_heatScalar_positive
  exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi)
    (Eventually.of_forall fun s => dampedHeatScalar_norm_le a s)

/-- Pointwise integration in the actual compact spectrum gives the
literal positive shifted resolvent multiplier; no a.e. spectral rewrite
is needed, since both sides vanish at the zero endpoint. -/
theorem integral_dampedHeatScalar (a : ℝ) (ha : 0 < a) :
    (∫ s : ℝ in Ioi 0, dampedHeatScalar a s) = scalarShiftedResolvent a ha := by
  ext t
  rw [ContinuousMap.integral_apply (dampedHeatScalar_integrableOn a ha) t]
  by_cases ht : (t : ℝ) = 0
  · calc
      _ = ∫ _s : ℝ in Ioi 0, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        rw [dampedHeatScalar_apply, heatScalar_of_pos hs, positiveHeatScalar_zero s ht, mul_zero]
      _ = 0 := integral_zero
      _ = scalarShiftedResolvent a ha t := by
        rw [scalarShiftedResolvent_apply, ht]
        simp
  · have htp : 0 < (t : ℝ) := lt_of_le_of_ne
      (spectrum_coordinate_mem_unitInterval t).1 (Ne.symm ht)
    have hrate : 0 < a + spectralLambda t :=
      add_pos_of_pos_of_nonneg ha (spectralLambda_nonneg htp)
    calc
      _ = ∫ s : ℝ in Ioi 0, Real.exp (-(a + spectralLambda t) * s) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        rw [dampedHeatScalar_apply, heatScalar_apply_of_pos hs htp, ← Real.exp_add]
        congr 1
        ring
      _ = -Real.exp (-(a + spectralLambda t) * 0) / (-(a + spectralLambda t)) :=
        integral_exp_mul_Ioi (neg_neg_of_pos hrate) 0
      _ = (a + spectralLambda t)⁻¹ := by simp
      _ = scalarShiftedResolvent a ha t := shifted_scalar_identity a ha htp

theorem cfcL_dampedHeatScalar (a s : ℝ) :
    cfcL actualWeakResolvent_selfAdjoint (dampedHeatScalar a s) =
      Real.exp (-a * s) • heatOperator s := by
  change resolventCFC (Real.exp (-a * s) • heatScalar s) = _
  rw [map_smul]
  rfl

/-- The operator-valued actual heat Laplace integrand is Bochner
integrable in operator norm, from continuous linear CFC and the proved
scalar Banach-valued integrability. -/
theorem dampedHeatOperator_integrableOn (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => Real.exp (-a * s) • heatOperator s) (Ioi (0 : ℝ)) := by
  have h := (cfcL actualWeakResolvent_selfAdjoint).integrable_comp
    (dampedHeatScalar_integrableOn a ha)
  simpa only [cfcL_dampedHeatScalar] using h

/-- Actual Bochner time-Laplace transform equals the actual shifted
Friedrichs resolvent, with no assumed integral representation. -/
theorem integral_dampedHeatOperator (a : ℝ) (ha : 0 < a) :
    (∫ s : ℝ in Ioi 0, Real.exp (-a * s) • heatOperator s) = shiftedResolvent a ha := by
  calc
    _ = ∫ s : ℝ in Ioi 0, cfcL actualWeakResolvent_selfAdjoint (dampedHeatScalar a s) := by
      simp only [cfcL_dampedHeatScalar]
    _ = cfcL actualWeakResolvent_selfAdjoint (∫ s : ℝ in Ioi 0, dampedHeatScalar a s) :=
      (cfcL actualWeakResolvent_selfAdjoint).integral_comp_comm
        (dampedHeatScalar_integrableOn a ha)
    _ = shiftedResolvent a ha := by
      rw [integral_dampedHeatScalar a ha]
      rfl

/-- Every actual L2 forcing has a genuinely Bochner-integrable damped
heat trajectory. Real scalar action is the canonical restriction of the
complex scalar action on the actual Hilbert space. -/
theorem dampedHeatTrajectory_integrableOn (a : ℝ) (ha : 0 < a) (f : HyperbolicL2) :
    IntegrableOn (fun s : ℝ => Real.exp (-a * s) • heatOperator s f) (Ioi (0 : ℝ)) := by
  exact (dampedHeatOperator_integrableOn a ha).apply_continuousLinearMap f

theorem integral_dampedHeatTrajectory (a : ℝ) (ha : 0 < a) (f : HyperbolicL2) :
    (∫ s : ℝ in Ioi 0, Real.exp (-a * s) • heatOperator s f) = shiftedResolvent a ha f := by
  have h := congrArg (fun T : ResolventAlgebra => T f) (integral_dampedHeatOperator a ha)
  rw [ContinuousLinearMap.integral_apply (dampedHeatOperator_integrableOn a ha) f] at h
  exact h

end
end ImbalancedChen.Part3.ActualHeatLaplaceResolvent20261025a
