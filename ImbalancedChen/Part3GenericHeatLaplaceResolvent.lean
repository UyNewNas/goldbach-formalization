import ImbalancedChen.Part3GenericPositiveResolventHeat
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Genuine Bochner heat Laplace transform for arbitrary primitive positive
self-adjoint contractive injective R on an arbitrary complex Hilbert space.
The result is the generic shiftedResolvent R a from the reusable positive
resolvent calculus. Time integrability and all integral identities are
proved, with no concrete whole-plane Hilbert space or integral supplier.
-/

namespace ImbalancedChen.Part3.GenericHeatLaplaceResolvent20261025a
noncomputable section
open MeasureTheory Set Filter Topology
open ImbalancedChen.Part3.GenericPositiveResolventHeat20261025a
open ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : ResolventData H)

abbrev genericRa (a : ℝ) : H →L[ℂ] H :=
  PositiveContractionResolventCalculus20261025a.shiftedResolvent D.R a

def scalarShiftedResolvent (a : ℝ) (ha : 0 < a) : C(Spectrum D, ℝ) :=
  ⟨fun t => resolventRatio a (t : ℝ),
    (continuousOn_resolventRatio D.R D.nonneg D.norm_le_one ha).domRestrict⟩

theorem scalarShiftedResolvent_apply (a : ℝ) (ha : 0 < a) (t : Spectrum D) :
    scalarShiftedResolvent D a ha t = (t : ℝ) / denominator a (t : ℝ) := rfl

theorem cfcMap_scalarShiftedResolvent (a : ℝ) (ha : 0 < a) :
    cfcMap D (scalarShiftedResolvent D a ha) = genericRa D a :=
  (cfc_apply (resolventRatio a) D.R D.selfAdjoint
    (continuousOn_resolventRatio D.R D.nonneg D.norm_le_one ha)).symm

theorem shifted_scalar_identity (a : ℝ) (ha : 0 < a) {t : Spectrum D}
    (ht : 0 < (t : ℝ)) :
    (a + spectralLambda D t)⁻¹ = scalarShiftedResolvent D a ha t := by
  have hd := denominator_pos ha (spectrum_coordinate_mem_unitInterval D t)
  have hl : 0 < a + spectralLambda D t :=
    add_pos_of_pos_of_nonneg ha (spectralLambda_nonneg D ht)
  change (a + spectralLambda D t)⁻¹ = resolventRatio a (t : ℝ)
  unfold spectralLambda at hl ⊢
  unfold resolventRatio denominator at hd ⊢
  field_simp [ht.ne', hd.ne', hl.ne']
  <;> ring

theorem continuousOn_heatScalar_positive : ContinuousOn (heatScalar D) (Ioi (0 : ℝ)) := by
  have hc : Continuous (fun s : Ioi (0 : ℝ) => positiveHeatScalar D (s : ℝ)) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : Ioi (0 : ℝ) × Spectrum D =>
      Real.exp (p.1 : ℝ) * expNegInvGlue ((p.2 : ℝ) / (p.1 : ℝ)))
    have htime : Continuous (fun p : Ioi (0 : ℝ) × Spectrum D => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hcoord : Continuous (fun p : Ioi (0 : ℝ) × Spectrum D => (p.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    exact (Real.continuous_exp.comp htime).mul
      ((expNegInvGlue.contDiff : ContDiff ℝ 0 expNegInvGlue).continuous.comp
        (hcoord.div htime (fun p => ne_of_gt p.1.property)))
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun s : Ioi (0 : ℝ) => heatScalar D (s : ℝ))
  have heq : (fun s : Ioi (0 : ℝ) => heatScalar D (s : ℝ)) =
      (fun s : Ioi (0 : ℝ) => positiveHeatScalar D (s : ℝ)) :=
    funext fun s => heatScalar_of_pos D s.property
  rw [heq]
  exact hc

def dampedHeatScalar (a s : ℝ) : C(Spectrum D, ℝ) :=
  Real.exp (-a * s) • heatScalar D s

theorem dampedHeatScalar_apply (a s : ℝ) (t : Spectrum D) :
    dampedHeatScalar D a s t = Real.exp (-a * s) * heatScalar D s t := rfl

theorem dampedHeatScalar_norm_le (a s : ℝ) :
    ‖dampedHeatScalar D a s‖ ≤ Real.exp (-a * s) := by
  have hh : ‖heatScalar D s‖ ≤ (1 : ℝ) := by
    apply (ContinuousMap.norm_le _ zero_le_one).2
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (heatScalar_mem_unitInterval D s t).1]
    exact (heatScalar_mem_unitInterval D s t).2
  rw [dampedHeatScalar, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hh (Real.exp_pos (-a * s)).le

/-- Exponential damping gives genuine Bochner integrability before any
functional-calculus or integral identity is invoked. -/
theorem dampedHeatScalar_integrableOn (a : ℝ) (ha : 0 < a) :
    IntegrableOn (dampedHeatScalar D a) (Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn (dampedHeatScalar D a) (Ioi (0 : ℝ)) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (-a * s))).continuousOn.smul
      (continuousOn_heatScalar_positive D)
  exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi)
    (Eventually.of_forall fun s => dampedHeatScalar_norm_le D a s)

/-- Pointwise integration in the actual compact spectrum gives the
literal positive shifted resolvent multiplier; no a.e. spectral rewrite
is needed, since both sides vanish at the zero endpoint. -/
theorem integral_dampedHeatScalar (a : ℝ) (ha : 0 < a) :
    (∫ s : ℝ in Ioi 0, dampedHeatScalar D a s) = scalarShiftedResolvent D a ha := by
  ext t
  rw [ContinuousMap.integral_apply (dampedHeatScalar_integrableOn D a ha) t]
  by_cases ht : (t : ℝ) = 0
  · calc
      _ = ∫ _s : ℝ in Ioi 0, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        rw [dampedHeatScalar_apply D, heatScalar_of_pos D hs, positiveHeatScalar_zero D s ht, mul_zero]
      _ = 0 := integral_zero
      _ = scalarShiftedResolvent D a ha t := by
        rw [scalarShiftedResolvent_apply D, ht]
        simp
  · have htp : 0 < (t : ℝ) := lt_of_le_of_ne
      (spectrum_coordinate_mem_unitInterval D t).1 (Ne.symm ht)
    have hrate : 0 < a + spectralLambda D t :=
      add_pos_of_pos_of_nonneg ha (spectralLambda_nonneg D htp)
    calc
      _ = ∫ s : ℝ in Ioi 0, Real.exp (-(a + spectralLambda D t) * s) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        rw [dampedHeatScalar_apply D, heatScalar_apply_of_pos D hs htp, ← Real.exp_add]
        congr 1
        ring
      _ = -Real.exp (-(a + spectralLambda D t) * 0) / (-(a + spectralLambda D t)) :=
        integral_exp_mul_Ioi (neg_neg_of_pos hrate) 0
      _ = (a + spectralLambda D t)⁻¹ := by simp
      _ = scalarShiftedResolvent D a ha t := shifted_scalar_identity D a ha htp

theorem cfcL_dampedHeatScalar (a s : ℝ) :
    cfcL D.selfAdjoint (dampedHeatScalar D a s) =
      Real.exp (-a * s) • heatOperator D s := by
  change cfcMap D (Real.exp (-a * s) • heatScalar D s) = _
  rw [map_smul]
  rfl

/-- The operator-valued actual heat Laplace integrand is Bochner
integrable in operator norm, from continuous linear CFC and the proved
scalar Banach-valued integrability. -/
theorem dampedHeatOperator_integrableOn (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => Real.exp (-a * s) • heatOperator D s) (Ioi (0 : ℝ)) := by
  have h := (cfcL D.selfAdjoint).integrable_comp
    (dampedHeatScalar_integrableOn D a ha)
  simpa only [cfcL_dampedHeatScalar D] using h

/-- Actual Bochner time-Laplace transform equals the actual shifted
Friedrichs resolvent, with no assumed integral representation. -/
theorem integral_dampedHeatOperator (a : ℝ) (ha : 0 < a) :
    (∫ s : ℝ in Ioi 0, Real.exp (-a * s) • heatOperator D s) = genericRa D a := by
  calc
    _ = ∫ s : ℝ in Ioi 0, cfcL D.selfAdjoint (dampedHeatScalar D a s) := by
      simp only [cfcL_dampedHeatScalar D]
    _ = cfcL D.selfAdjoint (∫ s : ℝ in Ioi 0, dampedHeatScalar D a s) :=
      (cfcL D.selfAdjoint).integral_comp_comm
        (dampedHeatScalar_integrableOn D a ha)
    _ = genericRa D a := by
      rw [integral_dampedHeatScalar D a ha]
      exact cfcMap_scalarShiftedResolvent D a ha

/-- Every actual L2 forcing has a genuinely Bochner-integrable damped
heat trajectory. Real scalar action is the canonical restriction of the
complex scalar action on the actual Hilbert space. -/
theorem dampedHeatTrajectory_integrableOn (a : ℝ) (ha : 0 < a) (f : H) :
    IntegrableOn (fun s : ℝ => Real.exp (-a * s) • heatOperator D s f) (Ioi (0 : ℝ)) := by
  exact (dampedHeatOperator_integrableOn D a ha).apply_continuousLinearMap f

theorem integral_dampedHeatTrajectory (a : ℝ) (ha : 0 < a) (f : H) :
    (∫ s : ℝ in Ioi 0, Real.exp (-a * s) • heatOperator D s f) = genericRa D a f := by
  have h := congrArg (fun T : (H →L[ℂ] H) => T f) (integral_dampedHeatOperator D a ha)
  rw [ContinuousLinearMap.integral_apply (dampedHeatOperator_integrableOn D a ha) f] at h
  exact h

end
end ImbalancedChen.Part3.GenericHeatLaplaceResolvent20261025a
