import ImbalancedChen.Part3ActualResolventZeroAtomPushforward
import ImbalancedChen.Part3ActualFriedrichsSelfAdjointOperator
import Mathlib.Tactic.Module

/-!
Actual positive shifts of the genuine Friedrichs operator. Real CFC at R
constructs t/(1+(a-1)t); a pair of actual CFC inverse-normalizer identities
proves both directions of the inverse relation with the true Friedrichs
graph. The actual pushed-forward scalar measure represents each shift.
No resolvent or spectral representation supplier is assumed.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualShiftedFriedrichsResolvents20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a
open ImbalancedChen.Part3.ActualFriedrichsSelfAdjointOperator20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
open ImbalancedChen.Part3.ActualResolventZeroAtomPushforward20261025a

def scalarDenominator (a : ℝ) : C(ResolventSpectrum, ℝ) :=
  1 + (a - 1) • spectrumCoordinate

theorem scalarDenominator_apply (a : ℝ) (t : ResolventSpectrum) :
    scalarDenominator a t = 1 + (a - 1) * (t : ℝ) := rfl

theorem scalarDenominator_lower (a : ℝ) (t : ResolventSpectrum) :
    min 1 a ≤ scalarDenominator a t := by
  have ht := spectrum_coordinate_mem_unitInterval t
  rw [scalarDenominator_apply]
  by_cases ha : 1 ≤ a
  · rw [min_eq_left ha]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) ht.1]
  · have ha' : a ≤ 1 := le_of_lt (lt_of_not_ge ha)
    rw [min_eq_right ha']
    nlinarith [mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr ht.2)]

theorem scalarDenominator_pos {a : ℝ} (ha : 0 < a) (t : ResolventSpectrum) :
    0 < scalarDenominator a t :=
  (lt_min zero_lt_one ha).trans_le (scalarDenominator_lower a t)

def scalarInverseDenominator (a : ℝ) (ha : 0 < a) : C(ResolventSpectrum, ℝ) where
  toFun t := 1 / scalarDenominator a t
  continuous_toFun := continuous_const.div (scalarDenominator a).continuous
    (fun t => (scalarDenominator_pos ha t).ne')

def scalarShiftedResolvent (a : ℝ) (ha : 0 < a) : C(ResolventSpectrum, ℝ) :=
  scalarInverseDenominator a ha * spectrumCoordinate

theorem scalarShiftedResolvent_apply (a : ℝ) (ha : 0 < a) (t : ResolventSpectrum) :
    scalarShiftedResolvent a ha t = (t : ℝ) / scalarDenominator a t := by
  change (1 / scalarDenominator a t) * (t : ℝ) = _
  ring

def normalizer (a : ℝ) : ResolventAlgebra := resolventCFC (scalarDenominator a)
def inverseNormalizer (a : ℝ) (ha : 0 < a) : ResolventAlgebra :=
  resolventCFC (scalarInverseDenominator a ha)

/-- The actual CFC function is exactly t/(1+(a-1)t). -/
def shiftedResolvent (a : ℝ) (ha : 0 < a) : ResolventAlgebra :=
  resolventCFC (scalarShiftedResolvent a ha)

theorem normalizer_eq (a : ℝ) :
    normalizer a = 1 + (((a - 1 : ℝ) : ℂ) • actualWeakResolvent) := by
  unfold normalizer scalarDenominator
  rw [map_add, map_one, map_smul, resolventCFC_coordinate]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]

theorem normalizer_apply (a : ℝ) (u : HyperbolicL2) :
    normalizer a u = u + (((a - 1 : ℝ) : ℂ) • actualWeakResolvent u) := by
  rw [normalizer_eq]
  rfl

theorem inverseNormalizer_mul_normalizer (a : ℝ) (ha : 0 < a) :
    inverseNormalizer a ha * normalizer a = 1 := by
  have hscalar : scalarInverseDenominator a ha * scalarDenominator a = 1 := by
    ext t
    change (1 / scalarDenominator a t) * scalarDenominator a t = 1
    exact one_div_mul_cancel (scalarDenominator_pos ha t).ne'
  change resolventCFC (scalarInverseDenominator a ha) * resolventCFC (scalarDenominator a) = 1
  rw [← map_mul, hscalar, map_one]

theorem normalizer_mul_inverseNormalizer (a : ℝ) (ha : 0 < a) :
    normalizer a * inverseNormalizer a ha = 1 := by
  have hscalar : scalarDenominator a * scalarInverseDenominator a ha = 1 := by
    ext t
    change scalarDenominator a t * (1 / scalarDenominator a t) = 1
    exact mul_one_div_cancel (scalarDenominator_pos ha t).ne'
  change resolventCFC (scalarDenominator a) * resolventCFC (scalarInverseDenominator a ha) = 1
  rw [← map_mul, hscalar, map_one]

theorem shiftedResolvent_eq_inverseNormalizer_mul (a : ℝ) (ha : 0 < a) :
    shiftedResolvent a ha = inverseNormalizer a ha * actualWeakResolvent := by
  unfold shiftedResolvent scalarShiftedResolvent inverseNormalizer
  rw [map_mul, resolventCFC_coordinate]

theorem normalizer_mul_shiftedResolvent (a : ℝ) (ha : 0 < a) :
    normalizer a * shiftedResolvent a ha = actualWeakResolvent := by
  rw [shiftedResolvent_eq_inverseNormalizer_mul, ← mul_assoc,
    normalizer_mul_inverseNormalizer, one_mul]

theorem scalarShiftedResolvent_nonneg (a : ℝ) (ha : 0 < a) (t : ResolventSpectrum) :
    0 ≤ scalarShiftedResolvent a ha t := by
  rw [scalarShiftedResolvent_apply]
  exact div_nonneg (spectrum_coordinate_mem_unitInterval t).1 (scalarDenominator_pos ha t).le

theorem scalarShiftedResolvent_le (a : ℝ) (ha : 0 < a) (t : ResolventSpectrum) :
    scalarShiftedResolvent a ha t ≤ 1 / a := by
  rw [scalarShiftedResolvent_apply]
  apply (div_le_div_iff₀ (scalarDenominator_pos ha t) ha).2
  rw [scalarDenominator_apply]
  nlinarith [(spectrum_coordinate_mem_unitInterval t).2]

/-- Genuine operator-norm control of every positive shifted inverse. -/
theorem shiftedResolvent_opNorm_le (a : ℝ) (ha : 0 < a) :
    ‖shiftedResolvent a ha‖ ≤ 1 / a := by
  change ‖cfcHom actualWeakResolvent_selfAdjoint (scalarShiftedResolvent a ha)‖ ≤ _
  rw [norm_cfcHom actualWeakResolvent (scalarShiftedResolvent a ha) actualWeakResolvent_selfAdjoint]
  apply (ContinuousMap.norm_le _ (by positivity : (0 : ℝ) ≤ 1 / a)).2
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (scalarShiftedResolvent_nonneg a ha t)]
  exact scalarShiftedResolvent_le a ha t

theorem shiftedResolvent_norm_le (a : ℝ) (ha : 0 < a) (f : HyperbolicL2) :
    ‖shiftedResolvent a ha f‖ ≤ (1 / a) * ‖f‖ :=
  ((shiftedResolvent a ha).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (shiftedResolvent_opNorm_le a ha) (norm_nonneg f))

/-- Every pair in the actual Friedrichs graph is inverted by the actual
positive shift constructed from R. -/
theorem shiftedResolvent_on_graph (a : ℝ) (ha : 0 < a)
    {u v : HyperbolicL2} (hgraph : (u, v) ∈ friedrichsGraph) :
    shiftedResolvent a ha ((a : ℂ) • u + v) = u := by
  have hR := (mem_friedrichsGraph_iff (u, v)).mp hgraph
  have hv : actualWeakResolvent v = u - actualWeakResolvent u := by
    apply (eq_sub_iff_add_eq).2
    simpa only [map_add, add_comm] using hR
  have hnormal : actualWeakResolvent ((a : ℂ) • u + v) = normalizer a u := by
    rw [map_add, map_smul, hv, normalizer_apply]
    push_cast
    module
  calc
    _ = inverseNormalizer a ha (actualWeakResolvent ((a : ℂ) • u + v)) := by
      rw [shiftedResolvent_eq_inverseNormalizer_mul]
      rfl
    _ = inverseNormalizer a ha (normalizer a u) := by rw [hnormal]
    _ = u := by
      have h := congrArg (fun T : ResolventAlgebra => T u) (inverseNormalizer_mul_normalizer a ha)
      exact h

/-- Conversely every ambient forcing has an actual graph pair with
the shifted inverse as its input coordinate. -/
theorem shiftedResolvent_graph_pair (a : ℝ) (ha : 0 < a) (f : HyperbolicL2) :
    (shiftedResolvent a ha f, f - (a : ℂ) • shiftedResolvent a ha f) ∈ friedrichsGraph := by
  let u := shiftedResolvent a ha f
  have hnormal : normalizer a u = actualWeakResolvent f :=
    congrArg (fun T : ResolventAlgebra => T f) (normalizer_mul_shiftedResolvent a ha)
  apply (mem_friedrichsGraph_iff _).2
  change actualWeakResolvent (u + (f - (a : ℂ) • u)) = u
  rw [map_add, map_sub, map_smul, ← hnormal, normalizer_apply]
  push_cast
  module

theorem existsUnique_shifted_graph_solution (a : ℝ) (ha : 0 < a) (f : HyperbolicL2) :
    ∃! u : HyperbolicL2, (u, f - (a : ℂ) • u) ∈ friedrichsGraph := by
  refine ⟨shiftedResolvent a ha f, shiftedResolvent_graph_pair a ha f, ?_⟩
  intro u hu
  have h := shiftedResolvent_on_graph a ha hu
  have hs : (a : ℂ) • u + (f - (a : ℂ) • u) = f := by abel
  rw [hs] at h
  exact h.symm

theorem shifted_scalar_identity (a : ℝ) (ha : 0 < a) {t : ResolventSpectrum}
    (ht : 0 < (t : ℝ)) :
    (a + spectralLambda t)⁻¹ = scalarShiftedResolvent a ha t := by
  have hd := scalarDenominator_pos ha t
  have hl : 0 < a + spectralLambda t := add_pos_of_pos_of_nonneg ha (spectralLambda_nonneg ht)
  rw [scalarShiftedResolvent_apply, scalarDenominator_apply]
  unfold spectralLambda at hl ⊢
  field_simp [ht.ne', hd.ne', hl.ne']
  <;> ring

/-- The actual unbounded-coordinate scalar measure represents every
positive shifted Friedrichs resolvent, using its proved zero-atom removal. -/
theorem scalar_shifted_resolvent_integral (a : ℝ) (ha : 0 < a) (f : HyperbolicL2) :
    (∫ lambda : ℝ, (a + lambda)⁻¹ ∂unboundedScalarMeasure f) =
      (inner ℂ f (shiftedResolvent a ha f)).re := by
  have hm : Measurable (fun lambda : ℝ => (a + lambda)⁻¹) := by fun_prop
  rw [unboundedScalarMeasure,
    integral_map_of_stronglyMeasurable measurable_spectralLambda hm.stronglyMeasurable]
  have heq : (fun t : ResolventSpectrum => (a + spectralLambda t)⁻¹) =ᵐ[scalarMeasure f]
      (fun t => scalarShiftedResolvent a ha t) := by
    filter_upwards [scalarMeasure_coordinate_pos_ae f] with t ht
    exact shifted_scalar_identity a ha ht
  rw [integral_congr_ae heq]
  exact scalarMeasure_integral f (scalarShiftedResolvent a ha)

end

end ImbalancedChen.Part3.ActualShiftedFriedrichsResolvents20261025a
