import ImbalancedChen.Part3GenericResolventCyclicIntertwining
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Genuine measurable-set projections on the actual generic scalar-measure L²
quotient, transported through the proved cyclic unitary. Indicator maps,
their norm bounds, self-adjointness, idempotence and intersection product
law are constructed and proved directly. No projection-valued-measure
premise occurs. Countable strong additivity is a separate source module.
-/

namespace ImbalancedChen.Part3.GenericCyclicBorelProjection20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R) (f : H)

def borelMultiply (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (ξ : ScalarL2 R hSA f) : ScalarL2 R hSA f :=
  ((Lp.memLp ξ).indicator hB).toLp (B.indicator ξ)

theorem borelMultiply_coe_ae (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (ξ : ScalarL2 R hSA f) :
    borelMultiply R hSA f B hB ξ =ᵐ[scalarMeasure R hSA f] B.indicator ξ :=
  ((Lp.memLp ξ).indicator hB).coeFn_toLp

def borelMultiplyLinear (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    ScalarL2 R hSA f →ₗ[ℂ] ScalarL2 R hSA f where
  toFun := borelMultiply R hSA f B hB
  map_add' ξ η := by
    apply Lp.ext
    filter_upwards [borelMultiply_coe_ae R hSA f B hB (ξ + η), Lp.coeFn_add ξ η,
      Lp.coeFn_add (borelMultiply R hSA f B hB ξ) (borelMultiply R hSA f B hB η),
      borelMultiply_coe_ae R hSA f B hB ξ, borelMultiply_coe_ae R hSA f B hB η]
        with t hleft hin hright hξ hη
    rw [hleft, hright, hξ, hη]
    by_cases ht : t ∈ B
    · simpa only [Set.indicator_of_mem ht] using hin
    · simp only [Set.indicator_of_notMem ht, zero_add]
  map_smul' c ξ := by
    apply Lp.ext
    filter_upwards [borelMultiply_coe_ae R hSA f B hB (c • ξ), Lp.coeFn_smul c ξ,
      Lp.coeFn_smul c (borelMultiply R hSA f B hB ξ),
      borelMultiply_coe_ae R hSA f B hB ξ] with t hleft hin hright hξ
    rw [hleft, hright, hξ]
    by_cases ht : t ∈ B
    · simpa only [Set.indicator_of_mem ht] using hin
    · simp only [Set.indicator_of_notMem ht, smul_zero]

theorem borelMultiply_norm_le (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (ξ : ScalarL2 R hSA f) : ‖borelMultiply R hSA f B hB ξ‖ ≤ ‖ξ‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [borelMultiply_coe_ae R hSA f B hB ξ] with t ht
  rw [ht]
  by_cases hmem : t ∈ B
  · simp only [Set.indicator_of_mem hmem, le_refl]
  · simpa only [Set.indicator_of_notMem hmem, norm_zero] using norm_nonneg (ξ t)

def borelMultiplier (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    ScalarL2 R hSA f →L[ℂ] ScalarL2 R hSA f :=
  (borelMultiplyLinear R hSA f B hB).mkContinuous 1 (by
    intro ξ
    simpa only [one_mul] using borelMultiply_norm_le R hSA f B hB ξ)

theorem borelMultiplier_coe_ae (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (ξ : ScalarL2 R hSA f) :
    borelMultiplier R hSA f B hB ξ =ᵐ[scalarMeasure R hSA f] B.indicator ξ :=
  borelMultiply_coe_ae R hSA f B hB ξ

theorem borelMultiplier_norm_le (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (ξ : ScalarL2 R hSA f) : ‖borelMultiplier R hSA f B hB ξ‖ ≤ ‖ξ‖ :=
  borelMultiply_norm_le R hSA f B hB ξ

theorem borelMultiplier_opNorm_le_one (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    ‖borelMultiplier R hSA f B hB‖ ≤ 1 := by
  apply (borelMultiplier R hSA f B hB).opNorm_le_bound zero_le_one
  intro ξ
  simpa only [one_mul] using borelMultiplier_norm_le R hSA f B hB ξ

theorem borelMultiplier_inner (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (ξ η : ScalarL2 R hSA f) :
    inner ℂ (borelMultiplier R hSA f B hB ξ) η =
      inner ℂ ξ (borelMultiplier R hSA f B hB η) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [borelMultiplier_coe_ae R hSA f B hB ξ,
    borelMultiplier_coe_ae R hSA f B hB η] with t hξ hη
  rw [hξ, hη]
  by_cases ht : t ∈ B
  · simp only [Set.indicator_of_mem ht]
  · simp only [Set.indicator_of_notMem ht, inner_zero_left, inner_zero_right]

theorem borelMultiplier_selfAdjoint (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    IsSelfAdjoint (borelMultiplier R hSA f B hB) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (borelMultiplier_inner R hSA f B hB)

theorem borelMultiplier_comp_inter (B C : Set (ResolventSpectrum R))
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (borelMultiplier R hSA f B hB).comp (borelMultiplier R hSA f C hC) =
      borelMultiplier R hSA f (B ∩ C) (hB.inter hC) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [borelMultiplier_coe_ae R hSA f B hB (borelMultiplier R hSA f C hC ξ),
    borelMultiplier_coe_ae R hSA f C hC ξ,
    borelMultiplier_coe_ae R hSA f (B ∩ C) (hB.inter hC) ξ] with t hleft hmiddle hright
  change (borelMultiplier R hSA f B hB (borelMultiplier R hSA f C hC ξ)) t = _
  rw [hleft, hright]
  by_cases htB : t ∈ B
  · rw [Set.indicator_of_mem htB, hmiddle]
    by_cases htC : t ∈ C <;> simp [htB, htC]
  · simp [htB]

theorem borelMultiplier_idempotent (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    (borelMultiplier R hSA f B hB).comp (borelMultiplier R hSA f B hB) =
      borelMultiplier R hSA f B hB := by
  simpa only [Set.inter_self] using borelMultiplier_comp_inter R hSA f B B hB hB

theorem borelMultiplier_empty : borelMultiplier R hSA f ∅ MeasurableSet.empty = 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [borelMultiplier_coe_ae R hSA f ∅ MeasurableSet.empty ξ,
    Lp.coeFn_zero ℂ (2 : ℝ≥0∞) (scalarMeasure R hSA f)] with t ht hz
  change (borelMultiplier R hSA f ∅ MeasurableSet.empty ξ) t = (0 : ScalarL2 R hSA f) t
  rw [ht, hz]
  simp only [Set.indicator_empty, Pi.zero_apply]

theorem borelMultiplier_univ : borelMultiplier R hSA f Set.univ MeasurableSet.univ =
    ContinuousLinearMap.id ℂ (ScalarL2 R hSA f) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [borelMultiplier_coe_ae R hSA f Set.univ MeasurableSet.univ ξ] with t ht
  simpa only [Set.indicator_univ, ContinuousLinearMap.id_apply] using ht

def cyclicBorelProjection (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    cyclicSubspace R hSA f →L[ℂ] cyclicSubspace R hSA f :=
  (cyclicRepresentation R hSA f).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((borelMultiplier R hSA f B hB).comp
      (cyclicRepresentation R hSA f).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem cyclicBorelProjection_apply (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (u : cyclicSubspace R hSA f) :
    cyclicBorelProjection R hSA f B hB u =
      cyclicRepresentation R hSA f
        (borelMultiplier R hSA f B hB ((cyclicRepresentation R hSA f).symm u)) := rfl

theorem cyclicBorelProjection_norm_le (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (u : cyclicSubspace R hSA f) : ‖cyclicBorelProjection R hSA f B hB u‖ ≤ ‖u‖ := by
  rw [cyclicBorelProjection_apply, (cyclicRepresentation R hSA f).norm_map]
  exact (borelMultiplier_norm_le R hSA f B hB _).trans_eq
    ((cyclicRepresentation R hSA f).symm.norm_map u)

theorem cyclicBorelProjection_opNorm_le_one (B : Set (ResolventSpectrum R))
    (hB : MeasurableSet B) : ‖cyclicBorelProjection R hSA f B hB‖ ≤ 1 := by
  apply (cyclicBorelProjection R hSA f B hB).opNorm_le_bound zero_le_one
  intro u
  simpa only [one_mul] using cyclicBorelProjection_norm_le R hSA f B hB u

theorem cyclicBorelProjection_inner (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (u v : cyclicSubspace R hSA f) :
    inner ℂ (cyclicBorelProjection R hSA f B hB u) v =
      inner ℂ u (cyclicBorelProjection R hSA f B hB v) := by
  let U := cyclicRepresentation R hSA f
  change inner ℂ (U (borelMultiplier R hSA f B hB (U.symm u))) v =
    inner ℂ u (U (borelMultiplier R hSA f B hB (U.symm v)))
  calc
    _ = inner ℂ (borelMultiplier R hSA f B hB (U.symm u)) (U.symm v) := by
      simpa only [U.apply_symm_apply] using
        U.inner_map_map (borelMultiplier R hSA f B hB (U.symm u)) (U.symm v)
    _ = inner ℂ (U.symm u) (borelMultiplier R hSA f B hB (U.symm v)) :=
      borelMultiplier_inner R hSA f B hB _ _
    _ = _ := by
      simpa only [U.apply_symm_apply] using
        (U.inner_map_map (U.symm u) (borelMultiplier R hSA f B hB (U.symm v))).symm

theorem cyclicBorelProjection_selfAdjoint (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    IsSelfAdjoint (cyclicBorelProjection R hSA f B hB) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (cyclicBorelProjection_inner R hSA f B hB)

theorem cyclicBorelProjection_comp_inter (B C : Set (ResolventSpectrum R))
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (cyclicBorelProjection R hSA f B hB).comp (cyclicBorelProjection R hSA f C hC) =
      cyclicBorelProjection R hSA f (B ∩ C) (hB.inter hC) := by
  apply ContinuousLinearMap.ext
  intro u
  let U := cyclicRepresentation R hSA f
  change U (borelMultiplier R hSA f B hB
    (U.symm (U (borelMultiplier R hSA f C hC (U.symm u))))) =
    U (borelMultiplier R hSA f (B ∩ C) (hB.inter hC) (U.symm u))
  rw [U.symm_apply_apply]
  exact congrArg U (congrArg (fun T : ScalarL2 R hSA f →L[ℂ] ScalarL2 R hSA f => T (U.symm u))
    (borelMultiplier_comp_inter R hSA f B C hB hC))

theorem cyclicBorelProjection_idempotent (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    (cyclicBorelProjection R hSA f B hB).comp (cyclicBorelProjection R hSA f B hB) =
      cyclicBorelProjection R hSA f B hB := by
  simpa only [Set.inter_self] using cyclicBorelProjection_comp_inter R hSA f B B hB hB

theorem cyclicBorelProjection_empty :
    cyclicBorelProjection R hSA f ∅ MeasurableSet.empty = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  rw [cyclicBorelProjection_apply, borelMultiplier_empty]
  simp only [ContinuousLinearMap.zero_apply, map_zero]

theorem cyclicBorelProjection_univ :
    cyclicBorelProjection R hSA f Set.univ MeasurableSet.univ =
      ContinuousLinearMap.id ℂ (cyclicSubspace R hSA f) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [cyclicBorelProjection_apply, borelMultiplier_univ]
  exact (cyclicRepresentation R hSA f).apply_symm_apply u

end

end ImbalancedChen.Part3.GenericCyclicBorelProjection20261025a
