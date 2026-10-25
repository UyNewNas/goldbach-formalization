import ImbalancedChen.Part3GenericResolventGlobalSpectralAssembly
import ImbalancedChen.Part3GenericCyclicBorelProjection

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Global projections for every Borel subset of the real spectrum, on any
complex Hilbert space and for any bounded self-adjoint operator. The
unrestricted Hilbert sum and its unitary are the proved Zorn construction.
This module proves the projection algebra; strong countable additivity is
provided separately. No totality, projection or unitary premise is used.
-/

namespace ImbalancedChen.Part3.GenericGlobalBorelProjection20261025a

noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a
open ImbalancedChen.Part3.GenericCyclicBorelProjection20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

def diagonalBorel (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    SpectralSum R hSA →L[ℂ] SpectralSum R hSA :=
  lp.mapCLM 2 (fun i => borelMultiplier R hSA (i : H) B hB) zero_le_one
    (fun i => borelMultiplier_opNorm_le_one R hSA (i : H) B hB)

theorem diagonalBorel_apply (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (ξ : SpectralSum R hSA) (i : SpectralIndex R hSA) :
    diagonalBorel R hSA B hB ξ i = borelMultiplier R hSA (i : H) B hB (ξ i) := rfl

theorem diagonalBorel_opNorm_le_one (B : Set (ResolventSpectrum R))
    (hB : MeasurableSet B) : ‖diagonalBorel R hSA B hB‖ ≤ 1 :=
  lp.norm_mapCLM_le _ _ _ _

theorem diagonalBorel_norm_le (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (ξ : SpectralSum R hSA) : ‖diagonalBorel R hSA B hB ξ‖ ≤ ‖ξ‖ := by
  calc
    _ ≤ ‖diagonalBorel R hSA B hB‖ * ‖ξ‖ := (diagonalBorel R hSA B hB).le_opNorm ξ
    _ ≤ 1 * ‖ξ‖ := mul_le_mul_of_nonneg_right
      (diagonalBorel_opNorm_le_one R hSA B hB) (norm_nonneg ξ)
    _ = _ := one_mul _

theorem diagonalBorel_inner (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (ξ η : SpectralSum R hSA) :
    inner ℂ (diagonalBorel R hSA B hB ξ) η =
      inner ℂ ξ (diagonalBorel R hSA B hB η) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  exact borelMultiplier_inner R hSA (i : H) B hB (ξ i) (η i)

theorem diagonalBorel_selfAdjoint (B : Set (ResolventSpectrum R))
    (hB : MeasurableSet B) : IsSelfAdjoint (diagonalBorel R hSA B hB) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (diagonalBorel_inner R hSA B hB)

theorem diagonalBorel_comp_inter (B C : Set (ResolventSpectrum R))
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (diagonalBorel R hSA B hB).comp (diagonalBorel R hSA C hC) =
      diagonalBorel R hSA (B ∩ C) (hB.inter hC) := by
  ext ξ i
  exact congrArg (fun T : ScalarL2 R hSA (i : H) →L[ℂ] ScalarL2 R hSA (i : H) => T (ξ i))
    (borelMultiplier_comp_inter R hSA (i : H) B C hB hC)

theorem diagonalBorel_idempotent (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    (diagonalBorel R hSA B hB).comp (diagonalBorel R hSA B hB) = diagonalBorel R hSA B hB := by
  simpa only [Set.inter_self] using diagonalBorel_comp_inter R hSA B B hB hB

theorem diagonalBorel_empty : diagonalBorel R hSA ∅ MeasurableSet.empty = 0 := by
  ext ξ i
  change borelMultiplier R hSA (i : H) ∅ MeasurableSet.empty (ξ i) = 0
  rw [borelMultiplier_empty]
  rfl

theorem diagonalBorel_univ : diagonalBorel R hSA Set.univ MeasurableSet.univ =
    ContinuousLinearMap.id ℂ (SpectralSum R hSA) := by
  ext ξ i
  change borelMultiplier R hSA (i : H) Set.univ MeasurableSet.univ (ξ i) = ξ i
  rw [borelMultiplier_univ]
  rfl

/-- Transport the actual fiber indicator through the constructed global unitary. -/
def globalBorelProjection (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) : H →L[ℂ] H :=
  (spectralUnitary R hSA).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((diagonalBorel R hSA B hB).comp
      (spectralUnitary R hSA).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem globalBorelProjection_apply (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (u : H) : globalBorelProjection R hSA B hB u =
      spectralUnitary R hSA (diagonalBorel R hSA B hB ((spectralUnitary R hSA).symm u)) := rfl

theorem globalBorelProjection_norm_le (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (u : H) : ‖globalBorelProjection R hSA B hB u‖ ≤ ‖u‖ := by
  rw [globalBorelProjection_apply, (spectralUnitary R hSA).norm_map]
  exact (diagonalBorel_norm_le R hSA B hB _).trans_eq
    ((spectralUnitary R hSA).symm.norm_map u)

theorem globalBorelProjection_inner (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (u v : H) : inner ℂ (globalBorelProjection R hSA B hB u) v =
      inner ℂ u (globalBorelProjection R hSA B hB v) := by
  let U := spectralUnitary R hSA
  change inner ℂ (U (diagonalBorel R hSA B hB (U.symm u))) v =
    inner ℂ u (U (diagonalBorel R hSA B hB (U.symm v)))
  calc
    _ = inner ℂ (diagonalBorel R hSA B hB (U.symm u)) (U.symm v) := by
      simpa only [U.apply_symm_apply] using
        U.inner_map_map (diagonalBorel R hSA B hB (U.symm u)) (U.symm v)
    _ = inner ℂ (U.symm u) (diagonalBorel R hSA B hB (U.symm v)) :=
      diagonalBorel_inner R hSA B hB _ _
    _ = _ := by
      simpa only [U.apply_symm_apply] using
        (U.inner_map_map (U.symm u) (diagonalBorel R hSA B hB (U.symm v))).symm

theorem globalBorelProjection_selfAdjoint (B : Set (ResolventSpectrum R))
    (hB : MeasurableSet B) : IsSelfAdjoint (globalBorelProjection R hSA B hB) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (globalBorelProjection_inner R hSA B hB)

theorem globalBorelProjection_comp_inter (B C : Set (ResolventSpectrum R))
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (globalBorelProjection R hSA B hB).comp (globalBorelProjection R hSA C hC) =
      globalBorelProjection R hSA (B ∩ C) (hB.inter hC) := by
  apply ContinuousLinearMap.ext
  intro u
  let U := spectralUnitary R hSA
  change U (diagonalBorel R hSA B hB (U.symm (U (diagonalBorel R hSA C hC (U.symm u))))) =
    U (diagonalBorel R hSA (B ∩ C) (hB.inter hC) (U.symm u))
  rw [U.symm_apply_apply]
  exact congrArg U (congrArg (fun T : SpectralSum R hSA →L[ℂ] SpectralSum R hSA => T (U.symm u))
    (diagonalBorel_comp_inter R hSA B C hB hC))

theorem globalBorelProjection_idempotent (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    (globalBorelProjection R hSA B hB).comp (globalBorelProjection R hSA B hB) =
      globalBorelProjection R hSA B hB := by
  simpa only [Set.inter_self] using globalBorelProjection_comp_inter R hSA B B hB hB

theorem globalBorelProjection_empty : globalBorelProjection R hSA ∅ MeasurableSet.empty = 0 := by
  ext u
  rw [globalBorelProjection_apply, diagonalBorel_empty]
  simp only [ContinuousLinearMap.zero_apply, map_zero]

theorem globalBorelProjection_univ : globalBorelProjection R hSA Set.univ MeasurableSet.univ =
    ContinuousLinearMap.id ℂ H := by
  ext u
  rw [globalBorelProjection_apply, diagonalBorel_univ]
  exact (spectralUnitary R hSA).apply_symm_apply u

end
end ImbalancedChen.Part3.GenericGlobalBorelProjection20261025a
