import ImbalancedChen.Part3ActualResolventContinuousCyclic
import Mathlib.Analysis.Normed.Operator.Extend

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
The genuine cyclic scalar-measure L² representation for an actual vector.
Pinned continuous-function density and the actual norm identity descend
the CFC vector map through the actual L² quotient and extend it isometrically.
Completeness gives closed range, proving surjectivity onto the actual
closed complex CFC orbit, without a density or onto premise.
-/

namespace ImbalancedChen.Part3.ActualResolventCyclicL2Representation20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
open ImbalancedChen.Part3.ActualResolventContinuousCyclic20261025a

def cyclicExtension (f : HyperbolicL2) : ScalarL2 f →L[ℂ] HyperbolicL2 :=
  (continuousCyclicMap f).extendOfNorm (spectralToLp f).toLinearMap

private theorem continuousCyclicMap_bound (f : HyperbolicL2) :
    ∀ φ, ‖continuousCyclicMap f φ‖ ≤ 1 * ‖spectralToLp f φ‖ := by
  intro φ
  rw [continuousCyclicMap_norm_eq_L2, one_mul]

theorem cyclicExtension_apply (f : HyperbolicL2) (φ : C(ResolventSpectrum, ℂ)) :
    cyclicExtension f (spectralToLp f φ) = continuousCyclicMap f φ :=
  LinearMap.extendOfNorm_eq (spectralToLp_denseRange f)
    ⟨1, continuousCyclicMap_bound f⟩ φ

theorem cyclicExtension_norm (f : HyperbolicL2) (ξ : ScalarL2 f) :
    ‖cyclicExtension f ξ‖ = ‖ξ‖ := by
  have hcont : Continuous (fun η : ScalarL2 f => ‖cyclicExtension f η‖) :=
    continuous_norm.comp (cyclicExtension f).continuous
  have heq : (fun η : ScalarL2 f => ‖cyclicExtension f η‖) = (fun η => ‖η‖) := by
    apply hcont.ext_on (show Dense (Set.range (spectralToLp f)) from spectralToLp_denseRange f)
      continuous_norm
    rintro η ⟨φ, rfl⟩
    rw [cyclicExtension_apply]
    exact continuousCyclicMap_norm_eq_L2 f φ
  exact congrFun heq ξ

def cyclicIsometry (f : HyperbolicL2) : ScalarL2 f →ₗᵢ[ℂ] HyperbolicL2 where
  toLinearMap := (cyclicExtension f).toLinearMap
  norm_map' := cyclicExtension_norm f

def cyclicSubspace (f : HyperbolicL2) : Submodule ℂ HyperbolicL2 :=
  (LinearMap.range (continuousCyclicMap f)).topologicalClosure

theorem isClosed_cyclicSubspace (f : HyperbolicL2) :
    IsClosed (cyclicSubspace f : Set HyperbolicL2) :=
  (LinearMap.range (continuousCyclicMap f)).isClosed_topologicalClosure

theorem continuousCyclicMap_mem_cyclicSubspace (f : HyperbolicL2)
    (φ : C(ResolventSpectrum, ℂ)) : continuousCyclicMap f φ ∈ cyclicSubspace f :=
  (LinearMap.range (continuousCyclicMap f)).le_topologicalClosure ⟨φ, rfl⟩

/-- The extended isometry has exactly the actual closed CFC orbit as
its range. Surjectivity is proved, rather than supplied. -/
theorem cyclicIsometry_range_eq (f : HyperbolicL2) :
    (cyclicIsometry f).toLinearMap.range = cyclicSubspace f := by
  apply le_antisymm
  · rintro u ⟨ξ, rfl⟩
    have hclosed : IsClosed {η : ScalarL2 f | cyclicExtension f η ∈ cyclicSubspace f} :=
      (isClosed_cyclicSubspace f).preimage (cyclicExtension f).continuous
    have hsub : Set.range (spectralToLp f) ⊆
        {η : ScalarL2 f | cyclicExtension f η ∈ cyclicSubspace f} := by
      rintro η ⟨φ, rfl⟩
      rw [cyclicExtension_apply]
      exact continuousCyclicMap_mem_cyclicSubspace f φ
    exact (closure_minimal hsub hclosed) (spectralToLp_denseRange f ξ)
  · apply (LinearMap.range (continuousCyclicMap f)).topologicalClosure_minimal
    · rintro u ⟨φ, rfl⟩
      exact ⟨spectralToLp f φ, cyclicExtension_apply f φ⟩
    · exact (cyclicIsometry f).isometry.isClosedEmbedding.isClosed_range

def cyclicIsometryToSubspace (f : HyperbolicL2) : ScalarL2 f →ₗᵢ[ℂ] cyclicSubspace f where
  toLinearMap := (cyclicIsometry f).toLinearMap.codRestrict (cyclicSubspace f) (by
    intro ξ
    have h : cyclicIsometry f ξ ∈ (cyclicIsometry f).toLinearMap.range := ⟨ξ, rfl⟩
    rwa [cyclicIsometry_range_eq] at h)
  norm_map' := (cyclicIsometry f).norm_map

theorem cyclicIsometryToSubspace_surjective (f : HyperbolicL2) :
    Function.Surjective (cyclicIsometryToSubspace f) := by
  intro u
  have hu : (u : HyperbolicL2) ∈ (cyclicIsometry f).toLinearMap.range := by
    rw [cyclicIsometry_range_eq]
    exact u.property
  obtain ⟨ξ, hξ⟩ := hu
  refine ⟨ξ, ?_⟩
  apply Subtype.ext
  exact hξ

/-- The genuine cyclic scalar-measure L² representation of the actual
closed CFC orbit of f. This is not a whole-space automorphic decomposition. -/
def cyclicRepresentation (f : HyperbolicL2) : ScalarL2 f ≃ₗᵢ[ℂ] cyclicSubspace f :=
  LinearIsometryEquiv.ofSurjective (cyclicIsometryToSubspace f)
    (cyclicIsometryToSubspace_surjective f)

theorem cyclicRepresentation_continuous (f : HyperbolicL2) (φ : C(ResolventSpectrum, ℂ)) :
    (cyclicRepresentation f (spectralToLp f φ) : HyperbolicL2) = continuousCyclicMap f φ :=
  cyclicExtension_apply f φ

end

end ImbalancedChen.Part3.ActualResolventCyclicL2Representation20261025a
