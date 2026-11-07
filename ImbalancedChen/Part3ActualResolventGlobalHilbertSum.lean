import ImbalancedChen.Part3ActualResolventCyclicReduction
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Actual whole-space Hilbert assembly of the scalar-measure cyclic models.
The index is the actual maximal orthogonal family, with no countability
assumption. Mathlib's lp family at exponent two supplies the external
Hilbert sum. Its sum map is isometric by genuine orthogonality and onto
by the proved totality of the actual cyclic subspaces and completeness.
No unitary, density, or whole-space representation premise is accepted.
-/

namespace ImbalancedChen.Part3.ActualResolventGlobalHilbertSum20261025a

noncomputable section

open Set MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualResolventContinuousCyclic20261025a
open ImbalancedChen.Part3.ActualResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.ActualResolventCyclicReduction20261025a

abbrev ActualSpectralIndex := actualCyclicSeeds

local instance : DecidableEq ActualSpectralIndex := Classical.decEq _

abbrev ActualSpectralFiber (i : ActualSpectralIndex) := ScalarL2 (i : HyperbolicL2)

abbrev ActualSpectralSum := lp ActualSpectralFiber 2

def actualFiberEmbedding (i : ActualSpectralIndex) :
    ActualSpectralFiber i →ₗᵢ[ℂ] HyperbolicL2 := cyclicIsometry (i : HyperbolicL2)

theorem actualFiberEmbedding_range (i : ActualSpectralIndex) :
    (actualFiberEmbedding i).toLinearMap.range = cyclicSubspace (i : HyperbolicL2) :=
  cyclicIsometry_range_eq (i : HyperbolicL2)

/-- Pairwise orthogonality is proved from the actual Zorn family and the
exact ranges of the actual scalar-measure cyclic embeddings. -/
theorem actualFiberEmbedding_orthogonal :
    OrthogonalFamily ℂ ActualSpectralFiber actualFiberEmbedding := by
  intro i j hij ξ η
  have hne : (i : HyperbolicL2) ≠ (j : HyperbolicL2) := by
    intro h
    exact hij (Subtype.ext h)
  have hspaces : cyclicSubspace (i : HyperbolicL2) ⟂ cyclicSubspace (j : HyperbolicL2) :=
    actualCyclicSeeds_orthogonal.1 i.property j.property hne
  apply hspaces.inner_eq
  · rw [← actualFiberEmbedding_range i]
    exact ⟨ξ, rfl⟩
  · rw [← actualFiberEmbedding_range j]
    exact ⟨η, rfl⟩

theorem actualFiberEmbedding_total :
    (⨆ i : ActualSpectralIndex, (actualFiberEmbedding i).toLinearMap.range).topologicalClosure =
      (⊤ : Submodule ℂ HyperbolicL2) := by
  simp only [actualFiberEmbedding_range]
  exact actualCyclicSeeds_total

/-- The actual complete Hilbert space is the Hilbert sum of its actual
scalar spectral measures; onto follows from actual totality. -/
def actualScalarHilbertSum :
    IsHilbertSum ℂ ActualSpectralFiber actualFiberEmbedding :=
  IsHilbertSum.mk actualFiberEmbedding_orthogonal
    (by rw [actualFiberEmbedding_total])

/-- The whole actual physical-space unitary, in the synthesis direction. -/
def actualSpectralUnitary : ActualSpectralSum ≃ₗᵢ[ℂ] HyperbolicL2 :=
  actualScalarHilbertSum.linearIsometryEquiv.symm

theorem actualSpectralUnitary_apply (ξ : ActualSpectralSum) :
    actualSpectralUnitary ξ = ∑' i : ActualSpectralIndex, actualFiberEmbedding i (ξ i) :=
  actualScalarHilbertSum.linearIsometryEquiv_symm_apply ξ

theorem actualSpectralUnitary_hasSum (ξ : ActualSpectralSum) :
    HasSum (fun i : ActualSpectralIndex => actualFiberEmbedding i (ξ i))
      (actualSpectralUnitary ξ) :=
  actualScalarHilbertSum.hasSum_linearIsometryEquiv_symm ξ

theorem actualSpectralUnitary_norm (ξ : ActualSpectralSum) :
    ‖actualSpectralUnitary ξ‖ = ‖ξ‖ := actualSpectralUnitary.norm_map ξ

/-- Every actual physical L2 vector is reconstructed by its actual cyclic
scalar coordinates, including for the unrestricted index set. -/
theorem actualSpectral_reconstruction (f : HyperbolicL2) :
    (∑' i : ActualSpectralIndex,
      actualFiberEmbedding i ((actualSpectralUnitary.symm f) i)) = f := by
  rw [← actualSpectralUnitary_apply, actualSpectralUnitary.apply_symm_apply]

theorem actualSpectralUnitary_single (i : ActualSpectralIndex)
    (ξ : ActualSpectralFiber i) :
    actualSpectralUnitary (lp.single 2 i ξ) = actualFiberEmbedding i ξ := by
  classical
  exact actualScalarHilbertSum.linearIsometryEquiv_symm_apply_single ξ

end
end ImbalancedChen.Part3.ActualResolventGlobalHilbertSum20261025a
