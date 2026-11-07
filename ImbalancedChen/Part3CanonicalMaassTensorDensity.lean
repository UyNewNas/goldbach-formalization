import ImbalancedChen.Part3CanonicalPlanarL2Unitary
import ImbalancedChen.Part3UpperSupportedTensorL2Closure
import ImbalancedChen.Part3MaassTensorHeightLift

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Actual canonical-domain density, transported from the actual planar tensor
span through the actual hyperbolic-to-planar L² unitary. The inverse of
each planar test is the actual compact tensor with height-multiplied
vertical factor. No density premise is supplied by the caller.
Both density and unitary dependencies are frozen source-only modules.
-/

namespace ImbalancedChen.Part3.CanonicalMaassTensorDensity20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a
open ImbalancedChen.Part3.MaassTensorHeightLift20261025a
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
open ImbalancedChen.Part3.MaassGradientUpperSupportClosure20261025a
open ImbalancedChen.Part3.PositiveRectangleSmoothTensorDensity20261025a
open ImbalancedChen.Part3.UpperSupportedTensorL2Closure20261025a
open ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly

def canonicalToPlane : HyperbolicL2 →ₗᵢ[ℂ] PlaneL2 :=
  upperSupportedSubmodule.subtypeₗᵢ.comp canonicalPlanarUnitary.toLinearIsometry

/-- Actual compact canonical tensors are dense in canonical hyperbolic L².
The proof uses a closed isometric image of their actual domain closure. -/
theorem actualTensorDomain_dense : Dense (actualTensorDomain : Set HyperbolicL2) := by
  let M : Submodule ℂ PlaneL2 :=
    actualTensorDomain.topologicalClosure.map canonicalToPlane.toLinearMap
  have hclosed : IsClosed (M : Set PlaneL2) := by
    change IsClosed ((actualTensorDomain.topologicalClosure.map
      canonicalToPlane.toLinearMap : Submodule ℂ PlaneL2) : Set PlaneL2)
    rw [Submodule.map_coe]
    exact canonicalToPlane.isometry.isClosedEmbedding.isClosedMap _
      actualTensorDomain.isClosed_topologicalClosure
  have htest : smoothTensorL2Span ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨T, rfl⟩
    let Q : CompactTensor := toMaassTensor T
    let F : HyperbolicL2 := finiteCoreL2 (Finset.univ : Finset (Fin 1))
      (fun _ => heightMultiplyTensor Q)
    have hF : F ∈ actualTensorDomain.topologicalClosure :=
      actualTensorDomain.le_topologicalClosure
        (finiteCoreL2_mem_actualTensorDomain Finset.univ (fun _ : Fin 1 => heightMultiplyTensor Q))
    refine ⟨F, hF, ?_⟩
    have he := canonicalPlanarUnitary.apply_symm_apply
      ⟨testL2 Q, testL2_mem_upperSupported Q⟩
    rw [unitary_inverse_testL2] at he
    exact congrArg (fun x : upperSupportedSubmodule => (x : PlaneL2)) he
  have hall : upperSupportedSubmodule ≤ M := by
    rw [← smoothTensorL2Span_topologicalClosure_eq_upperSupported]
    exact smoothTensorL2Span.topologicalClosure_minimal htest hclosed
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro F _
  have hLF : canonicalToPlane F ∈ upperSupportedSubmodule :=
    (canonicalPlanarUnitary F).property
  obtain ⟨G, hG, hGF⟩ := hall hLF
  exact (canonicalToPlane.injective hGF) ▸ hG

end

end ImbalancedChen.Part3.CanonicalMaassTensorDensity20261025a
