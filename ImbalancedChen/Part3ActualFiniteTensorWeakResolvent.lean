import ImbalancedChen.Part3FiniteTensorGalerkinResolvent
import ImbalancedChen.Part3MaassFiniteCoreL2LinearOperator

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The trial space is the actual canonical hyperbolic L2 span of a given
finite family of compact C2 tensors. The actual coordinate Laplacian
restriction is constructed from the proved linear graph; neither an
operator restriction, graph certificate, coercivity nor invertibility is
an input of the final theorem. No independence of the supplied tensors is
needed. The weak equation retains the actual L2 inner product throughout.

This is finite Galerkin solvability. Infinite-dimensional graph closure,
domain density, self-adjointness and the Maass spectral resolution remain
separate obligations.
-/

namespace ImbalancedChen.Part3.ActualFiniteTensorWeakResolvent20261025a

noncomputable section

open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a
open ImbalancedChen.Part3.FiniteTensorGalerkinResolvent20261025a

/-- The literal finite trial space inside canonical hyperbolic L2. -/
def actualFiniteTensorSpan (n : ℕ) (T : Fin n → CompactTensor) :
    Submodule ℂ HyperbolicL2 :=
  Submodule.span ℂ (Set.range (fun i : Fin n => finiteCoreL2 {i} T))

instance actualFiniteTensorSpan_finiteDimensional
    (n : ℕ) (T : Fin n → CompactTensor) :
    FiniteDimensional ℂ (actualFiniteTensorSpan n T) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/-- Every vector of the finite span is in the proved actual Maass graph
domain, including dependencies and cancellations among the generators. -/
theorem actualFiniteTensorSpan_le_domain (n : ℕ) (T : Fin n → CompactTensor) :
    actualFiniteTensorSpan n T ≤ actualTensorDomain := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact finiteCoreL2_mem_actualTensorDomain {i} T

/-- The operator is the restriction of the actual coordinate Laplacian;
no choice of an abstract positive matrix enters its definition. -/
def actualFiniteTensorLaplacian (n : ℕ) (T : Fin n → CompactTensor) :
    actualFiniteTensorSpan n T →ₗ[ℂ] HyperbolicL2 :=
  restrictActualTensorLaplacian (actualFiniteTensorSpan n T)
    (actualFiniteTensorSpan_le_domain n T)

theorem actualFiniteTensorLaplacian_mem_graph
    (n : ℕ) (T : Fin n → CompactTensor) (u : actualFiniteTensorSpan n T) :
    ((u : HyperbolicL2), actualFiniteTensorLaplacian n T u) ∈ finiteTensorL2Graph :=
  restrictActualTensorLaplacian_mem_graph (actualFiniteTensorSpan n T)
    (actualFiniteTensorSpan_le_domain n T) u

/-- Arbitrary actual finite tensor trials admit exactly one weak solution
of `1 + Maass` for every ambient L2 forcing, with the contraction bound.
There is no assumed resolvent, independent basis or positive form supplier. -/
theorem existsUnique_actualFiniteTensor_weak_resolvent
    (n : ℕ) (T : Fin n → CompactTensor) (f : HyperbolicL2) :
    ∃! u : actualFiniteTensorSpan n T,
      (∀ v : actualFiniteTensorSpan n T,
        inner ℂ (v : HyperbolicL2)
            ((u : HyperbolicL2) + actualFiniteTensorLaplacian n T u) =
          inner ℂ (v : HyperbolicL2) f) ∧
        ‖(u : HyperbolicL2)‖ ≤ ‖f‖ := by
  exact existsUnique_weakSolution (actualFiniteTensorSpan n T)
    (actualFiniteTensorLaplacian n T)
    (actualFiniteTensorLaplacian_mem_graph n T) f

end
end ImbalancedChen.Part3.ActualFiniteTensorWeakResolvent20261025a
