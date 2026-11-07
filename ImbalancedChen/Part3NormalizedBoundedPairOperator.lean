import ImbalancedChen.Part3InjectiveSelfAdjointPartialInverse

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
A native unbounded self-adjoint operator from a normalized bounded pair.
For the subsequent measurable real multiplier m the pair is
B=(1+m^2)^(-1), C=m/(1+m^2). This module supplies the nontrivial native
graph theorem, not a premise asserting the desired unbounded result.
-/

namespace ImbalancedChen.Part3.NormalizedBoundedPairOperator20261025a

noncomputable section
open Set
open ImbalancedChen.Part3.InjectiveSelfAdjointPartialInverse20261025a

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (B C : H →L[𝕜] H)

def pairEquation : (H × H) →L[𝕜] H :=
  B.comp (ContinuousLinearMap.snd 𝕜 H H) - C.comp (ContinuousLinearMap.fst 𝕜 H H)

def pairOperator : H →ₗ.[𝕜] H := (pairEquation B C).ker.toLinearPMap

theorem pairOperator_graph (hBinj : Function.Injective B) :
    (pairOperator B C).graph = (pairEquation B C).ker := by
  apply Submodule.toLinearPMap_graph_eq
  intro p hp hp0
  apply hBinj
  have h : B p.2 - C p.1 = 0 := hp
  simpa only [hp0, map_zero, sub_zero] using h

theorem pairOperator_mem_graph_iff (hBinj : Function.Injective B) {u v : H} :
    (u,v) ∈ (pairOperator B C).graph ↔ B v = C u := by
  rw [pairOperator_graph B C hBinj]
  change B v - C u = 0 ↔ B v = C u
  exact sub_eq_zero

theorem pairOperator_mem_domain_iff (hBinj : Function.Injective B) (u : H) :
    u ∈ (pairOperator B C).domain ↔ ∃ v, B v = C u := by
  rw [LinearPMap.mem_domain_iff]
  simp only [pairOperator_mem_graph_iff B C hBinj]

theorem pairOperator_isClosed (hBinj : Function.Injective B) :
    (pairOperator B C).IsClosed := by
  rw [LinearPMap.IsClosed, pairOperator_graph B C hBinj]
  exact (pairEquation B C).isClosed_ker

theorem pairOperator_core_pair (hBinj : Function.Injective B)
    (hcomm : B.comp C = C.comp B) (x : H) :
    (B x, C x) ∈ (pairOperator B C).graph := by
  apply (pairOperator_mem_graph_iff B C hBinj).mpr
  exact congrArg (fun T : H →L[𝕜] H => T x) hcomm

theorem pairOperator_dense_domain (hB : IsSelfAdjoint B) (hBinj : Function.Injective B)
    (hcomm : B.comp C = C.comp B) : Dense ((pairOperator B C).domain : Set H) := by
  apply (rangeR_dense B hB hBinj).mono
  rintro u ⟨x, rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (pairOperator_core_pair B C hBinj hcomm x)

/-- The normalization identity reconstructs the first graph coordinate
from two bounded maps applied to the graph pair. -/
theorem pairOperator_graph_reconstruction (hBinj : Function.Injective B)
    (hcomm : B.comp C = C.comp B) (hsq : B.comp B + C.comp C = B)
    {u v : H} (huv : (u,v) ∈ (pairOperator B C).graph) : B u + C v = u := by
  have hv := (pairOperator_mem_graph_iff B C hBinj).mp huv
  apply hBinj
  calc
    B (B u + C v) = B (B u) + B (C v) := map_add B _ _
    _ = B (B u) + C (B v) := by
      rw [show B (C v) = C (B v) from congrArg (fun T : H →L[𝕜] H => T v) hcomm]
    _ = B (B u) + C (C u) := by rw [hv]
    _ = B u := congrArg (fun T : H →L[𝕜] H => T u) hsq

theorem pairOperator_graph_symmetric (hB : IsSelfAdjoint B) (hC : IsSelfAdjoint C)
    (hBinj : Function.Injective B) (hcomm : B.comp C = C.comp B)
    (hsq : B.comp B + C.comp C = B) {u v x y : H}
    (huv : (u,v) ∈ (pairOperator B C).graph)
    (hxy : (x,y) ∈ (pairOperator B C).graph) :
    inner 𝕜 v x = inner 𝕜 u y := by
  have hv := (pairOperator_mem_graph_iff B C hBinj).mp huv
  have hy := (pairOperator_mem_graph_iff B C hBinj).mp hxy
  have hu := pairOperator_graph_reconstruction B C hBinj hcomm hsq huv
  have hx := pairOperator_graph_reconstruction B C hBinj hcomm hsq hxy
  calc
    inner 𝕜 v x = inner 𝕜 v (B x + C y) := congrArg (inner 𝕜 v) hx.symm
    _ = inner 𝕜 (B v) x + inner 𝕜 (C v) y := by
      rw [inner_add_right, ← hB.isSymmetric v x, ← hC.isSymmetric v y]
    _ = inner 𝕜 (C u) x + inner 𝕜 (C v) y := by rw [hv]
    _ = inner 𝕜 u (C x) + inner 𝕜 (C v) y := by rw [hC.isSymmetric u x]
    _ = inner 𝕜 u (B y) + inner 𝕜 (C v) y := by rw [hy]
    _ = inner 𝕜 (B u + C v) y := by rw [inner_add_left, hB.isSymmetric u y]
    _ = inner 𝕜 u y := by rw [hu]

/-- The native adjoint graph is computed, including its entire domain.
Testing on the explicit dense core (B x,C x) gives the reverse inclusion. -/
theorem pairOperator_adjoint_graph (hB : IsSelfAdjoint B) (hC : IsSelfAdjoint C)
    (hBinj : Function.Injective B) (hcomm : B.comp C = C.comp B)
    (hsq : B.comp B + C.comp C = B) :
    (pairOperator B C).adjoint.graph = (pairOperator B C).graph := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (pairOperator_dense_domain B C hB hBinj hcomm)]
  apply SetLike.ext
  intro p
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro hp
    apply (pairOperator_mem_graph_iff B C hBinj).mpr
    apply ext_inner_left 𝕜
    intro x
    have hx := sub_eq_zero.mp (hp (B x) (C x) (pairOperator_core_pair B C hBinj hcomm x))
    calc
      inner 𝕜 x (B p.2) = inner 𝕜 (B x) p.2 := (hB.isSymmetric x p.2).symm
      _ = inner 𝕜 (C x) p.1 := hx.symm
      _ = inner 𝕜 x (C p.1) := hC.isSymmetric x p.1
  · intro hp a b hab
    exact sub_eq_zero.mpr (pairOperator_graph_symmetric B C hB hC hBinj hcomm hsq hab hp)

theorem pairOperator_isSelfAdjoint (hB : IsSelfAdjoint B) (hC : IsSelfAdjoint C)
    (hBinj : Function.Injective B) (hcomm : B.comp C = C.comp B)
    (hsq : B.comp B + C.comp C = B) : IsSelfAdjoint (pairOperator B C) :=
  LinearPMap.isSelfAdjoint_def.mpr (LinearPMap.eq_of_eq_graph
    (pairOperator_adjoint_graph B C hB hC hBinj hcomm hsq))

end
end ImbalancedChen.Part3.NormalizedBoundedPairOperator20261025a
