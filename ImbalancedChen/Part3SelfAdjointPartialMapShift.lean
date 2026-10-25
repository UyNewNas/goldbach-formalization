import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A genuine native partial-operator shift lemma on an arbitrary Hilbert
space. Subtraction of the identity leaves the EXACT original domain
unchanged. Its graph and the adjoint graph are transformed by the same
explicit shear (u,v) -> (u,u+v). This proves native self-adjointness of
the shift from native self-adjointness of the original partial operator.
No bounded-inverse construction or shifted self-adjointness is assumed.
-/

namespace ImbalancedChen.Part3.SelfAdjointPartialMapShift20261025a

noncomputable section
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Native partial map T-I, with the domain of T, not an ambient total
map equipped with arbitrary values outside its true domain. -/
def shiftMinusIdentity (T : H →ₗ.[𝕜] H) : H →ₗ.[𝕜] H :=
  (-(LinearMap.id : H →ₗ[𝕜] H)) +ᵥ T

@[simp] theorem shiftMinusIdentity_domain (T : H →ₗ.[𝕜] H) :
    (shiftMinusIdentity T).domain = T.domain := rfl

theorem shiftMinusIdentity_apply (T : H →ₗ.[𝕜] H) (u : T.domain) :
    shiftMinusIdentity T u = T u - (u : H) := by
  change -(u : H) + T u = T u - (u : H)
  abel

/-- The exact graph shear, valid without density or symmetry assumptions. -/
theorem shiftMinusIdentity_mem_graph_iff (T : H →ₗ.[𝕜] H) {u v : H} :
    (u, v) ∈ (shiftMinusIdentity T).graph ↔ (u, u + v) ∈ T.graph := by
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x, hx, hval⟩
    refine ⟨x, hx, ?_⟩
    rw [shiftMinusIdentity_apply] at hval
    calc
      T x = (x : H) + (T x - (x : H)) := by abel
      _ = u + v := by rw [hx, hval]
  · rintro ⟨x, hx, hval⟩
    refine ⟨x, hx, ?_⟩
    rw [shiftMinusIdentity_apply, hval, hx]
    abel

/-- The SAME shear identifies adjoint graphs, with no density hypothesis
needed for this statement about the actual adjoint submodules. -/
theorem shiftMinusIdentity_mem_graph_adjoint_iff (T : H →ₗ.[𝕜] H) {u v : H} :
    (u, v) ∈ (shiftMinusIdentity T).graph.adjoint ↔
      (u, u + v) ∈ T.graph.adjoint := by
  rw [Submodule.mem_adjoint_iff, Submodule.mem_adjoint_iff]
  constructor
  · intro h a b hab
    have hshift : (a, b - a) ∈ (shiftMinusIdentity T).graph := by
      apply (shiftMinusIdentity_mem_graph_iff T).mpr
      convert hab using 1 <;> abel
    have ht := h a (b - a) hshift
    rw [inner_sub_left] at ht
    rw [inner_add_right]
    linear_combination ht
  · intro h a b hab
    have ht := h a (a + b) ((shiftMinusIdentity_mem_graph_iff T).mp hab)
    rw [inner_add_left, inner_add_right] at ht
    linear_combination ht

/-- True equality with the native unbounded adjoint after the shift. -/
theorem shiftMinusIdentity_isSelfAdjoint (T : H →ₗ.[𝕜] H)
    (hT : IsSelfAdjoint T) : IsSelfAdjoint (shiftMinusIdentity T) := by
  have hdense : Dense ((shiftMinusIdentity T).domain : Set H) := hT.dense_domain
  have hgraph : T.graph.adjoint = T.graph := by
    rw [← LinearPMap.adjoint_graph_eq_graph_adjoint hT.dense_domain]
    exact congrArg LinearPMap.graph (LinearPMap.isSelfAdjoint_def.mp hT)
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hdense]
  apply SetLike.ext
  rintro ⟨u, v⟩
  rw [shiftMinusIdentity_mem_graph_adjoint_iff, hgraph,
    shiftMinusIdentity_mem_graph_iff]

theorem shiftMinusIdentity_isClosed (T : H →ₗ.[𝕜] H)
    (hT : IsSelfAdjoint T) : (shiftMinusIdentity T).IsClosed :=
  (shiftMinusIdentity_isSelfAdjoint T hT).isClosed

end
end ImbalancedChen.Part3.SelfAdjointPartialMapShift20261025a
