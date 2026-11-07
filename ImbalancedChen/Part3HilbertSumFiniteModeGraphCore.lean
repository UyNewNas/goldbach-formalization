import ImbalancedChen.Part3HilbertSumFriedrichsOperator
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The genuine finite-mode graph core of the unbounded Hilbert direct sum.
Every full graph pair is the convergent sum of its actual single-mode
graph pairs. Consequently the graph is exactly the closure of the span
of these pairs. This uses convergence in BOTH physical and output norms;
plain density in the underlying physical L2 space would be insufficient.

The coordinate graph vectors use full coordinate domains. No claim of
smooth compact graph-core density is made. Physical closed-form core
identification is a separate step.
-/

namespace ImbalancedChen.Part3.HilbertSumFiniteModeGraphCore20261026b
noncomputable section
open Set
open GenericFriedrichsOperator20261025a
open HilbertSumFriedrichsOperator20261026b

variable {ι : Type*} {H : ι → Type*}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

local instance : DecidableEq ι := Classical.decEq ι

/-- Actual graph pairs supported in one mode, with no output chosen
outside the true coordinate operator domain. -/
def singleModeGraphPairs (R : ∀ i, H i →L[ℂ] H i) :
    Set (HilbertSum (H := H) × HilbertSum (H := H)) :=
  {p | ∃ (i : ι) (u v : H i), (u, v) ∈ (friedrichsR (R i)).graph ∧
    p = (lp.single 2 i u, lp.single 2 i v)}

theorem singleModeGraphPairs_subset (R : ∀ i, H i →L[ℂ] H i)
    (hRnorm : ∀ i, ‖R i‖ ≤ 1) (hinj : ∀ i, Function.Injective (R i)) :
    singleModeGraphPairs R ⊆ (sumOperator R hRnorm).graph := by
  classical
  rintro p ⟨i, u, v, huv, rfl⟩
  apply (sumOperator_graph_iff R hRnorm hinj _ _).mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [lp.single_apply, Pi.single_eq_same] using huv
  · have hz : ((0 : H j), (0 : H j)) ∈ (friedrichsR (R j)).graph :=
      (friedrichsR (R j)).graph.zero_mem
    simpa [lp.single_apply, hji] using hz

/-- The actual graph pair is reconstructed in graph norm from finite-mode
pieces; no separate domain approximation premise is supplied. -/
theorem graphPair_hasSum_singleModes (u v : HilbertSum (H := H)) :
    HasSum (fun i => (lp.single 2 i (u i), lp.single 2 i (v i))) (u, v) :=
  (lp.hasSum_single (by norm_num) u).prodMk
    (lp.hasSum_single (by norm_num) v)

/-- Exact graph closure of genuine finite-mode graph vectors. Closedness
is the proved closedness of the constructed unbounded sum operator. -/
theorem sumOperator_graph_eq_finiteModeClosure (R : ∀ i, H i →L[ℂ] H i)
    (hRnorm : ∀ i, ‖R i‖ ≤ 1) (hinj : ∀ i, Function.Injective (R i)) :
    (sumOperator R hRnorm).graph =
      (Submodule.span ℂ (singleModeGraphPairs R)).topologicalClosure := by
  apply le_antisymm
  · rintro ⟨u, v⟩ huv
    have hcoord := (sumOperator_graph_iff R hRnorm hinj u v).mp huv
    have hsingle : ∀ i,
        (lp.single 2 i (u i), lp.single 2 i (v i)) ∈
          (Submodule.span ℂ (singleModeGraphPairs R)).topologicalClosure := by
      intro i
      apply Submodule.le_topologicalClosure
      exact Submodule.subset_span ⟨i, u i, v i, hcoord i, rfl⟩
    apply (Submodule.isClosed_topologicalClosure
      (Submodule.span ℂ (singleModeGraphPairs R))).mem_of_tendsto
      (graphPair_hasSum_singleModes u v)
    exact Filter.Eventually.of_forall fun s =>
      (Submodule.span ℂ (singleModeGraphPairs R)).topologicalClosure.sum_mem
        (fun i _ => hsingle i)
  · apply Submodule.topologicalClosure_minimal
    · exact Submodule.span_le.mpr (singleModeGraphPairs_subset R hRnorm hinj)
    · exact sumOperator_isClosed R hRnorm hinj

end
end ImbalancedChen.Part3.HilbertSumFiniteModeGraphCore20261026b
