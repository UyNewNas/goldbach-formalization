import ImbalancedChen.Part3ActualCompletedEnergyResolvent
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual Friedrichs weak operator reconstructed from the genuine
completed-energy resolvent R. Its graph is the actual closed kernel
R(u+v)-u=0. Injectivity and dense range of R make it an actual densely
defined operator. A direct maximal Green-test identity proves equality
with its native unbounded adjoint, without a self-adjointness premise.
Nonnegativity uses the genuine energy-space norm and physical contraction.

No identification with the earlier minimal differential closure or a
Γ₀ automorphic spectral operator is asserted.
-/

namespace ImbalancedChen.Part3.ActualFriedrichsSelfAdjointOperator20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedTensorEnergyForm20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a

def friedrichsEquation : (HyperbolicL2 × HyperbolicL2) →L[ℂ] HyperbolicL2 :=
  actualWeakResolvent.comp
    (ContinuousLinearMap.fst ℂ HyperbolicL2 HyperbolicL2 +
      ContinuousLinearMap.snd ℂ HyperbolicL2 HyperbolicL2) -
    ContinuousLinearMap.fst ℂ HyperbolicL2 HyperbolicL2

def friedrichsGraph : Submodule ℂ (HyperbolicL2 × HyperbolicL2) :=
  friedrichsEquation.ker

theorem mem_friedrichsGraph_iff (p : HyperbolicL2 × HyperbolicL2) :
    p ∈ friedrichsGraph ↔ actualWeakResolvent (p.1 + p.2) = p.1 := by
  change actualWeakResolvent (p.1 + p.2) - p.1 = 0 ↔ _
  exact sub_eq_zero

theorem isClosed_friedrichsGraph :
    IsClosed (friedrichsGraph : Set (HyperbolicL2 × HyperbolicL2)) :=
  friedrichsEquation.isClosed_ker

theorem friedrichsGraph_vertical_trivial (p : HyperbolicL2 × HyperbolicL2)
    (hp : p ∈ friedrichsGraph) (hzero : p.1 = 0) : p.2 = 0 := by
  have hR := (mem_friedrichsGraph_iff p).mp hp
  apply actualWeakResolvent_injective
  simpa only [hzero, zero_add, map_zero] using hR

theorem friedrichsGraph_right_unique {u v w : HyperbolicL2}
    (huv : (u, v) ∈ friedrichsGraph) (huw : (u, w) ∈ friedrichsGraph) : v = w := by
  have hsum := actualWeakResolvent_injective
    (((mem_friedrichsGraph_iff (u, v)).mp huv).trans
      ((mem_friedrichsGraph_iff (u, w)).mp huw).symm)
  exact add_left_cancel hsum

/-- A native unbounded linear operator, with no junk-value graph branch
because its actual graph has proved trivial vertical fibers. -/
def actualFriedrichs : HyperbolicL2 →ₗ.[ℂ] HyperbolicL2 :=
  friedrichsGraph.toLinearPMap

theorem actualFriedrichs_graph_eq : actualFriedrichs.graph = friedrichsGraph :=
  friedrichsGraph.toLinearPMap_graph_eq friedrichsGraph_vertical_trivial

theorem friedrichs_resolvent_pair (f : HyperbolicL2) :
    (actualWeakResolvent f, f - actualWeakResolvent f) ∈ friedrichsGraph := by
  apply (mem_friedrichsGraph_iff _).mpr
  have hs : actualWeakResolvent f + (f - actualWeakResolvent f) = f := by abel
  rw [hs]

theorem actualFriedrichs_domain_eq_range : actualFriedrichs.domain = actualWeakResolvent.range := by
  apply SetLike.ext
  intro u
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨v, hv⟩
    rw [actualFriedrichs_graph_eq] at hv
    exact ⟨u + v, (mem_friedrichsGraph_iff (u, v)).mp hv⟩
  · rintro ⟨f, hf⟩
    refine ⟨f - u, ?_⟩
    rw [actualFriedrichs_graph_eq, mem_friedrichsGraph_iff]
    have hs : u + (f - u) = f := by abel
    rw [hs]
    exact hf

theorem actualFriedrichs_dense_domain :
    Dense (actualFriedrichs.domain : Set HyperbolicL2) := by
  rw [actualFriedrichs_domain_eq_range]
  exact actualWeakResolvent_denseRange

theorem actualFriedrichs_isClosed : actualFriedrichs.IsClosed := by
  rw [LinearPMap.IsClosed, actualFriedrichs_graph_eq]
  exact isClosed_friedrichsGraph

theorem friedrichsGraph_symmetric {x y u v : HyperbolicL2}
    (hxy : (x, y) ∈ friedrichsGraph) (huv : (u, v) ∈ friedrichsGraph) :
    inner ℂ y u = inner ℂ x v := by
  have hx := (mem_friedrichsGraph_iff (x, y)).mp hxy
  have hu := (mem_friedrichsGraph_iff (u, v)).mp huv
  have hsa := actualWeakResolvent_selfAdjoint.isSymmetric (x + y) (u + v)
  rw [hx, hu, inner_add_right, inner_add_left] at hsa
  exact (add_left_cancel hsa).symm

/-- Maximal adjoint-graph identity, proved by testing against the actual
resolvent pairs `(Rf,f-Rf)` for every f in canonical hyperbolic L². -/
theorem friedrichsGraph_maximal_test (u v : HyperbolicL2) :
    (∀ x y : HyperbolicL2, (x, y) ∈ friedrichsGraph →
      inner ℂ y u = inner ℂ x v) ↔ (u, v) ∈ friedrichsGraph := by
  constructor
  · intro htest
    apply (mem_friedrichsGraph_iff (u, v)).mpr
    apply ext_inner_left ℂ
    intro f
    have ht := htest (actualWeakResolvent f) (f - actualWeakResolvent f)
      (friedrichs_resolvent_pair f)
    rw [inner_sub_left] at ht
    calc
      inner ℂ f (actualWeakResolvent (u + v)) =
          inner ℂ (actualWeakResolvent f) (u + v) :=
        (actualWeakResolvent_selfAdjoint.isSymmetric f (u + v)).symm
      _ = inner ℂ (actualWeakResolvent f) u + inner ℂ (actualWeakResolvent f) v :=
        inner_add_right _ _ _
      _ = inner ℂ f u := by rw [← ht]; ring
  · intro huv x y hxy
    exact friedrichsGraph_symmetric hxy huv

/-- Equality with the native Hilbert adjoint of the actual graph. -/
theorem friedrichsGraph_adjoint_eq : friedrichsGraph.adjoint = friedrichsGraph := by
  apply SetLike.ext
  intro p
  rw [Submodule.mem_adjoint_iff]
  simp only [sub_eq_zero]
  exact friedrichsGraph_maximal_test p.1 p.2

/-- Genuine native unbounded self-adjointness of the actual Friedrichs
weak operator reconstructed from the actual energy resolvent. -/
theorem actualFriedrichs_selfAdjoint : IsSelfAdjoint actualFriedrichs := by
  change actualFriedrichs.adjoint = actualFriedrichs
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint actualFriedrichs_dense_domain,
    actualFriedrichs_graph_eq, friedrichsGraph_adjoint_eq]

theorem friedrichsGraph_nonneg {u v : HyperbolicL2}
    (huv : (u, v) ∈ friedrichsGraph) : 0 ≤ (inner ℂ u v).re := by
  let f : HyperbolicL2 := u + v
  have hu : actualWeakResolvent f = u := (mem_friedrichsGraph_iff (u, v)).mp huv
  have henergy := actualWeakResolvent_quadratic f
  rw [hu] at henergy
  have hnorm : ‖u‖ ≤ ‖energyRieszSolution f‖ := by
    have hp := physicalProjection_norm_le (energyRieszSolution f)
    change ‖actualWeakResolvent f‖ ≤ ‖energyRieszSolution f‖ at hp
    rwa [hu] at hp
  have hself : (inner ℂ u u).re = ‖u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hform : ‖u‖ ^ 2 + (inner ℂ u v).re = ‖energyRieszSolution f‖ ^ 2 := by
    change (inner ℂ (u + v) u).re = ‖energyRieszSolution f‖ ^ 2 at henergy
    rw [inner_add_left, Complex.add_re, hself, inner_re_symm] at henergy
    exact henergy
  have hsq : ‖u‖ ^ 2 ≤ ‖energyRieszSolution f‖ ^ 2 := by gcongr
  linarith

theorem actualFriedrichs_mem_graph (u : actualFriedrichs.domain) :
    ((u : HyperbolicL2), actualFriedrichs u) ∈ friedrichsGraph := by
  rw [← actualFriedrichs_graph_eq]
  exact LinearPMap.mem_graph_iff.mpr ⟨u, rfl, rfl⟩

theorem actualFriedrichs_nonneg (u : actualFriedrichs.domain) :
    0 ≤ (inner ℂ (u : HyperbolicL2) (actualFriedrichs u)).re :=
  friedrichsGraph_nonneg (actualFriedrichs_mem_graph u)

/-- The actual bounded weak resolvent is the inverse of `1+A` on all
right-hand sides, as an equality of the actual operator graph. -/
theorem actualFriedrichs_resolvent_pair (f : HyperbolicL2) :
    (actualWeakResolvent f, f - actualWeakResolvent f) ∈ actualFriedrichs.graph := by
  rw [actualFriedrichs_graph_eq]
  exact friedrichs_resolvent_pair f

theorem actualFriedrichs_shift_surjective (f : HyperbolicL2) :
    ∃ u : actualFriedrichs.domain, (u : HyperbolicL2) + actualFriedrichs u = f := by
  obtain ⟨u, hu, hAu⟩ := LinearPMap.mem_graph_iff.mp (actualFriedrichs_resolvent_pair f)
  refine ⟨u, ?_⟩
  rw [hu, hAu]
  abel

end

end ImbalancedChen.Part3.ActualFriedrichsSelfAdjointOperator20261025a
