import ImbalancedChen.Part3CanonicalMaassTensorDensity
import ImbalancedChen.Part3MaassFiniteCoreGraphClosure
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Actual closability of the canonical finite tensor Maass operator, using
genuine canonical-domain density and the genuine closed-graph Green identity.
The closed graph is right unique, so the native `LinearPMap` closure is an
actual closed densely defined symmetric operator. No self-adjointness,
surjectivity of a resolvent or spectral theorem is asserted.
Its actual domain-density supplier is a frozen source-only module.
-/

namespace ImbalancedChen.Part3.ActualMaassClosableOperator20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a
open ImbalancedChen.Part3.MaassFiniteCoreGraphClosure20261025a
open ImbalancedChen.Part3.CanonicalMaassTensorDensity20261025a

def actualPartialMaass : HyperbolicL2 →ₗ.[ℂ] HyperbolicL2 where
  domain := actualTensorDomain
  toFun := actualTensorLaplacian

theorem actualPartialMaass_graph_eq : actualPartialMaass.graph = actualFiniteGraphSubmodule := by
  apply SetLike.ext
  intro p
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨u, hu, hv⟩
    have h := actualTensorLaplacian_mem_graph u
    rw [hu, hv] at h
    exact h
  · intro hp
    let u : actualTensorDomain := ⟨p.1, ⟨p.2, hp⟩⟩
    exact ⟨u, rfl, actualTensorLaplacian_eq_of_mem_graph u hp⟩

theorem actualPartialMaass_closureGraph_eq :
    actualPartialMaass.graph.topologicalClosure = closedTensorGraph := by
  rw [actualPartialMaass_graph_eq]
  rfl

/-- Genuine actual-domain density eliminates every vertical fiber of
the actual topological graph closure. There is no density premise. -/
theorem closedTensorGraph_vertical_trivial (p : HyperbolicL2 × HyperbolicL2)
    (hp : p ∈ closedTensorGraph) (hzero : p.1 = 0) : p.2 = 0 := by
  have hp0 : ((0 : HyperbolicL2), p.2) ∈ closedTensorGraph := by
    rw [← hzero]
    exact hp
  apply actualTensorDomain_dense.eq_zero_of_inner_left ℂ
  intro u hu
  exact closedTensorGraph_zero_input_annihilates_actualDomain hp0 ⟨u, hu⟩

theorem closedTensorGraph_right_unique {f g h : HyperbolicL2}
    (hfg : (f, g) ∈ closedTensorGraph) (hfh : (f, h) ∈ closedTensorGraph) : g = h := by
  have hdiff : ((0 : HyperbolicL2), g - h) ∈ closedTensorGraph := by
    have hsub := closedTensorGraph.sub_mem hfg hfh
    change (f - f, g - h) ∈ closedTensorGraph at hsub
    simpa only [sub_self] using hsub
  exact sub_eq_zero.mp (closedTensorGraph_vertical_trivial (0, g - h) hdiff rfl)

/-- The actual coordinate Maass operator is closable in canonical L². -/
theorem actualPartialMaass_isClosable : actualPartialMaass.IsClosable := by
  refine ⟨closedTensorGraph.toLinearPMap, ?_⟩
  rw [actualPartialMaass_closureGraph_eq]
  exact (closedTensorGraph.toLinearPMap_graph_eq closedTensorGraph_vertical_trivial).symm

def actualClosedMaass : HyperbolicL2 →ₗ.[ℂ] HyperbolicL2 :=
  actualPartialMaass.closure

theorem actualClosedMaass_graph_eq : actualClosedMaass.graph = closedTensorGraph := by
  calc
    _ = actualPartialMaass.graph.topologicalClosure :=
      actualPartialMaass_isClosable.graph_closure_eq_closure_graph.symm
    _ = _ := actualPartialMaass_closureGraph_eq

theorem actualClosedMaass_isClosed : actualClosedMaass.IsClosed :=
  actualPartialMaass_isClosable.closure_isClosed

theorem actualClosedMaass_extends : actualPartialMaass ≤ actualClosedMaass :=
  actualPartialMaass.le_closure

theorem actualClosedMaass_dense_domain : Dense (actualClosedMaass.domain : Set HyperbolicL2) :=
  actualTensorDomain_dense.mono actualClosedMaass_extends.1

theorem actualClosedMaass_mem_graph (u : actualClosedMaass.domain) :
    ((u : HyperbolicL2), actualClosedMaass u) ∈ closedTensorGraph := by
  rw [← actualClosedMaass_graph_eq]
  exact LinearPMap.mem_graph_iff.mpr ⟨u, rfl, rfl⟩

theorem actualClosedMaass_symmetric (u v : actualClosedMaass.domain) :
    inner ℂ (actualClosedMaass u) (v : HyperbolicL2) =
      inner ℂ (u : HyperbolicL2) (actualClosedMaass v) :=
  closedTensorGraph_symmetric (actualClosedMaass_mem_graph u) (actualClosedMaass_mem_graph v)

theorem actualClosedMaass_nonneg (u : actualClosedMaass.domain) :
    0 ≤ (inner ℂ (u : HyperbolicL2) (actualClosedMaass u)).re :=
  closedTensorGraph_nonneg (actualClosedMaass_mem_graph u)

theorem actualClosedMaass_shifted_coercive (u : actualClosedMaass.domain) :
    ‖(u : HyperbolicL2)‖ ^ 2 ≤
      (inner ℂ (u : HyperbolicL2) ((u : HyperbolicL2) + actualClosedMaass u)).re :=
  closedTensorGraph_shifted_coercive (actualClosedMaass_mem_graph u)

end

end ImbalancedChen.Part3.ActualMaassClosableOperator20261025a
