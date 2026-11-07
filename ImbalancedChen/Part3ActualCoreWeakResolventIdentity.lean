import ImbalancedChen.Part3ActualCompletedTensorEnergyGreen
import ImbalancedChen.Part3ActualCompletedEnergyResolvent
import ImbalancedChen.Part3MaassFiniteCoreGraphClosure

/-!
The constructed completed-energy weak resolvent inverts the actual shifted
coordinate Maass graph on its true finite tensor domain. Continuity extends
this identity to the actual minimal differential graph closure. This is
extension inclusion, without assuming essential self-adjointness or equality
between the minimal closure and the full form-associated operator.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualCoreWeakResolventIdentity20261025a

noncomputable section

open Set
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a
open ImbalancedChen.Part3.MaassFiniteCoreGraphClosure20261025a
open ImbalancedChen.Part3.ActualCompletedTensorEnergyForm20261025a
open ImbalancedChen.Part3.ActualCompletedTensorEnergyGreen20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a

/-- Actual coordinate Green pairing supplies the concrete core weak
equation for a shifted actual differential input. -/
theorem coreEmbedding_isWeak_for_shiftedMaass (u : actualTensorDomain) :
    IsCoreTestWeakSolution ((u : HyperbolicL2) + actualTensorLaplacian u) (coreEmbedding u) :=
  fun v => coreEmbedding_inner_eq_shiftedMaass v u

theorem energyRieszSolution_shiftedMaass (u : actualTensorDomain) :
    energyRieszSolution ((u : HyperbolicL2) + actualTensorLaplacian u) = coreEmbedding u :=
  (coreTestWeakSolution_unique (coreEmbedding_isWeak_for_shiftedMaass u)).symm

/-- The genuine physical weak resolvent inverts the actual shifted
coordinate operator on every true finite tensor input. -/
theorem actualWeakResolvent_shiftedMaass (u : actualTensorDomain) :
    actualWeakResolvent ((u : HyperbolicL2) + actualTensorLaplacian u) = (u : HyperbolicL2) := by
  rw [actualWeakResolvent_apply, energyRieszSolution_shiftedMaass,
    physicalProjection_coreEmbedding]

theorem actualWeakResolvent_actualMaass (u : actualTensorDomain) :
    actualWeakResolvent (actualTensorLaplacian u) =
      (u : HyperbolicL2) - actualWeakResolvent (u : HyperbolicL2) := by
  have h := actualWeakResolvent_shiftedMaass u
  rw [map_add] at h
  apply (eq_sub_iff_add_eq).2
  simpa only [add_comm] using h

theorem actualWeakResolvent_on_actualGraph {u v : HyperbolicL2}
    (hgraph : (u, v) ∈ finiteTensorL2Graph) : actualWeakResolvent (u + v) = u := by
  let q : actualTensorDomain := ⟨u, ⟨v, hgraph⟩⟩
  have h := actualWeakResolvent_shiftedMaass q
  have hL := actualTensorLaplacian_eq_of_mem_graph q hgraph
  rw [hL] at h
  exact h

/-- The actual minimal graph closure is contained in the shifted inverse
relation of the constructed physical resolvent, proved by continuity. -/
theorem actualWeakResolvent_on_closedTensorGraph {u v : HyperbolicL2}
    (hgraph : (u, v) ∈ closedTensorGraph) : actualWeakResolvent (u + v) = u := by
  have hclosed : IsClosed {p : HyperbolicL2 × HyperbolicL2 |
      actualWeakResolvent (p.1 + p.2) = p.1} :=
    isClosed_eq (actualWeakResolvent.continuous.comp (continuous_fst.add continuous_snd))
      continuous_fst
  have hcore : finiteTensorL2Graph ⊆ {p : HyperbolicL2 × HyperbolicL2 |
      actualWeakResolvent (p.1 + p.2) = p.1} := by
    intro p hp
    exact actualWeakResolvent_on_actualGraph hp
  exact closure_minimal hcore hclosed hgraph

end

end ImbalancedChen.Part3.ActualCoreWeakResolventIdentity20261025a
