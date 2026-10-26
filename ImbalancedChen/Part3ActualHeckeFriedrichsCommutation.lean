import ImbalancedChen.Part3ActualHeckeMinimalClosedGraph
import ImbalancedChen.Part3GammaActualMinimalDefectVanishes

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The actual bounded ORIGINAL physical prime Hecke preserves the ENTIRE
native ACTUAL Friedrichs domain and commutes with its native Maass action.
The original-core closed-graph proof is consumed together with the exact
independently proved actual minimal-closure=Friedrichs identity (d3bb5e).
The actual physical shifted-energy resolvent consequently commutes too,
using its genuine graph equation R(u+Au)=u. No commutation/domain/core or
abstract operator-identification premise is supplied; no private carrier
comparison API or Hecke selfadjointness assertion is used.
-/

namespace ImbalancedChen.Part3.ActualHeckeFriedrichsCommutation20261026b
noncomputable section
open MeasureTheory
open ActualBoundedPhysicalHecke20261026b ActualHeckeMinimalClosedGraph20261026b
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open Gamma0ActualFriedrichsOperator20261025a GammaActualMinimalDefectVanishes20261026b
open Gamma0ActualWeakRieszResolvent20261025a

variable (N p : ℕ) [NeZero N] [NeZero (N*p)]
  (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)

/-- Entire actual Friedrichs graph preservation, with the exact ORIGINAL
geometric operator identity already proved by the defect-vanishing chain. -/
theorem physicalHecke_friedrichs_graph_stable {q : QuotientL2 N × QuotientL2 N}
    (hq : q ∈ (actualGammaFriedrichs N).graph) :
    physicalHeckePairMap N p hN hp hpN q ∈ (actualGammaFriedrichs N).graph := by
  rw [← actual_minimal_closure_eq_friedrichs N] at hq ⊢
  exact physicalHecke_minimal_graph_stable N p hN hp hpN hq

theorem physicalHecke_mem_friedrichs_domain (u : (actualGammaFriedrichs N).domain) :
    physicalHeckeOperator N p hN hp hpN (u : QuotientL2 N) ∈ (actualGammaFriedrichs N).domain := by
  have hgraph := physicalHecke_friedrichs_graph_stable N p hN hp hpN
    (LinearPMap.mem_graph (actualGammaFriedrichs N) u)
  obtain ⟨w,hw,_⟩ := LinearPMap.mem_graph_iff.mp hgraph
  rw [← hw]
  exact w.property

/-- Concrete linear restriction of the SAME physical bounded Tp to the
proved invariant full native Friedrichs domain. -/
def friedrichsHeckeDomainMap : (actualGammaFriedrichs N).domain →ₗ[ℂ] (actualGammaFriedrichs N).domain where
  toFun u := ⟨physicalHeckeOperator N p hN hp hpN u,physicalHecke_mem_friedrichs_domain N p hN hp hpN u⟩
  map_add' u v := by
    apply Subtype.ext
    exact (physicalHeckeOperator N p hN hp hpN).map_add u v
  map_smul' c u := by
    apply Subtype.ext
    exact (physicalHeckeOperator N p hN hp hpN).map_smul c u

theorem friedrichsHeckeDomainMap_coe (u : (actualGammaFriedrichs N).domain) :
    (friedrichsHeckeDomainMap N p hN hp hpN u : QuotientL2 N) =
      physicalHeckeOperator N p hN hp hpN u := rfl

/-- EXACT A Tp=Tp A for EVERY vector of the ACTUAL Friedrichs domain. -/
theorem actualFriedrichs_physicalHecke_commute (u : (actualGammaFriedrichs N).domain) :
    actualGammaFriedrichs N (friedrichsHeckeDomainMap N p hN hp hpN u) =
      physicalHeckeOperator N p hN hp hpN (actualGammaFriedrichs N u) := by
  have hgraph := physicalHecke_friedrichs_graph_stable N p hN hp hpN
    (LinearPMap.mem_graph (actualGammaFriedrichs N) u)
  obtain ⟨w,hw,hAw⟩ := LinearPMap.mem_graph_iff.mp hgraph
  have hw' : w=friedrichsHeckeDomainMap N p hN hp hpN u := Subtype.ext hw
  simpa only [hw'] using hAw

/-- Genuine physical energy resolvent commutation on ALL quotient L2
vectors follows from actual graph invariance and the exact graph equation. -/
theorem actualResolvent_physicalHecke_commute (f : QuotientL2 N) :
    actualGammaResolvent N (physicalHeckeOperator N p hN hp hpN f) =
      physicalHeckeOperator N p hN hp hpN (actualGammaResolvent N f) := by
  have hgraph : (actualGammaResolvent N f,f-actualGammaResolvent N f) ∈
      (actualGammaFriedrichs N).graph := by
    apply (actualGammaFriedrichs_mem_graph_iff N).mpr
    have hadd : actualGammaResolvent N f+(f-actualGammaResolvent N f)=f := by abel
    rw [hadd]
  have hTgraph := physicalHecke_friedrichs_graph_stable N p hN hp hpN hgraph
  have hshift := (actualGammaFriedrichs_mem_graph_iff N).mp hTgraph
  change actualGammaResolvent N
    (physicalHeckeOperator N p hN hp hpN (actualGammaResolvent N f)+
      physicalHeckeOperator N p hN hp hpN (f-actualGammaResolvent N f)) =
        physicalHeckeOperator N p hN hp hpN (actualGammaResolvent N f) at hshift
  have hinput : physicalHeckeOperator N p hN hp hpN (actualGammaResolvent N f)+
      physicalHeckeOperator N p hN hp hpN (f-actualGammaResolvent N f) =
        physicalHeckeOperator N p hN hp hpN f := by
    rw [(physicalHeckeOperator N p hN hp hpN).map_sub]
    abel
  rw [hinput] at hshift
  exact hshift

end
end ImbalancedChen.Part3.ActualHeckeFriedrichsCommutation20261026b

