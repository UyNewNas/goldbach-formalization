import ImbalancedChen.Part3ActualHeckeCompactSeedNativeGraph
import ImbalancedChen.Part3Gamma0PoincarePairingUnfolding
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The ORIGINAL actual compact smooth seedPair generators are sent by the
actual physical bounded Hecke pair map into the native minimal closed
Maass graph. Original coreGraph=span(range seedPair) pays finite span.
The exact actualClosedGammaMaass.graph=(coreGraph).topologicalClosure
and continuity of the ACTUAL bounded physical Hecke pair map pay closure.
Thus the full native minimal closed domain is invariant and A Tp=Tp A
there, with an actual linear map on that native domain. No core/domain
commutation, core density, graph invariance or output identity is assumed.
Friedrichs identification is a separate proved supplier/consumer.
-/

namespace ImbalancedChen.Part3.ActualHeckeMinimalClosedGraph20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ActualBoundedPhysicalHecke20261026b ActualHeckeCompactSeedNativeGraph20261026b
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualMaassClosedOperator20261025a GammaCompactSeedGraphTransport20261026a
open Gamma0CompactTensorPoincareLocalFinite20261025a Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0SmoothCompactTensorCore20261025a Gamma0PoincarePairingUnfolding20261025a
open MaassWeakOperatorCore20261024zz Gamma0QuotientCellPushforward20261025a

variable (N p : ℕ) [NeZero N] [NeZero (N*p)]
  (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)

def physicalHeckePairMap : (QuotientL2 N × QuotientL2 N) →L[ℂ] (QuotientL2 N × QuotientL2 N) :=
  (physicalHeckeOperator N p hN hp hpN).prodMap (physicalHeckeOperator N p hN hp hpN)

/-- Original finite smooth tensor generators, identified with the actual
compact seed definitions before using the paid compact native graph bridge. -/
theorem physicalHecke_seedPair_mem_closedGraph (s : SmoothSeed) :
    physicalHeckePairMap N p hN hp hpN (seedPair N s) ∈ closedGammaGraph N := by
  rcases s with ⟨n,T⟩
  let f : UpperHalfPlane → ℂ := finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor)
  have hfc : HasCompactSupport f := finiteCoreFunction_hasCompactSupport Finset.univ _
  have hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart := by
    dsimp only [f]
    rw [extendUpper_finiteCoreFunction]
    exact (finiteSmoothChart_contDiff Finset.univ T).contDiffOn
  have hpair := physicalHecke_compactInput_graph N p hN hp hpN f hfc hf
  rw [compactInput_finiteTensor_eq N T (tsupport f) hfc (subset_tsupport f),
    compactOutput_finiteTensor_eq N T (tsupport f) hfc (subset_tsupport f),
    actualClosedGammaMaass_graph_eq] at hpair
  exact hpair

/-- The EXISTING original seed span is handled by actual linearity.
The transformed seed need not belong to the algebraic tensor span. -/
theorem physicalHecke_coreGraph_mem_closedGraph {q : QuotientL2 N × QuotientL2 N}
    (hq : q ∈ coreGraph N) : physicalHeckePairMap N p hN hp hpN q ∈ closedGammaGraph N := by
  have hle : coreGraph N ≤ (closedGammaGraph N).comap (physicalHeckePairMap N p hN hp hpN).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro q ⟨s,rfl⟩
    exact physicalHecke_seedPair_mem_closedGraph N p hN hp hpN s
  exact hle hq

/-- Full actual closed graph invariance, derived from the ORIGINAL graph
closure supplier and continuity of the genuine bounded physical pair map. -/
theorem physicalHecke_minimal_graph_stable {q : QuotientL2 N × QuotientL2 N}
    (hq : q ∈ (actualClosedGammaMaass N).graph) :
    physicalHeckePairMap N p hN hp hpN q ∈ (actualClosedGammaMaass N).graph := by
  have hcore : (coreGraph N : Set (QuotientL2 N × QuotientL2 N)) ⊆
      physicalHeckePairMap N p hN hp hpN ⁻¹' (closedGammaGraph N : Set _) :=
    fun r hr => physicalHecke_coreGraph_mem_closedGraph N p hN hp hpN hr
  have hpre : IsClosed (physicalHeckePairMap N p hN hp hpN ⁻¹' (closedGammaGraph N : Set _)) :=
    (closedGammaGraph_isClosed N).preimage (physicalHeckePairMap N p hN hp hpN).continuous
  have hclosure := closure_minimal hcore hpre
  rw [actualClosedGammaMaass_graph_eq] at hq ⊢
  exact hclosure hq

theorem physicalHecke_mem_minimal_domain (u : (actualClosedGammaMaass N).domain) :
    physicalHeckeOperator N p hN hp hpN (u : QuotientL2 N) ∈ (actualClosedGammaMaass N).domain := by
  have hgraph := physicalHecke_minimal_graph_stable N p hN hp hpN (LinearPMap.mem_graph (actualClosedGammaMaass N) u)
  obtain ⟨w,hw,_⟩ := LinearPMap.mem_graph_iff.mp hgraph
  rw [← hw]
  exact w.property

/-- Actual linear restriction of physical Tp to the proved invariant
native minimal closed operator domain. -/
def minimalHeckeDomainMap : (actualClosedGammaMaass N).domain →ₗ[ℂ] (actualClosedGammaMaass N).domain where
  toFun u := ⟨physicalHeckeOperator N p hN hp hpN u,physicalHecke_mem_minimal_domain N p hN hp hpN u⟩
  map_add' u v := by
    apply Subtype.ext
    exact (physicalHeckeOperator N p hN hp hpN).map_add u v
  map_smul' c u := by
    apply Subtype.ext
    exact (physicalHeckeOperator N p hN hp hpN).map_smul c u

theorem minimalHeckeDomainMap_coe (u : (actualClosedGammaMaass N).domain) :
    (minimalHeckeDomainMap N p hN hp hpN u : QuotientL2 N) = physicalHeckeOperator N p hN hp hpN u := rfl

/-- Exact ACTUAL native closed-Maass commutation on its ENTIRE domain. -/
theorem actualClosedMaass_physicalHecke_commute (u : (actualClosedGammaMaass N).domain) :
    actualClosedGammaMaass N (minimalHeckeDomainMap N p hN hp hpN u) =
      physicalHeckeOperator N p hN hp hpN (actualClosedGammaMaass N u) := by
  have hgraph := physicalHecke_minimal_graph_stable N p hN hp hpN (LinearPMap.mem_graph (actualClosedGammaMaass N) u)
  obtain ⟨w,hw,hAw⟩ := LinearPMap.mem_graph_iff.mp hgraph
  have hw' : w=minimalHeckeDomainMap N p hN hp hpN u := Subtype.ext hw
  simpa only [hw'] using hAw

end
end ImbalancedChen.Part3.ActualHeckeMinimalClosedGraph20261026b

