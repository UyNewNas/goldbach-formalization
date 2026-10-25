import ImbalancedChen.Part3Gamma0ActualSmoothCoreSymmetry
import ImbalancedChen.Part3Gamma0SmoothQuotientCoreDensity
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

The actual Gamma0 quotient Maass operator on the existing actual smooth
quotient core is closable. Its graph closure is an actual closed, densely
defined, symmetric partial complex linear map in the canonical quotient L2.
The proof uses the genuine all-core quotient Green identity and the genuine
compact-seed quotient density theorem. Neither density nor symmetry is an
input assumption. The operator and its graph are the existing actual
quotient input/output objects, not a whole-plane operator transported by name.

No nonnegative energy, self-adjointness or resolvent conclusion is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0ActualMaassClosedOperator20261025a

noncomputable section
open Set Filter MeasureTheory
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothCoreSymmetry20261025a
open ImbalancedChen.Part3.Gamma0SmoothQuotientCoreDensity20261025a

/-- Actual compact smooth Poincare inputs are dense in the already typed
actual quotient input core. This is a consequence of the supplied genuine
family approximation, not a density premise. -/
theorem actual_smoothCore_dense (N : ℕ) [NeZero N] :
    Dense (smoothCore N : Set (QuotientL2 N)) := by
  apply (smoothQuotientCore_dense N).mono
  intro v hv
  obtain ⟨n,T,rfl⟩ := hv
  exact Submodule.subset_span ⟨⟨n,T⟩,rfl⟩

/-- Partial operator with exactly the original smooth quotient core and
the previously constructed actual quotient-L2 differential output. -/
def actualPartialGammaMaass (N : ℕ) [NeZero N] :
    QuotientL2 N →ₗ.[ℂ] QuotientL2 N where
  domain := smoothCore N
  toFun := actualCoreLaplacian N

theorem actualPartialGammaMaass_graph_eq (N : ℕ) [NeZero N] :
    (actualPartialGammaMaass N).graph = coreGraph N := by
  apply SetLike.ext
  intro p
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨u,hu,hv⟩
    have hp := graphOutput_mem N u
    change ((u : QuotientL2 N),actualCoreLaplacian N u) ∈ coreGraph N at hp
    rw [hu,hv] at hp
    exact hp
  · intro hp
    have hu : p.1 ∈ smoothCore N := (coreGraph_domain_iff N p.1).mp ⟨p.2,hp⟩
    let u : smoothCore N := ⟨p.1,hu⟩
    have hv : p.2 = actualCoreLaplacian N u :=
      (coreGraph_iff_operator N u p.2).mp hp
    exact ⟨u,rfl,hv.symm⟩

theorem actualPartialGammaMaass_dense_domain (N : ℕ) [NeZero N] :
    Dense ((actualPartialGammaMaass N).domain : Set (QuotientL2 N)) :=
  actual_smoothCore_dense N

/-- The actual graph relation inherits the genuine all-core Green identity. -/
theorem actual_coreGraph_symmetric (N : ℕ) [NeZero N]
    {f g u v : QuotientL2 N} (hfg : (f,g) ∈ coreGraph N)
    (huv : (u,v) ∈ coreGraph N) : inner ℂ g u = inner ℂ f v := by
  have hf : f ∈ smoothCore N := (coreGraph_domain_iff N f).mp ⟨g,hfg⟩
  have hu : u ∈ smoothCore N := (coreGraph_domain_iff N u).mp ⟨v,huv⟩
  have hg := (coreGraph_iff_operator N ⟨f,hf⟩ g).mp hfg
  have hv := (coreGraph_iff_operator N ⟨u,hu⟩ v).mp huv
  rw [hg,hv]
  exact actualCoreLaplacian_symmetric N ⟨f,hf⟩ ⟨u,hu⟩

/-- Topological closure of the ACTUAL quotient input/output graph. -/
def closedGammaGraph (N : ℕ) [NeZero N] :
    Submodule ℂ (QuotientL2 N × QuotientL2 N) :=
  (coreGraph N).topologicalClosure

theorem closedGammaGraph_isClosed (N : ℕ) [NeZero N] :
    IsClosed (closedGammaGraph N : Set (QuotientL2 N × QuotientL2 N)) :=
  (coreGraph N).isClosed_topologicalClosure

theorem actualPartialGammaMaass_closureGraph_eq (N : ℕ) [NeZero N] :
    (actualPartialGammaMaass N).graph.topologicalClosure = closedGammaGraph N := by
  rw [actualPartialGammaMaass_graph_eq]
  rfl

/-- First close one graph variable against an actual smooth compact-seed
core test. The equality set is closed by continuity of the Hilbert pairing. -/
theorem closedGammaGraph_core_weak_pairing (N : ℕ) [NeZero N]
    {f g u v : QuotientL2 N} (hfg : (f,g) ∈ closedGammaGraph N)
    (huv : (u,v) ∈ coreGraph N) : inner ℂ g u = inner ℂ f v := by
  have hclosed : IsClosed {p : QuotientL2 N × QuotientL2 N |
      inner ℂ p.2 u = inner ℂ p.1 v} :=
    isClosed_eq (continuous_snd.inner continuous_const)
      (continuous_fst.inner continuous_const)
  have hsub : (coreGraph N : Set (QuotientL2 N × QuotientL2 N)) ⊆
      {p | inner ℂ p.2 u = inner ℂ p.1 v} := by
    intro p hp
    exact actual_coreGraph_symmetric N hp huv
  exact (closure_minimal hsub hclosed) hfg

/-- Closing the second variable proves actual graph-closure symmetry. -/
theorem closedGammaGraph_symmetric (N : ℕ) [NeZero N]
    {f g u v : QuotientL2 N} (hfg : (f,g) ∈ closedGammaGraph N)
    (huv : (u,v) ∈ closedGammaGraph N) : inner ℂ g u = inner ℂ f v := by
  have hclosed : IsClosed {p : QuotientL2 N × QuotientL2 N |
      inner ℂ g p.1 = inner ℂ f p.2} :=
    isClosed_eq (continuous_const.inner continuous_fst)
      (continuous_const.inner continuous_snd)
  have hsub : (coreGraph N : Set (QuotientL2 N × QuotientL2 N)) ⊆
      {p | inner ℂ g p.1 = inner ℂ f p.2} := by
    intro p hp
    exact closedGammaGraph_core_weak_pairing N hfg hp
  exact (closure_minimal hsub hclosed) huv

theorem closedGammaGraph_zero_input_annihilates_core (N : ℕ) [NeZero N]
    {g : QuotientL2 N} (hg : ((0 : QuotientL2 N),g) ∈ closedGammaGraph N)
    (u : smoothCore N) : inner ℂ g (u : QuotientL2 N) = 0 := by
  simpa only [inner_zero_left] using
    closedGammaGraph_core_weak_pairing N hg (graphOutput_mem N u)

/-- Genuine quotient-core density removes every vertical limit fiber. -/
theorem closedGammaGraph_vertical_trivial (N : ℕ) [NeZero N]
    (p : QuotientL2 N × QuotientL2 N) (hp : p ∈ closedGammaGraph N)
    (hzero : p.1 = 0) : p.2 = 0 := by
  have hp0 : ((0 : QuotientL2 N),p.2) ∈ closedGammaGraph N := by
    rw [← hzero]
    exact hp
  apply (actual_smoothCore_dense N).eq_zero_of_inner_left ℂ
  intro u hu
  exact closedGammaGraph_zero_input_annihilates_core N hp0 ⟨u,hu⟩

theorem closedGammaGraph_right_unique (N : ℕ) [NeZero N]
    {f g h : QuotientL2 N} (hfg : (f,g) ∈ closedGammaGraph N)
    (hfh : (f,h) ∈ closedGammaGraph N) : g = h := by
  have hdiff : ((0 : QuotientL2 N),g-h) ∈ closedGammaGraph N := by
    have hsub := (closedGammaGraph N).sub_mem hfg hfh
    change (f-f,g-h) ∈ closedGammaGraph N at hsub
    simpa only [sub_self] using hsub
  exact sub_eq_zero.mp (closedGammaGraph_vertical_trivial N (0,g-h) hdiff rfl)

theorem actualPartialGammaMaass_isClosable (N : ℕ) [NeZero N] :
    (actualPartialGammaMaass N).IsClosable := by
  refine ⟨(closedGammaGraph N).toLinearPMap,?_⟩
  rw [actualPartialGammaMaass_closureGraph_eq]
  exact ((closedGammaGraph N).toLinearPMap_graph_eq
    (closedGammaGraph_vertical_trivial N)).symm

/-- Native closure of the actual quotient smooth-core Maass operator. -/
def actualClosedGammaMaass (N : ℕ) [NeZero N] :
    QuotientL2 N →ₗ.[ℂ] QuotientL2 N := (actualPartialGammaMaass N).closure

theorem actualClosedGammaMaass_graph_eq (N : ℕ) [NeZero N] :
    (actualClosedGammaMaass N).graph = closedGammaGraph N := by
  calc
    _ = (actualPartialGammaMaass N).graph.topologicalClosure :=
      (actualPartialGammaMaass_isClosable N).graph_closure_eq_closure_graph.symm
    _ = _ := actualPartialGammaMaass_closureGraph_eq N

theorem actualClosedGammaMaass_isClosed (N : ℕ) [NeZero N] :
    (actualClosedGammaMaass N).IsClosed :=
  (actualPartialGammaMaass_isClosable N).closure_isClosed

theorem actualClosedGammaMaass_extends (N : ℕ) [NeZero N] :
    actualPartialGammaMaass N ≤ actualClosedGammaMaass N :=
  (actualPartialGammaMaass N).le_closure

theorem actualClosedGammaMaass_dense_domain (N : ℕ) [NeZero N] :
    Dense ((actualClosedGammaMaass N).domain : Set (QuotientL2 N)) :=
  (actual_smoothCore_dense N).mono (actualClosedGammaMaass_extends N).1

theorem actualClosedGammaMaass_mem_graph (N : ℕ) [NeZero N]
    (u : (actualClosedGammaMaass N).domain) :
    ((u : QuotientL2 N),actualClosedGammaMaass N u) ∈ closedGammaGraph N := by
  rw [← actualClosedGammaMaass_graph_eq]
  exact LinearPMap.mem_graph_iff.mpr ⟨u,rfl,rfl⟩

theorem actualClosedGammaMaass_symmetric (N : ℕ) [NeZero N]
    (u v : (actualClosedGammaMaass N).domain) :
    inner ℂ (actualClosedGammaMaass N u) (v : QuotientL2 N) =
      inner ℂ (u : QuotientL2 N) (actualClosedGammaMaass N v) :=
  closedGammaGraph_symmetric N (actualClosedGammaMaass_mem_graph N u)
    (actualClosedGammaMaass_mem_graph N v)

end
end ImbalancedChen.Part3.Gamma0ActualMaassClosedOperator20261025a
