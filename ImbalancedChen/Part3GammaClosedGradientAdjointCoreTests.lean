import ImbalancedChen.Part3GammaActualClosedGradientCore
import ImbalancedChen.Part3Gamma0SmoothCoreFinitePoincareRepresentation

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Native adjoint-gradient graph testing on the ORIGINAL EnergyCore and on
literal finite SmoothSeed tests. Reverse implication uses the proved
actual gradient graph closure and continuity of the residual pairing;
no adjoint/form/divergence or graph-density premise is assumed.
-/
namespace ImbalancedChen.Part3.GammaClosedGradientAdjointCoreTests20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0CarrierGradientHilbertMap20261026b
open Gamma0SmoothCoreFinitePoincareRepresentation20261025a
open GammaActualClosedGradientRealization20261026b GammaActualClosedGradientCore20261026b

/-- Exact original core testing, with scalar physical and vector carrier
spaces kept distinct. The reverse pays true graph density. -/
theorem actual_gradient_adjoint_graph_iff_core_tests (N : ℕ) [NeZero N]
    (g : CarrierGradientL2 N) (w : QuotientL2 N) :
    (g,w) ∈ (actualClosedGradient N).adjoint.graph ↔
      ∀ u : EnergyCore N, inner ℂ (carrierCoreGradient N u) g = inner ℂ (physicalCore N u) w := by
  constructor
  · intro hadj u
    have hcore : (physicalCore N u,carrierCoreGradient N u) ∈ (actualClosedGradient N).graph := by
      change (physicalCore N u,carrierCoreGradient N u) ∈
        ((actualClosedGradient N).graph : Set (QuotientL2 N × CarrierGradientL2 N))
      rw [← actualClosedGradient_graph_core N]
      exact subset_closure ⟨u,rfl⟩
    rw [LinearPMap.adjoint_graph_eq_graph_adjoint (actualClosedGradient_dense_domain N)] at hadj
    have h := (Submodule.mem_adjoint_iff _ _).mp hadj _ _ hcore
    exact sub_eq_zero.mp h
  · intro hcore
    let R : QuotientL2 N × CarrierGradientL2 N → ℂ :=
      fun p => inner ℂ p.2 g - inner ℂ p.1 w
    have hsub : originalCoreGradientPairs N ⊆ {p | R p = 0} := by
      rintro p ⟨u,rfl⟩
      exact sub_eq_zero.mpr (hcore u)
    have hclosed : IsClosed {p : QuotientL2 N × CarrierGradientL2 N | R p = 0} :=
      isClosed_eq ((continuous_snd.inner continuous_const).sub (continuous_fst.inner continuous_const)) continuous_const
    have hclosure := closure_minimal hsub hclosed
    rw [actualClosedGradient_graph_core N] at hclosure
    rw [LinearPMap.adjoint_graph_eq_graph_adjoint (actualClosedGradient_dense_domain N)]
    apply (Submodule.mem_adjoint_iff _ _).mpr
    intro a b hab
    exact hclosure hab

/-- Restriction to genuine finite SmoothSeed tests is sufficient because
every original core vector has its proved finite Poincare rendering. -/
theorem actual_gradient_adjoint_graph_iff_finite_seed_tests (N : ℕ) [NeZero N]
    (g : CarrierGradientL2 N) (w : QuotientL2 N) :
    (g,w) ∈ (actualClosedGradient N).adjoint.graph ↔
      ∀ s : SmoothSeed,
        inner ℂ (carrierCoreGradient N (seedCoreElement N s : EnergyCore N)) g =
          inner ℂ (seedVector N s) w := by
  rw [actual_gradient_adjoint_graph_iff_core_tests]
  constructor
  · intro h s
    exact h (seedCoreElement N s)
  · intro h u
    obtain ⟨n,T,hT⟩ := exists_finite_poincare_representation N u
    have hu : u = (seedCoreElement N ⟨n,T⟩ : EnergyCore N) := Subtype.ext hT
    rw [hu]
    exact h ⟨n,T⟩

/-- Native adjoint-gradient domain requires a global scalar quotient L2
output for these literal finite-core pairings, not a presumed divergence. -/
theorem actual_gradient_adjoint_domain_iff_finite_output (N : ℕ) [NeZero N]
    (g : CarrierGradientL2 N) :
    g ∈ (actualClosedGradient N).adjoint.domain ↔
      ∃ w : QuotientL2 N, ∀ s : SmoothSeed,
        inner ℂ (carrierCoreGradient N (seedCoreElement N s : EnergyCore N)) g =
          inner ℂ (seedVector N s) w := by
  constructor
  · intro hg
    let u : (actualClosedGradient N).adjoint.domain := ⟨g,hg⟩
    exact ⟨(actualClosedGradient N).adjoint u,
      (actual_gradient_adjoint_graph_iff_finite_seed_tests N g _).mp (LinearPMap.mem_graph _ u)⟩
  · rintro ⟨w,hw⟩
    exact LinearPMap.mem_domain_iff.mpr
      ⟨w,(actual_gradient_adjoint_graph_iff_finite_seed_tests N g w).mpr hw⟩

end
end ImbalancedChen.Part3.GammaClosedGradientAdjointCoreTests20261026b
