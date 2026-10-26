import ImbalancedChen.Part3GammaClosedGradientAdjointCoreTests

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A true bounded-original-core criterion for the native gradient adjoint
(divergence) domain. The bound is against the PHYSICAL quotient L2 norm,
not the energy norm. Genuine graph closure extends it to the native
gradient domain; native Riesz adjoint construction supplies the global
scalar quotient L2 output. Original quotient-core density proves its norm
bound and uniqueness. No output/form/adjoint/divergence premise is assumed.
-/
namespace ImbalancedChen.Part3.GammaGradientAdjointBoundedCore20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualMaassClosedOperator20261025a Gamma0CarrierGradientHilbertMap20261026b
open Gamma0SmoothCoreFinitePoincareRepresentation20261025a
open GammaActualClosedGradientRealization20261026b GammaActualClosedGradientCore20261026b
open GammaClosedGradientAdjointCoreTests20261026b

def BoundedCoreGradientFunctional (N : ℕ) [NeZero N] (g : CarrierGradientL2 N) (C : ℝ) : Prop :=
  ∀ u : EnergyCore N,
    ‖inner ℂ g (carrierCoreGradient N u)‖ ≤ C * ‖physicalCore N u‖

/-- Native adjoint outputs are unique; no independent weak-divergence
uniqueness or vector covariance is supplied as a premise. -/
theorem gradient_adjoint_output_unique (N : ℕ) [NeZero N]
    {g : CarrierGradientL2 N} {w₁ w₂ : QuotientL2 N}
    (h₁ : (g,w₁) ∈ (actualClosedGradient N).adjoint.graph)
    (h₂ : (g,w₂) ∈ (actualClosedGradient N).adjoint.graph) : w₁ = w₂ := by
  obtain ⟨u₁,hu₁,hAu₁⟩ := LinearPMap.mem_graph_iff.mp h₁
  obtain ⟨u₂,hu₂,hAu₂⟩ := LinearPMap.mem_graph_iff.mp h₂
  have hueq : u₁ = u₂ := Subtype.ext (hu₁.trans hu₂.symm)
  exact hAu₁.symm.trans ((congrArg (actualClosedGradient N).adjoint hueq).trans hAu₂)

/-- A physical-norm bound on ORIGINAL finite smooth core vectors
constructs an actual native adjoint output, with derived norm bound. -/
theorem bounded_core_functional_has_adjoint_output (N : ℕ) [NeZero N]
    (g : CarrierGradientL2 N) (C : ℝ) (hC : 0 ≤ C)
    (hbound : BoundedCoreGradientFunctional N g C) :
    ∃ w : QuotientL2 N,
      (g,w) ∈ (actualClosedGradient N).adjoint.graph ∧ ‖w‖ ≤ C ∧
      ∀ w' : QuotientL2 N, (g,w') ∈ (actualClosedGradient N).adjoint.graph → w' = w := by
  have hsub : originalCoreGradientPairs N ⊆
      {p : QuotientL2 N × CarrierGradientL2 N | ‖inner ℂ g p.2‖ ≤ C * ‖p.1‖} := by
    rintro p ⟨u,rfl⟩
    exact hbound u
  have hclosed : IsClosed
      {p : QuotientL2 N × CarrierGradientL2 N | ‖inner ℂ g p.2‖ ≤ C * ‖p.1‖} :=
    isClosed_le (continuous_const.inner continuous_snd).norm (continuous_const.mul continuous_fst.norm)
  have hgraphbound := closure_minimal hsub hclosed
  rw [actualClosedGradient_graph_core N] at hgraphbound
  let L : (actualClosedGradient N).domain →ₗ[ℂ] ℂ :=
    (innerₛₗ ℂ g).comp (actualClosedGradient N).toFun
  have hL : ∀ u : (actualClosedGradient N).domain, ‖L u‖ ≤ C * ‖u‖ := by
    intro u
    exact hgraphbound (LinearPMap.mem_graph _ u)
  let LC := L.mkContinuous C hL
  have hdom : g ∈ (actualClosedGradient N).adjoint.domain :=
    (LinearPMap.mem_adjoint_domain_iff (actualClosedGradient N) g).mpr LC.continuous
  let y : (actualClosedGradient N).adjoint.domain := ⟨g,hdom⟩
  let w : QuotientL2 N := (actualClosedGradient N).adjoint y
  have hgw : (g,w) ∈ (actualClosedGradient N).adjoint.graph := LinearPMap.mem_graph _ y
  have hpair := (actual_gradient_adjoint_graph_iff_core_tests N g w).mp hgw
  have hscalar : (smoothCore N : Set (QuotientL2 N)) ⊆
      {x : QuotientL2 N | ‖inner ℂ w x‖ ≤ C * ‖x‖} := by
    intro x hx
    let u : EnergyCore N := ⟨x,hx⟩
    have heq : inner ℂ g (carrierCoreGradient N u) = inner ℂ w (physicalCore N u) := by
      simpa only [inner_conj_symm] using congrArg star (hpair u)
    change ‖inner ℂ w (physicalCore N u)‖ ≤ C * ‖physicalCore N u‖
    rw [← heq]
    exact hbound u
  have hscalarclosed : IsClosed {x : QuotientL2 N | ‖inner ℂ w x‖ ≤ C * ‖x‖} :=
    isClosed_le (continuous_const.inner continuous_id).norm (continuous_const.mul continuous_id.norm)
  have hall (x : QuotientL2 N) : ‖inner ℂ w x‖ ≤ C * ‖x‖ :=
    closure_minimal hscalar hscalarclosed ((actual_smoothCore_dense N) x)
  have hww := hall w
  rw [inner_self_eq_norm_sq_to_K,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg w)] at hww
  have hn : ‖w‖ ≤ C := by
    by_cases hz : ‖w‖ = 0
    · rw [hz]
      exact hC
    · have hp : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      exact (mul_le_mul_right hp).mp (by simpa only [pow_two] using hww)
  exact ⟨w,hgw,hn,fun w' hw' => gradient_adjoint_output_unique N hw' hgw⟩

/-- Exact native adjoint domain characterization. Only a scalar physical
L2 bound on the original core functional is required in the reverse. -/
theorem actual_gradient_adjoint_domain_iff_bounded_core (N : ℕ) [NeZero N]
    (g : CarrierGradientL2 N) :
    g ∈ (actualClosedGradient N).adjoint.domain ↔
      ∃ C : ℝ, 0 ≤ C ∧ BoundedCoreGradientFunctional N g C := by
  constructor
  · intro hg
    let y : (actualClosedGradient N).adjoint.domain := ⟨g,hg⟩
    let w := (actualClosedGradient N).adjoint y
    have hp := (actual_gradient_adjoint_graph_iff_core_tests N g w).mp (LinearPMap.mem_graph _ y)
    refine ⟨‖w‖,norm_nonneg _,fun u => ?_⟩
    rw [norm_inner_symm,hp u]
    exact (norm_inner_le_norm (physicalCore N u) w).trans_eq (mul_comm _ _)
  · rintro ⟨C,hC,hbound⟩
    obtain ⟨w,hgraph,hn,hunique⟩ := bounded_core_functional_has_adjoint_output N g C hC hbound
    exact LinearPMap.mem_domain_iff.mpr ⟨w,hgraph⟩

/-- The bounded-functional criterion can be checked on the literal
original finite SmoothSeed ABI, with the physical SEED VECTOR norm. -/
theorem actual_gradient_adjoint_domain_iff_bounded_finite_tests (N : ℕ) [NeZero N]
    (g : CarrierGradientL2 N) :
    g ∈ (actualClosedGradient N).adjoint.domain ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s : SmoothSeed,
        ‖inner ℂ g (carrierCoreGradient N (seedCoreElement N s : EnergyCore N))‖ ≤ C * ‖seedVector N s‖ := by
  rw [actual_gradient_adjoint_domain_iff_bounded_core]
  constructor
  · rintro ⟨C,hC,hbound⟩
    exact ⟨C,hC,fun s => hbound (seedCoreElement N s)⟩
  · rintro ⟨C,hC,hbound⟩
    refine ⟨C,hC,fun u => ?_⟩
    obtain ⟨n,T,hT⟩ := exists_finite_poincare_representation N u
    have hu : u = (seedCoreElement N ⟨n,T⟩ : EnergyCore N) := Subtype.ext hT
    rw [hu]
    exact hbound ⟨n,T⟩

end
end ImbalancedChen.Part3.GammaGradientAdjointBoundedCore20261026b
