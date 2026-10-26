import ImbalancedChen.Part3GammaActualClosedGradientRealization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Native first-order factorization of the actual minimal Maass closure.
The exact square-domain condition is retained: f belongs to the original
closed-gradient domain and its gradient belongs to the NATIVE adjoint
gradient domain, with actual adjoint output w. This is proved equivalent
to the original Maass graph; no formal G*G identity/domain is presumed.
-/

namespace ImbalancedChen.Part3.GammaActualMaassGradientFactorization20261026b
noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a Gamma0CarrierGradientHilbertMap20261026b
open GammaActualMinimalDefectVanishes20261026b GammaActualCarrierGradientPolarization20261026b
open GammaActualClosedGradientRealization20261026b

/-- Honest native G†G graph with its full domain restriction. -/
theorem actual_Maass_graph_iff_gradient_adjoint_graph (N : ℕ) [NeZero N]
    (f w : QuotientL2 N) :
    (f,w) ∈ (actualClosedGammaMaass N).graph ↔
      ∃ u : (actualClosedGradient N).domain,
        (u : QuotientL2 N) = f ∧
          (actualClosedGradient N u,w) ∈ (actualClosedGradient N).adjoint.graph := by
  constructor
  · intro hgraph
    rw [actual_minimal_closure_eq_friedrichs N] at hgraph
    obtain ⟨e,he,hpair⟩ := (actualGammaFriedrichs_mem_graph_iff_formPair N).mp hgraph
    let u : actualEnergyFormDomain N := ⟨f,⟨e,he⟩⟩
    have heq : actualEnergyLift N u = e := by
      apply physicalProjection_injective N
      exact (actualEnergyLift_projection N u).trans he.symm
    refine ⟨u,rfl,?_⟩
    rw [LinearPMap.adjoint_graph_eq_graph_adjoint (actualClosedGradient_dense_domain N),
      Submodule.mem_adjoint_iff]
    intro a b hab
    obtain ⟨v,hv,hGv⟩ := LinearPMap.mem_graph_iff.mp hab
    rw [← hv, ← hGv]
    change inner ℂ (completedCarrierGradient N (actualEnergyLift N v))
      (completedCarrierGradient N (actualEnergyLift N u)) - inner ℂ (v : QuotientL2 N) w = 0
    rw [heq, completed_carrier_gradient_inner, hpair, actualEnergyLift_projection, sub_self]
  · rintro ⟨u,hu,hadj⟩
    let e := actualEnergyLift N u
    have he : physicalProjection N e = f := (actualEnergyLift_projection N u).trans hu
    rw [LinearPMap.adjoint_graph_eq_graph_adjoint (actualClosedGradient_dense_domain N),
      Submodule.mem_adjoint_iff] at hadj
    have hpair : ∀ d : EnergyCompletion N,
        actualDirichletPair N d e = inner ℂ (physicalProjection N d) w := by
      intro d
      let v : actualEnergyFormDomain N := ⟨physicalProjection N d,⟨d,rfl⟩⟩
      have hd : actualEnergyLift N v = d := by
        apply physicalProjection_injective N
        exact actualEnergyLift_projection N v
      have h := hadj (v : QuotientL2 N) (actualClosedGradient N v)
        (LinearPMap.mem_graph _ v)
      change inner ℂ (completedCarrierGradient N (actualEnergyLift N v))
        (completedCarrierGradient N (actualEnergyLift N u)) -
          inner ℂ (physicalProjection N d) w = 0 at h
      rw [hd,completed_carrier_gradient_inner] at h
      exact sub_eq_zero.mp h
    rw [actual_minimal_closure_eq_friedrichs N]
    exact (actualGammaFriedrichs_mem_graph_iff_formPair N).mpr ⟨e,he,hpair⟩

/-- Native square-domain characterization; existence of a global quotient
output is required and is not confused with merely local weak H1 data. -/
theorem actual_Maass_domain_iff_gradient_adjoint_domain (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    f ∈ (actualClosedGammaMaass N).domain ↔
      ∃ u : (actualClosedGradient N).domain,
        (u : QuotientL2 N) = f ∧ actualClosedGradient N u ∈ (actualClosedGradient N).adjoint.domain := by
  constructor
  · intro hf
    let v : (actualClosedGammaMaass N).domain := ⟨f,hf⟩
    obtain ⟨u,hu,hgraph⟩ := (actual_Maass_graph_iff_gradient_adjoint_graph N f
      (actualClosedGammaMaass N v)).mp (LinearPMap.mem_graph _ v)
    exact ⟨u,hu,(LinearPMap.mem_domain_iff).mpr ⟨_,hgraph⟩⟩
  · rintro ⟨u,hu,hG⟩
    let v : (actualClosedGradient N).adjoint.domain := ⟨actualClosedGradient N u,hG⟩
    exact (LinearPMap.mem_domain_iff).mpr ⟨(actualClosedGradient N).adjoint v,
      (actual_Maass_graph_iff_gradient_adjoint_graph N f _).mpr
        ⟨u,hu,LinearPMap.mem_graph _ v⟩⟩

end
end ImbalancedChen.Part3.GammaActualMaassGradientFactorization20261026b
