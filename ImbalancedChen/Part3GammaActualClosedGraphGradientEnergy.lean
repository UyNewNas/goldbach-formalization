import ImbalancedChen.Part3GammaActualMinimalDefectVanishes
import ImbalancedChen.Part3Gamma0CarrierGradientExhaustion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Every actual closed native graph pair has a canonical energy witness,
namely the original Riesz lift of f+w. Its represented GLOBAL carrier
gradient energy is exactly Re<f,w>, and hence bounded by ||f|| ||w||.
The completed energy norm is controlled by the actual graph norm. These
are all-domain geometric estimates, not a presumed Sobolev-domain model.
-/

namespace ImbalancedChen.Part3.GammaActualClosedGraphGradientEnergy20261026b
noncomputable section
open Set Filter MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open Gamma0ActualWeakRieszResolvent20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a Gamma0CarrierGradientHilbertMap20261026b
open Gamma0CarrierGradientExhaustion20261026b GammaActualMinimalDefectVanishes20261026b

def graphEnergyLift (N : ℕ) [NeZero N] (f w : QuotientL2 N) : EnergyCompletion N :=
  actualRieszLift N (f+w)

theorem graphEnergyLift_projection (N : ℕ) [NeZero N] {f w : QuotientL2 N}
    (hgraph : (f,w) ∈ (actualClosedGammaMaass N).graph) :
    physicalProjection N (graphEnergyLift N f w) = f := by
  rw [actual_minimal_closure_eq_friedrichs N] at hgraph
  change physicalProjection N (actualRieszLift N (f+w)) = f
  rw [← actualGammaResolvent_apply]
  exact (actualGammaFriedrichs_mem_graph_iff N).mp hgraph

/-- Exact native association, retaining arbitrary actual completed tests. -/
theorem graphEnergyLift_form_pairing (N : ℕ) [NeZero N] {f w : QuotientL2 N}
    (hgraph : (f,w) ∈ (actualClosedGammaMaass N).graph) (d : EnergyCompletion N) :
    actualDirichletPair N d (graphEnergyLift N f w) = inner ℂ (physicalProjection N d) w := by
  have h := actualRieszLift_weak N (f+w) d
  rw [actualDirichletPair, graphEnergyLift_projection N hgraph]
  change inner ℂ d (actualRieszLift N (f+w)) - inner ℂ (physicalProjection N d) f = _
  rw [h,inner_add_right]
  ring

theorem graphEnergyLift_norm_sq (N : ℕ) [NeZero N] {f w : QuotientL2 N}
    (hgraph : (f,w) ∈ (actualClosedGammaMaass N).graph) :
    ‖graphEnergyLift N f w‖^2 = ‖f‖^2 + (inner ℂ f w).re := by
  have h := congrArg Complex.re (graphEnergyLift_form_pairing N hgraph (graphEnergyLift N f w))
  rw [actualDirichletPair, graphEnergyLift_projection N hgraph, Complex.sub_re,
    ← InnerProductSpace.norm_sq_eq_re_inner, ← InnerProductSpace.norm_sq_eq_re_inner] at h
  linarith

/-- Global ACTUAL carrier gradient energy, without assuming a weak
gradient or finite Dirichlet energy for the graph-domain vector. -/
theorem actual_closed_graph_carrier_gradient_energy (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hgraph : (f,w) ∈ (actualClosedGammaMaass N).graph) :
    ‖completedCarrierGradient N (graphEnergyLift N f w)‖^2 = (inner ℂ f w).re := by
  rw [completedCarrierGradient_norm_sq, graphEnergyLift_form_pairing N hgraph,
    graphEnergyLift_projection N hgraph]

theorem actual_closed_graph_gradient_energy_bound (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hgraph : (f,w) ∈ (actualClosedGammaMaass N).graph) :
    ‖completedCarrierGradient N (graphEnergyLift N f w)‖^2 ≤ ‖f‖ * ‖w‖ := by
  rw [actual_closed_graph_carrier_gradient_energy N hgraph]
  exact re_inner_le_norm (𝕜 := ℂ) f w

theorem actual_closed_graph_carrier_gradient_integral (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hgraph : (f,w) ∈ (actualClosedGammaMaass N).graph) :
    (∫ z, ‖completedCarrierGradient N (graphEnergyLift N f w) z‖^2
      ∂Gamma0CarrierGradientHilbertMap20261026b.carrierVolume N) = (inner ℂ f w).re := by
  rw [← actualDirichletPair_eq_carrier_gradient_integral,
    graphEnergyLift_form_pairing N hgraph, graphEnergyLift_projection N hgraph]

theorem actual_closed_graph_energy_norm_le (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hgraph : (f,w) ∈ (actualClosedGammaMaass N).graph) :
    ‖graphEnergyLift N f w‖ ≤ ‖f‖ + ‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [graphEnergyLift_norm_sq N hgraph]
  have hi := re_inner_le_norm (𝕜 := ℂ) f w
  nlinarith [mul_nonneg (norm_nonneg f) (norm_nonneg w), sq_nonneg ‖w‖]

end
end ImbalancedChen.Part3.GammaActualClosedGraphGradientEnergy20261026b
