import ImbalancedChen.Part3GammaActualClosedGraphGradientEnergy

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Complex polarization identifies the FULL actual closed Dirichlet form
with the sesquilinear inner product of its represented carrier gradients.
Both imaginary and real cross terms are retained. The all-domain native
Green pairing is then a literal global carrier gradient integral.
-/

namespace ImbalancedChen.Part3.GammaActualCarrierGradientPolarization20261026b
noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a Gamma0CarrierGradientHilbertMap20261026b
open GammaActualClosedGraphGradientEnergy20261026b

/-- Genuine complex polarization of the already proved norm identity.
No mixed-pairing or global gradient identity is assumed. -/
theorem completed_carrier_gradient_inner (N : ℕ) [NeZero N]
    (d e : EnergyCompletion N) :
    inner ℂ (completedCarrierGradient N d) (completedCarrierGradient N e) =
      actualDirichletPair N d e := by
  unfold actualDirichletPair
  simp_rw [inner_eq_sum_norm_sq_div_four]
  simp only [← (completedCarrierGradient N).map_add, ← (completedCarrierGradient N).map_sub,
    ← (completedCarrierGradient N).map_smul,
    ← (physicalProjection N).map_add, ← (physicalProjection N).map_sub,
    ← (physicalProjection N).map_smul, ← Complex.ofReal_pow,
    completedCarrierGradient_norm_sq, actualDirichletPair_self_re_eq_energy_defect]
  push_cast
  ring

theorem completed_carrier_gradient_mixed_integrable (N : ℕ) [NeZero N]
    (d e : EnergyCompletion N) :
    Integrable (fun z => inner ℂ (completedCarrierGradient N d z) (completedCarrierGradient N e z))
      (carrierVolume N) := L2.integrable_inner (𝕜 := ℂ) _ _

/-- Full complex physical Green form, on the ORIGINAL canonical carrier. -/
theorem actualDirichletPair_eq_carrier_gradient_pair (N : ℕ) [NeZero N]
    (d e : EnergyCompletion N) :
    actualDirichletPair N d e =
      ∫ z, inner ℂ (completedCarrierGradient N d z) (completedCarrierGradient N e z)
        ∂carrierVolume N := by
  rw [← completed_carrier_gradient_inner N d e]
  exact L2.inner_def _ _

/-- Native all-closed-domain Green pairing with arbitrary completed
energy test, retaining the full complex output. -/
theorem actual_closed_graph_gradient_Green (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hgraph : (f,w) ∈ (actualClosedGammaMaass N).graph)
    (d : EnergyCompletion N) :
    (∫ z, inner ℂ (completedCarrierGradient N d z)
      (completedCarrierGradient N (graphEnergyLift N f w) z) ∂carrierVolume N) =
        inner ℂ (physicalProjection N d) w := by
  rw [← actualDirichletPair_eq_carrier_gradient_pair, graphEnergyLift_form_pairing N hgraph]

end
end ImbalancedChen.Part3.GammaActualCarrierGradientPolarization20261026b
