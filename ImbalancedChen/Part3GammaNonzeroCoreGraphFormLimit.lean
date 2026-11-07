import ImbalancedChen.Part3GammaCoreGraphEnergyLimit
import ImbalancedChen.Part3Gamma0CarrierGradientHilbertMap

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The preceding actual graph-to-form lemma handled zero differential output.
Compact smooth multiplier seeds generally have NONZERO output. This leaf
proves their required general limit primitive: actual finite-core graph
convergence gives genuine energy-completion convergence, the canonical
closed-form pair, and strong convergence of the global carrier gradient.
No form convergence, form-domain membership or gradient limit is assumed.
-/

namespace ImbalancedChen.Part3.GammaNonzeroCoreGraphFormLimit20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualMaassClosedOperator20261025a Gamma0ActualMinimalFriedrichsInclusion20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a GammaCoreGraphEnergyLimit20261026a
open Gamma0CarrierGradientHilbertMap20261026b

/-- General actual graph convergence, including a nonzero native output.
The original finite smooth core supplies energy Cauchy control; actual
closed graph membership supplies the true completed form association. -/
theorem exists_energy_limit_of_core_graph
    (N : ℕ) [NeZero N] (u : ℕ → EnergyCore N) (f g : QuotientL2 N)
    (hp : Tendsto (fun n => physicalCore N (u n)) atTop (𝓝 f))
    (hL : Tendsto (fun n => coreLaplacian N (u n)) atTop (𝓝 g)) :
    ∃ e : EnergyCompletion N,
      Tendsto (fun n => coreEmbedding N (u n)) atTop (𝓝 e) ∧
      physicalProjection N e = f ∧
      (∀ d : EnergyCompletion N, actualDirichletPair N d e =
        inner ℂ (physicalProjection N d) g) ∧
      actualDirichletPair N e e = inner ℂ f g ∧
      (f,g) ∈ (actualGammaFriedrichs N).graph := by
  obtain ⟨e,he⟩ := cauchySeq_tendsto_of_complete
    (energy_cauchySeq_of_graph_cauchySeq N u hp.cauchySeq hL.cauchySeq)
  have hproj : physicalProjection N e = f := by
    apply tendsto_nhds_unique _ hp
    simpa only [physicalProjection_core] using
      ((physicalProjection N).continuous.tendsto e).comp he
  have hclosed : (f,g) ∈ closedGammaGraph N := by
    apply (closedGammaGraph_isClosed N).mem_of_tendsto (hp.prodMk_nhds hL)
    exact Eventually.of_forall (fun n =>
      (coreGraph N).le_topologicalClosure (graphOutput_mem N (u n)))
  have hfg : (f,g) ∈ (actualGammaFriedrichs N).graph :=
    closedGammaGraph_le_friedrichsGraph N hclosed
  obtain ⟨e',he',htest⟩ := (actualGammaFriedrichs_mem_graph_iff_formPair N).mp hfg
  have heq : e' = e := (physicalProjection_injective N) (he'.trans hproj.symm)
  have ht : ∀ d : EnergyCompletion N, actualDirichletPair N d e =
      inner ℂ (physicalProjection N d) g := by
    simpa only [heq] using htest
  refine ⟨e,he,hproj,ht,?_,hfg⟩
  simpa only [hproj] using ht e

/-- The physical limit determines the energy limit uniquely by actual
form closability. No choice of finite-core approximants survives. -/
theorem core_graph_tendsto_canonical_energy
    (N : ℕ) [NeZero N] (u : ℕ → EnergyCore N)
    (e : EnergyCompletion N) (g : QuotientL2 N)
    (hp : Tendsto (fun n => physicalCore N (u n)) atTop (𝓝 (physicalProjection N e)))
    (hL : Tendsto (fun n => coreLaplacian N (u n)) atTop (𝓝 g)) :
    Tendsto (fun n => coreEmbedding N (u n)) atTop (𝓝 e) := by
  obtain ⟨e',he',hproj,_⟩ := exists_energy_limit_of_core_graph N u _ g hp hL
  have heq : e' = e := (physicalProjection_injective N) hproj
  simpa only [heq] using he'

/-- Strong global gradient convergence on the actual carrier defining
quotient volume follows from the genuine energy limit, even when the
approximated compact smooth seed is outside the finite tensor span. -/
theorem core_graph_tendsto_carrier_gradient
    (N : ℕ) [NeZero N] (u : ℕ → EnergyCore N)
    (e : EnergyCompletion N) (g : QuotientL2 N)
    (hp : Tendsto (fun n => physicalCore N (u n)) atTop (𝓝 (physicalProjection N e)))
    (hL : Tendsto (fun n => coreLaplacian N (u n)) atTop (𝓝 g)) :
    Tendsto (fun n => carrierCoreGradient N (u n)) atTop
      (𝓝 (completedCarrierGradient N e)) := by
  have he := core_graph_tendsto_canonical_energy N u e g hp hL
  simpa only [completedCarrierGradient_core] using
    ((completedCarrierGradient N).continuous.tendsto e).comp he

/-- Full unshifted actual energy, rather than a compact carrier fragment,
is recovered from the original differential output of the graph limit. -/
theorem core_graph_gradient_energy_tendsto
    (N : ℕ) [NeZero N] (u : ℕ → EnergyCore N) (f g : QuotientL2 N)
    (hp : Tendsto (fun n => physicalCore N (u n)) atTop (𝓝 f))
    (hL : Tendsto (fun n => coreLaplacian N (u n)) atTop (𝓝 g)) :
    Tendsto (fun n => ‖carrierCoreGradient N (u n)‖ ^ 2) atTop
      (𝓝 ((inner ℂ f g).re)) := by
  obtain ⟨e,he,hproj,ht,henergy,hgraph⟩ := exists_energy_limit_of_core_graph N u f g hp hL
  have hg : Tendsto (fun n => carrierCoreGradient N (u n)) atTop
      (𝓝 (completedCarrierGradient N e)) := by
    simpa only [completedCarrierGradient_core] using
      ((completedCarrierGradient N).continuous.tendsto e).comp he
  simpa only [completedCarrierGradient_norm_sq,henergy] using hg.norm.pow 2

end
end ImbalancedChen.Part3.GammaNonzeroCoreGraphFormLimit20261026b
