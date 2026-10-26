import ImbalancedChen.Part3GammaActualCutoffCommutatorExtension
import ImbalancedChen.Part3GammaActualClosedGraphGradientEnergy
import ImbalancedChen.Part3ActualModularCutoffCompactSupport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual cutoff preservation of the ENTIRE native minimal closed-operator
domain, with its genuine graph Leibniz output. The constructed original
core graph sequence converges in both physical coordinates and in energy;
bounded actual cutoff and commutator maps then identify the output before
the actual CLOSED GRAPH is invoked. No operator-domain multiplication or
graph convergence is a premise. Every cutoff input has an explicit compact
quotient-support representative.
-/

namespace ImbalancedChen.Part3.GammaActualCutoffClosedOperatorGraph20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualMaassClosedOperator20261025a Gamma0ActualEnergyCompletion20261025a
open GammaActualClosedGraphGradientEnergy20261026b GammaMinimalPairFormApproximation20261026b
open GammaActualCutoffCoreGraphOutput20261026b GammaActualCutoffCommutatorExtension20261026b
open GammaActualQuotientCutoffMultiplier20261026b GammaActualClosedFormCutoffMultiplier20261026b
open GammaSmoothMultiplierLegalTests20261026a GammaSmoothMultiplierPeriodization20261026a
open ActualModularCutoffMaassBudget20261025a ActualModularCutoffCompactSupport20261025a
open ActualModularSmoothCutoffL2Tail20261025a

/-- The only extra energy datum is its physical representation of f.
The canonical graphEnergyLift supplies it in the public endpoint below. -/
theorem actualCutoff_closedGraph_pair_of_energy_rep
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    {f g : QuotientL2 N} (hgraph : (f,g) ∈ (actualClosedGammaMaass N).graph)
    (e : EnergyCompletion N) (hproj : physicalProjection N e = f) :
    (actualQuotientCutoffMultiplier N Y hY f,
      actualQuotientCutoffMultiplier N Y hY g+actualCutoffCommutator N Y hY e)
      ∈ (actualClosedGammaMaass N).graph := by
  obtain ⟨u,e',hp,hL,he,hproj',ht,hgrad,henergy⟩ := exists_minimal_pair_form_approximation N f g hgraph
  have heq : e' = e := (physicalProjection_injective N) (hproj'.trans hproj.symm)
  have hE : Tendsto (fun n => coreEmbedding N (u n)) atTop (𝓝 e) := by simpa only [heq] using he
  have hinput := ((actualQuotientCutoffMultiplier N Y hY).continuous.tendsto f).comp hp
  have houtput : Tendsto (fun n => cutoffCoreOutputLinear N Y hY (u n)) atTop
      (𝓝 (actualQuotientCutoffMultiplier N Y hY g+actualCutoffCommutator N Y hY e)) := by
    have hA := ((actualQuotientCutoffMultiplier N Y hY).continuous.tendsto g).comp hL
    have hC := ((actualCutoffCommutator N Y hY).continuous.tendsto e).comp hE
    have hsum := hA.add hC
    apply hsum.congr'
    exact Eventually.of_forall (fun n => by
      rw [actualCutoffCommutator_core]
      change _ = actualQuotientCutoffMultiplier N Y hY (coreLaplacian N (u n)) +
        (cutoffCoreOutputLinear N Y hY (u n)-actualQuotientCutoffMultiplier N Y hY (coreLaplacian N (u n)))
      abel)
  rw [actualClosedGammaMaass_graph_eq]
  apply (closedGammaGraph_isClosed N).mem_of_tendsto (hinput.prodMk_nhds houtput)
  exact Eventually.of_forall (fun n => by
    rw [← actualClosedGammaMaass_graph_eq]
    exact cutoffCoreOutput_graph N Y hY (u n))

/-- Genuine all-domain graph Leibniz endpoint, with the original Riesz
energy lift fixed by the input/output pair and no caller form premise. -/
theorem actualCutoff_closedGraph_pair
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    {f g : QuotientL2 N} (hgraph : (f,g) ∈ (actualClosedGammaMaass N).graph) :
    (actualQuotientCutoffMultiplier N Y hY f,
      actualQuotientCutoffMultiplier N Y hY g+
        actualCutoffCommutator N Y hY (graphEnergyLift N f g))
      ∈ (actualClosedGammaMaass N).graph :=
  actualCutoff_closedGraph_pair_of_energy_rep N Y hY hgraph (graphEnergyLift N f g)
    (graphEnergyLift_projection N hgraph)

theorem actualCutoff_preserves_operatorDomain
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : (actualClosedGammaMaass N).domain) :
    actualQuotientCutoffMultiplier N Y hY (u : QuotientL2 N) ∈ (actualClosedGammaMaass N).domain :=
  LinearPMap.mem_domain_iff.mpr ⟨_,actualCutoff_closedGraph_pair N Y hY (LinearPMap.mem_graph _ u)⟩

def actualOperatorDomainCutoff (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    (actualClosedGammaMaass N).domain →ₗ[ℂ] (actualClosedGammaMaass N).domain where
  toFun u := ⟨actualQuotientCutoffMultiplier N Y hY (u : QuotientL2 N),
    actualCutoff_preserves_operatorDomain N Y hY u⟩
  map_add' u v := Subtype.ext (by simp only [Submodule.coe_add,map_add])
  map_smul' c u := Subtype.ext (by simp only [Submodule.coe_smul,map_smul])

theorem actualOperatorDomainCutoff_output
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : (actualClosedGammaMaass N).domain) :
    actualClosedGammaMaass N (actualOperatorDomainCutoff N Y hY u) =
      actualQuotientCutoffMultiplier N Y hY (actualClosedGammaMaass N u)+
        actualCutoffCommutator N Y hY (graphEnergyLift N (u : QuotientL2 N) (actualClosedGammaMaass N u)) := by
  have h1 := LinearPMap.mem_graph (actualClosedGammaMaass N) (actualOperatorDomainCutoff N Y hY u)
  have h2 := actualCutoff_closedGraph_pair N Y hY (LinearPMap.mem_graph _ u)
  rw [actualClosedGammaMaass_graph_eq] at h1 h2
  exact closedGammaGraph_right_unique N h1 h2

theorem actualCutoff_graph_output_bound
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    {f g : QuotientL2 N} (hgraph : (f,g) ∈ (actualClosedGammaMaass N).graph) :
    ‖actualQuotientCutoffMultiplier N Y hY g+
        actualCutoffCommutator N Y hY (graphEnergyLift N f g)‖ ≤
      ‖g‖+cutoffCommutatorBound*(‖f‖+‖g‖) := by
  apply (norm_add_le _ _).trans
  exact add_le_add (actualQuotientCutoffMultiplier_norm_le N Y hY g)
    ((actualCutoffCommutator_norm_le N Y hY _).trans
      (mul_le_mul_of_nonneg_left (actual_closed_graph_energy_norm_le N hgraph) cutoffCommutatorBound_nonneg))

/-- Explicit compact-quotient-support representative of the actual L2
cutoff product; no regularity of the arbitrary original input is needed. -/
theorem actualCutoff_quotient_compact_representative
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (f : QuotientL2 N) :
    ∃ F : Gamma0OrbitSpace N → ℂ,
      (actualQuotientCutoffMultiplier N Y hY f : Gamma0OrbitSpace N → ℂ)
        =ᵐ[carrierPushforward N] F ∧ HasCompactSupport F ∧
      Function.support F ⊆ quotientTruncatedCarrier N (2*Y) := by
  let F := quotientMultiplier N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y) * f
  have hs : Function.support F ⊆ quotientTruncatedCarrier N (2*Y) := by
    intro q hq
    apply quotientCutoff_support_subset N Y hY.le
    intro hzero
    apply hq
    simp only [F,Pi.mul_apply,actualCutoff_quotientMultiplier, hzero,Complex.ofReal_zero,zero_mul]
  letI := quotient_t2 N
  exact ⟨F,actualQuotientCutoffMultiplier_coe_ae N Y hY f,
    HasCompactSupport.of_support_subset_isCompact (quotientTruncatedCarrier_isCompact N (2*Y)) hs,hs⟩

end
end ImbalancedChen.Part3.GammaActualCutoffClosedOperatorGraph20261026b
