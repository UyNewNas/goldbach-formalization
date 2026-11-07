import ImbalancedChen.Part3GammaActualCutoffClosedOperatorGraph

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual modular cutoff approximation in the NATIVE CLOSED OPERATOR GRAPH.
The actual quotient L2 cutoff first converges on all physical vectors by
its proved contraction and the dense physical energy range. The actual
operator output then converges by the genuine graph Leibniz identity and
the proved strong commutator decay. Every approximant has an explicitly
compact quotient-support representative. Energy convergence alone is
never used as a substitute for convergence of the operator output.
-/

namespace ImbalancedChen.Part3.GammaActualCutoffOperatorGraphConvergence20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0WeightedCutoffDefectLimit20261026a
open GammaActualClosedGraphGradientEnergy20261026b GammaActualCutoffCommutatorExtension20261026b
open GammaActualQuotientCutoffMultiplier20261026b GammaActualClosedFormCutoffConvergence20261026b
open GammaActualCutoffClosedOperatorGraph20261026b

/-- Actual physical quotient cutoff convergence for EVERY L2 vector,
including an operator output that is not itself assumed in the form domain. -/
theorem actualQuotientCutoffMultiplier_tendsto
    (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    Tendsto (fun n => actualQuotientCutoffMultiplier N (cutoffHeight n) (cutoffHeight_gt_one n) f)
      atTop (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨w,hw,hnear⟩ := Metric.mem_closure_iff.mp ((physicalProjection_denseRange N) f)
    (epsilon/4) (by positivity)
  obtain ⟨e,rfl⟩ := hw
  let g := physicalProjection N e
  have hsmall : ‖f-g‖ < epsilon/4 := by simpa only [dist_eq_norm] using hnear
  have hmiddle := Metric.tendsto_nhds.mp (actualClosedFormCutoff_physical_tendsto N e)
    (epsilon/2) (half_pos hepsilon)
  filter_upwards [hmiddle] with n hn
  rw [dist_eq_norm] at hn ⊢
  let Q := actualQuotientCutoffMultiplier N (cutoffHeight n) (cutoffHeight_gt_one n)
  have hdecomp : Q f-f = Q (f-g)+(Q g-g)+(g-f) := by
    rw [map_sub]
    abel
  have hrev : ‖g-f‖ = ‖f-g‖ := norm_sub_rev _ _
  calc
    _ = ‖Q (f-g)+(Q g-g)+(g-f)‖ := congrArg norm hdecomp
    _ ≤ (‖Q (f-g)‖+‖Q g-g‖)+‖g-f‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ (‖f-g‖+‖Q g-g‖)+‖g-f‖ :=
      add_le_add_right (add_le_add_right (actualQuotientCutoffMultiplier_norm_le N _ _ (f-g)) _) _
    _ < epsilon := by rw [hrev]; change ‖Q g-g‖ < epsilon/2 at hn; linarith

def actualCutoffGraphPair (N : ℕ) [NeZero N] (n : ℕ) (f g : QuotientL2 N) :
    QuotientL2 N × QuotientL2 N :=
  (actualQuotientCutoffMultiplier N (cutoffHeight n) (cutoffHeight_gt_one n) f,
    actualQuotientCutoffMultiplier N (cutoffHeight n) (cutoffHeight_gt_one n) g+
      actualCutoffCommutator N (cutoffHeight n) (cutoffHeight_gt_one n) (graphEnergyLift N f g))

theorem actualCutoffGraphPair_mem_nativeGraph
    (N : ℕ) [NeZero N] {f g : QuotientL2 N}
    (hgraph : (f,g) ∈ (actualClosedGammaMaass N).graph) (n : ℕ) :
    actualCutoffGraphPair N n f g ∈ (actualClosedGammaMaass N).graph :=
  actualCutoff_closedGraph_pair N (cutoffHeight n) (cutoffHeight_gt_one n) hgraph

/-- The native output converges by a PROVED vanishing commutator,
alongside strong physical L2 cutoff convergence of the original output. -/
theorem actualCutoffGraphPair_tendsto
    (N : ℕ) [NeZero N] {f g : QuotientL2 N}
    (hgraph : (f,g) ∈ (actualClosedGammaMaass N).graph) :
    Tendsto (fun n => actualCutoffGraphPair N n f g) atTop (𝓝 (f,g)) := by
  have houtput : Tendsto (fun n =>
      actualQuotientCutoffMultiplier N (cutoffHeight n) (cutoffHeight_gt_one n) g+
        actualCutoffCommutator N (cutoffHeight n) (cutoffHeight_gt_one n) (graphEnergyLift N f g))
      atTop (𝓝 g) := by
    simpa only [add_zero] using (actualQuotientCutoffMultiplier_tendsto N g).add
      (actualCutoffCommutator_tendsto_zero N (graphEnergyLift N f g))
  exact (actualQuotientCutoffMultiplier_tendsto N f).prodMk_nhds houtput

theorem actualOperatorDomainCutoff_graph_tendsto
    (N : ℕ) [NeZero N] (u : (actualClosedGammaMaass N).domain) :
    Tendsto (fun n =>
      (((actualOperatorDomainCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) u) : QuotientL2 N),
        actualClosedGammaMaass N (actualOperatorDomainCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) u)))
      atTop (𝓝 ((u : QuotientL2 N),actualClosedGammaMaass N u)) := by
  change Tendsto (fun n =>
    (actualQuotientCutoffMultiplier N (cutoffHeight n) (cutoffHeight_gt_one n) (u : QuotientL2 N),
      actualClosedGammaMaass N (actualOperatorDomainCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) u))) _ _
  simp_rw [actualOperatorDomainCutoff_output]
  exact actualCutoffGraphPair_tendsto N (LinearPMap.mem_graph _ u)

/-- Actual all-domain compact quotient-support graph approximation.
The approximants are original native operator-domain vectors obtained
from chi_(n+2); neither their membership nor graph convergence is assumed. -/
theorem exists_compactly_supported_native_graph_sequence
    (N : ℕ) [NeZero N] (u : (actualClosedGammaMaass N).domain) :
    ∃ v : ℕ → (actualClosedGammaMaass N).domain,
      Tendsto (fun n => ((v n : QuotientL2 N),actualClosedGammaMaass N (v n)))
        atTop (𝓝 ((u : QuotientL2 N),actualClosedGammaMaass N u)) ∧
      ∀ n : ℕ, ∃ F : Gamma0QuotientCellPushforward20261025a.Gamma0OrbitSpace N → ℂ,
        ((v n : QuotientL2 N) : Gamma0QuotientCellPushforward20261025a.Gamma0OrbitSpace N → ℂ)
          =ᵐ[Gamma0QuotientCellPushforward20261025a.carrierPushforward N] F ∧
        HasCompactSupport F ∧ Function.support F ⊆
          ActualModularCutoffCompactSupport20261025a.quotientTruncatedCarrier N (2*cutoffHeight n) := by
  refine ⟨fun n => actualOperatorDomainCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) u,
    actualOperatorDomainCutoff_graph_tendsto N u,?_⟩
  intro n
  exact actualCutoff_quotient_compact_representative N (cutoffHeight n) (cutoffHeight_gt_one n) u

end
end ImbalancedChen.Part3.GammaActualCutoffOperatorGraphConvergence20261026b
