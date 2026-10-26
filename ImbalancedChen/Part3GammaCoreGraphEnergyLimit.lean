import ImbalancedChen.Part3Gamma0PhysicalClosedDirichletForm
import ImbalancedChen.Part3Gamma0ActualMinimalFriedrichsInclusion
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Sequences

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A graph-convergent sequence in the ACTUAL finite smooth tensor Poincare
core converges in the ACTUAL completed shifted Dirichlet norm. In the
zero-output case the physical limit has zero closed Dirichlet energy
and belongs to the actual Friedrichs kernel. No compact smooth function
is declared a core vector, and no form membership is an input.
-/
namespace ImbalancedChen.Part3.GammaCoreGraphEnergyLimit20261026a

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a

/-- The actual shifted form norm is bounded by the actual graph norm,
with no unknown continuity constant. -/
theorem energy_norm_le_graph_sum (N : ℕ) [NeZero N] (u : EnergyCore N) :
    ‖u‖ ≤ ‖physicalCore N u‖ + ‖coreLaplacian N u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [energy_norm_sq]
  have hi := re_inner_le_norm (𝕜 := ℂ) (physicalCore N u) (coreLaplacian N u)
  nlinarith [mul_nonneg (norm_nonneg (physicalCore N u)) (norm_nonneg (coreLaplacian N u)),
    sq_nonneg ‖coreLaplacian N u‖]

/-- Physical and differential Cauchy control gives genuine form Cauchy
control before completing, on the original legal core itself. -/
theorem energy_cauchySeq_of_graph_cauchySeq (N : ℕ) [NeZero N]
    (u : ℕ → EnergyCore N)
    (hp : CauchySeq (fun n => physicalCore N (u n)))
    (hL : CauchySeq (fun n => coreLaplacian N (u n))) :
    CauchySeq (fun n => coreEmbedding N (u n)) := by
  apply Metric.cauchySeq_iff.mpr
  intro eps heps
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hp (eps / 2) (half_pos heps)
  obtain ⟨L, hL⟩ := Metric.cauchySeq_iff.mp hL (eps / 2) (half_pos heps)
  refine ⟨max K L, ?_⟩
  intro m hm n hn
  have hp' := hK m ((le_max_left K L).trans hm) n ((le_max_left K L).trans hn)
  have hL' := hL m ((le_max_right K L).trans hm) n ((le_max_right K L).trans hn)
  rw [dist_eq_norm, ← map_sub, coreEmbedding_norm]
  have hb := energy_norm_le_graph_sum N (u m - u n)
  simp only [map_sub] at hb
  rw [dist_eq_norm] at hp' hL'
  exact hb.trans_lt (by linarith)

/-- A graph-zero sequence produces its energy limit and the exact
physical projection; neither is postulated as a form-domain witness. -/
theorem exists_energy_limit_of_core_graph_zero (N : ℕ) [NeZero N]
    (u : ℕ → EnergyCore N) (f : QuotientL2 N)
    (hp : Tendsto (fun n => physicalCore N (u n)) atTop (𝓝 f))
    (hL : Tendsto (fun n => coreLaplacian N (u n)) atTop (𝓝 0)) :
    ∃ e : EnergyCompletion N,
      Tendsto (fun n => coreEmbedding N (u n)) atTop (𝓝 e) ∧
      physicalProjection N e = f ∧ actualDirichletPair N e e = 0 := by
  obtain ⟨e, he⟩ := cauchySeq_tendsto_of_complete
    (energy_cauchySeq_of_graph_cauchySeq N u hp.cauchySeq hL.cauchySeq)
  have hproj : physicalProjection N e = f := by
    apply tendsto_nhds_unique _ hp
    simpa only [physicalProjection_core] using ((physicalProjection N).continuous.tendsto e).comp he
  have hclosed : Tendsto (fun n => actualDirichletPair N (coreEmbedding N (u n))
      (coreEmbedding N (u n))) atTop (𝓝 (actualDirichletPair N e e)) := by
    unfold actualDirichletPair
    exact (he.inner he).sub ((((physicalProjection N).continuous.tendsto e).comp he).inner
      (((physicalProjection N).continuous.tendsto e).comp he))
  have hzero : Tendsto (fun n => actualDirichletPair N (coreEmbedding N (u n))
      (coreEmbedding N (u n))) atTop (𝓝 0) := by
    simpa only [actualDirichletPair_core, inner_zero_right] using hp.inner hL
  exact ⟨e, he, hproj, tendsto_nhds_unique hclosed hzero⟩

/-- Zero self-energy kills all cross pairings by the genuine closed-form
Cauchy--Schwarz inequality, not an unproved weak PDE assertion. -/
theorem actualDirichletPair_right_zero_of_self_zero (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) (he : actualDirichletPair N e e = 0)
    (d : EnergyCompletion N) : actualDirichletPair N d e = 0 := by
  have hb := actualDirichletPair_normSq_le N d e
  rw [he, Complex.zero_re, mul_zero] at hb
  have hz : Complex.normSq (actualDirichletPair N d e) = 0 :=
    le_antisymm hb (Complex.normSq_nonneg _)
  exact Complex.normSq_eq_zero.mp hz

/-- The actual graph-zero approximation yields the native Friedrichs
kernel, with its exact completed energy witness and convergence. -/
theorem core_graph_zero_energy_and_kernel (N : ℕ) [NeZero N]
    (u : ℕ → EnergyCore N) (f : QuotientL2 N)
    (hp : Tendsto (fun n => physicalCore N (u n)) atTop (𝓝 f))
    (hL : Tendsto (fun n => coreLaplacian N (u n)) atTop (𝓝 0)) :
    ∃ e : EnergyCompletion N,
      Tendsto (fun n => coreEmbedding N (u n)) atTop (𝓝 e) ∧
      physicalProjection N e = f ∧ actualDirichletPair N e e = 0 ∧
      (f, (0 : QuotientL2 N)) ∈ (actualGammaFriedrichs N).graph := by
  obtain ⟨e, he, hpE, hq⟩ := exists_energy_limit_of_core_graph_zero N u f hp hL
  refine ⟨e, he, hpE, hq, (actualGammaFriedrichs_mem_graph_iff_formPair N).mpr ?_⟩
  refine ⟨e, hpE, ?_⟩
  intro d
  rw [actualDirichletPair_right_zero_of_self_zero N e hq d, inner_zero_right]

end
end ImbalancedChen.Part3.GammaCoreGraphEnergyLimit20261026a

