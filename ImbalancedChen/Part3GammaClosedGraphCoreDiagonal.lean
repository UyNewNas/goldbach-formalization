import ImbalancedChen.Part3GammaCoreGraphEnergyLimit
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Concrete diagonalization into the ORIGINAL finite smooth tensor core.
For each member (U_n,V_n) of the genuine minimal closed graph choose one
original core pair within the explicit tolerance 1/(n+1). Both coordinate
errors are proved with that same tolerance. If the outside graph sequence
converges to (f,0), these legal core vectors converge in the true closed
energy norm to a zero-energy lift of f. No smooth compact/core shortcut.
-/
namespace ImbalancedChen.Part3.GammaClosedGraphCoreDiagonal20261026a

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualMaassClosedOperator20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open GammaCoreGraphEnergyLimit20261026a

def diagonalTolerance (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem diagonalTolerance_pos (n : ℕ) : 0 < diagonalTolerance n := by
  unfold diagonalTolerance
  positivity

theorem diagonalTolerance_tendsto : Tendsto diagonalTolerance atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Every chosen stage is an original EnergyCore vector; a closure point
is never treated as an algebraic finite tensor vector. -/
theorem exists_legal_core_diagonal (N : ℕ) [NeZero N]
    (U V : ℕ → QuotientL2 N)
    (hG : ∀ n, (U n, V n) ∈ closedGammaGraph N) :
    ∃ u : ℕ → EnergyCore N, ∀ n,
      dist (U n) (physicalCore N (u n)) < diagonalTolerance n ∧
      dist (V n) (coreLaplacian N (u n)) < diagonalTolerance n := by
  have hex : ∀ n, ∃ u : EnergyCore N,
      dist (U n) (physicalCore N u) < diagonalTolerance n ∧
      dist (V n) (coreLaplacian N u) < diagonalTolerance n := by
    intro n
    have hmem : (U n, V n) ∈ closure (coreGraph N : Set (QuotientL2 N × QuotientL2 N)) := hG n
    obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hmem
      (diagonalTolerance n) (diagonalTolerance_pos n)
    have hu : p.1 ∈ smoothCore N := (coreGraph_domain_iff N p.1).mp ⟨p.2, hp⟩
    let u : EnergyCore N := ⟨p.1, hu⟩
    have hv : p.2 = coreLaplacian N u := (coreGraph_iff_operator N ⟨p.1, hu⟩ p.2).mp hp
    have hm : max (dist (U n) p.1) (dist (V n) p.2) < diagonalTolerance n := by
      simpa only [Prod.dist_eq] using hdist
    refine ⟨u, ?_, ?_⟩
    · exact (le_max_left _ _).trans_lt hm
    · rw [← hv]
      exact (le_max_right _ _).trans_lt hm
  choose u hu using hex
  exact ⟨u, hu⟩

/-- Explicit same-stage graph tolerances plus the actual outside cutoff
limit give legal core convergence, rather than only density as a slogan. -/
theorem exists_legal_energy_diagonal_of_graph_zero (N : ℕ) [NeZero N]
    (U V : ℕ → QuotientL2 N) (f : QuotientL2 N)
    (hG : ∀ n, (U n, V n) ∈ closedGammaGraph N)
    (hU : Tendsto U atTop (𝓝 f)) (hV : Tendsto V atTop (𝓝 0)) :
    ∃ u : ℕ → EnergyCore N, ∃ e : EnergyCompletion N,
      (∀ n, dist (U n) (physicalCore N (u n)) < diagonalTolerance n ∧
        dist (V n) (coreLaplacian N (u n)) < diagonalTolerance n) ∧
      Tendsto (fun n => physicalCore N (u n)) atTop (𝓝 f) ∧
      Tendsto (fun n => coreLaplacian N (u n)) atTop (𝓝 0) ∧
      Tendsto (fun n => coreEmbedding N (u n)) atTop (𝓝 e) ∧
      physicalProjection N e = f ∧ actualDirichletPair N e e = 0 ∧
      (f, (0 : QuotientL2 N)) ∈ (actualGammaFriedrichs N).graph := by
  obtain ⟨u, hu⟩ := exists_legal_core_diagonal N U V hG
  have hpGap : Tendsto (fun n => dist (U n) (physicalCore N (u n))) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun n => (hu n).1.le) diagonalTolerance_tendsto
  have hLGap : Tendsto (fun n => dist (V n) (coreLaplacian N (u n))) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun n => (hu n).2.le) diagonalTolerance_tendsto
  have hp := hU.congr_dist hpGap
  have hL := hV.congr_dist hLGap
  obtain ⟨e, he, hproj, henergy, hkernel⟩ := core_graph_zero_energy_and_kernel N u f hp hL
  exact ⟨u, e, hu, hp, hL, he, hproj, henergy, hkernel⟩

end
end ImbalancedChen.Part3.GammaClosedGraphCoreDiagonal20261026a
