import ImbalancedChen.P5OriginalPrimeChartHBWitnesses

/-!
The existing active-psi scale lemma and the six repaired uniform-cutoff
supplier declarations, with original namespaces and statements preserved.
Four Lean API adaptations repair their existing proof expressions.
The two later grouped/selected-W interfaces remain in a historical postimage.
This source adoption adds no cutoff argument or arithmetic estimate.
-/

namespace ImbalancedChen.P5Z.OriginalIndependentFourPrimeChartCutoff
noncomputable section
open Classical Filter
open scoped BigOperators
open ActualLabelledPrimeSmoothCharts ExactOriginalSmoothDyadicPartition
open OriginalChartRoughCutoff

local notation "R" => ExactOriginalSmoothDyadicPartition.R

/-- Actual nonzero ψ, together with the physical slot floor and cap,
bounds every active R_j on the same ordered chart word. -/
theorem active_psi_scale_each (chi : ℝ → ℝ) {astar : ℝ}
    {N : ℕ} {js ps : List ℕ}
    (hwin : List.Forall₂
      (fun j p => psi chi ((p : ℝ) / R j) ≠ 0 ∧
        R j / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * R j) js ps)
    (hsource : ∀ p ∈ ps,
      (N : ℝ) ^ astar ≤ (p : ℝ) ∧ (p : ℝ) ≤ N) :
    ∀ j ∈ js,
      (N : ℝ) ^ astar / 2 ≤ R j ∧ R j ≤ 2 * N := by
  simp only [Lean.Internal.coeM, bind_pure_comp, List.map_eq_map] at hwin
  rw [List.forall₂_map_right_iff] at hwin
  induction hwin with
  | nil =>
      intro j hj
      simp at hj
  | @cons j p js ps hj htail ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · have hp := hsource p (by simp)
        constructor <;> linarith [hj.2.1,hj.2.2,hp.1,hp.2]
      · exact ih (fun q hq => hsource q (List.mem_cons_of_mem p hq)) a ha


end
end ImbalancedChen.P5Z.OriginalIndependentFourPrimeChartCutoff
