import ImbalancedChen.ActualRosserTripleBoxFamily
import ImbalancedChen.RosserTripleMesh
import ImbalancedChen.RosserTripleLayerIdentity

/-!
# Actual upper Rosser density above continuous three-prime lower sums

A normalized inner mesh is chosen before the target grows. Scaling its
coordinates by the fixed positive outer exponent preserves all boundary
gates and disjointness. The actual finite-family theorem then supplies one
threshold for the complete lower sum, uniformly in covering caps.
The proved continuous mesh limit then selects a mesh before that threshold
and supplies the lower bound by the genuine three-prime layer integral.
The exact integral identity also expresses this contribution as Suzuki's
source layer three. It does not sum the higher positive boundary layers.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology

/-- Every fixed strict inner mesh contributes its entire logarithmic lower
sum to the same raw upper Rosser density at residual coordinate three. -/
theorem exists_actualSmallRosserPlusDensity_tripleMesh_lower_threshold
    (u : ℝ) (hu : 0 < u) (n : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + (∑ j ∈ rosserTripleMeshCells n,
          (1 / rosserTripleMeshHi n j 2) *
            (∏ i, Real.log (rosserTripleMeshHi n j i / rosserTripleMeshLo n j i))) - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  let a := fun j : Fin 3 → Fin (n + 1) => fun i => u * rosserTripleMeshLo n j i
  let b := fun j : Fin 3 → Fin (n + 1) => fun i => u * rosserTripleMeshHi n j i
  have ha (j : Fin 3 → Fin (n + 1)) (_hj : j ∈ rosserTripleMeshCells n) (i : Fin 3) :
      0 < a j i := by
    have h := (rosserTripleMeshLoHi_bounds n j i).1
    exact mul_pos hu (by linarith)
  have hab (j : Fin 3 → Fin (n + 1)) (_hj : j ∈ rosserTripleMeshCells n) (i : Fin 3) :
      a j i < b j i :=
    mul_lt_mul_of_pos_left (rosserTripleMeshLoHi_bounds n j i).2.1 hu
  have hsep (j : Fin 3 → Fin (n + 1)) (hj : j ∈ rosserTripleMeshCells n)
      (i : Fin 2) : b j i.succ ≤ a j i.castSucc := by
    have h := mem_rosserTripleMeshCells.mp hj
    fin_cases i
    · exact mul_le_mul_of_nonneg_left h.1 hu.le
    · exact mul_le_mul_of_nonneg_left h.2.1 hu.le
  have hbu (j : Fin 3 → Fin (n + 1)) (_hj : j ∈ rosserTripleMeshCells n) : b j 0 ≤ u := by
    simpa [b] using mul_le_mul_of_nonneg_left (rosserTripleMeshLoHi_bounds n j 0).2.2 hu.le
  have hcube (j : Fin 3 → Fin (n + 1)) (hj : j ∈ rosserTripleMeshCells n) :
      3 * b j 0 ≤ 3 * u := by linarith [hbu j hj]
  have hshell (j : Fin 3 → Fin (n + 1)) (hj : j ∈ rosserTripleMeshCells n) :
      3 * u ≤ a j 0 + a j 1 + 3 * a j 2 := by
    have h := mul_lt_mul_of_pos_left (mem_rosserTripleMeshCells.mp hj).2.2 hu
    dsimp [a]
    nlinarith
  have hdisj (j : Fin 3 → Fin (n + 1)) (_hj : j ∈ rosserTripleMeshCells n)
      (k : Fin 3 → Fin (n + 1)) (_hk : k ∈ rosserTripleMeshCells n) (hjk : j ≠ k) :
      ∃ i, b j i ≤ a k i ∨ b k i ≤ a j i := by
    obtain ⟨i, hi | hi⟩ := rosserTripleMesh_separated hjk
    · exact ⟨i, Or.inl (mul_le_mul_of_nonneg_left hi hu.le)⟩
    · exact ⟨i, Or.inr (mul_le_mul_of_nonneg_left hi hu.le)⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_tripleBoxFamily_lower_threshold
      (rosserTripleMeshCells n) a b u (3 * u) hu (by linarith)
      ha hab hsep hbu hcube hshell hdisj eta heta
  have heq (j : Fin 3 → Fin (n + 1)) :
      (u / b j 2) * (∏ i, Real.log (b j i / a j i)) =
        (1 / rosserTripleMeshHi n j 2) *
          (∏ i, Real.log (rosserTripleMeshHi n j i / rosserTripleMeshLo n j i)) := by
    have hratio (i : Fin 3) : b j i / a j i =
        rosserTripleMeshHi n j i / rosserTripleMeshLo n j i := by
      dsimp [a, b]
      exact mul_div_mul_left _ _ hu.ne'
    simp_rw [hratio]
    congr 1
    dsimp [b]
    rw [div_mul_eq_div_div, div_self hu.ne']
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  simpa only [heq] using hbound N hN hEven cap hcap

/-- The full continuous three-prime layer is a proved lower contribution
to the same raw density. The mesh and its target threshold are both chosen
before N and cap; there is no prime-density or integral-limit hypothesis. -/
theorem exists_actualSmallRosserPlusDensity_tripleLayer_lower_threshold
    (u : ℝ) (hu : 0 < u) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + rosserTripleLayerIntegral - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hnear := tendsto_rosserTripleMeshLowerSum.eventually
    (lt_mem_nhds (show rosserTripleLayerIntegral - eta / 2 < rosserTripleLayerIntegral by
      linarith))
  obtain ⟨n, hn⟩ := hnear.exists
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_tripleMesh_lower_threshold u hu n (eta / 2)
      (by linarith)
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  have h := hbound N hN hEven cap hcap
  change 1 + rosserTripleMeshLowerSum n - eta / 2 ≤ _ at h
  linarith

/-- At the original residual-three scale R=N, the genuine layer integral
is obtained uniformly in every cap covering the strict cube cutoff. -/
theorem exists_actualSmallRosserPlusDensity_oneThird_tripleLayer_lower_threshold
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ (1 / 3 : ℝ) ≤ (cap : ℝ) →
        1 + rosserTripleLayerIntegral - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ (1 / 3 : ℝ)) (N : ℝ) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  simpa only [show (3 * (1 / 3 : ℝ)) = 1 by norm_num, Real.rpow_one] using
    exists_actualSmallRosserPlusDensity_tripleLayer_lower_threshold (1 / 3) (by norm_num)
      eta heta

/-- The continuous contribution is the proved Suzuki source layer, not a
new constant assumed to equal it. Higher layers are still omitted. -/
theorem exists_actualSmallRosserPlusDensity_suzukiLayerThree_lower_threshold
    (u : ℝ) (hu : 0 < u) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiLayer 1 2 3 3 - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  simpa only [rosserTripleLayerIntegral_eq_suzukiLayer] using
    exists_actualSmallRosserPlusDensity_tripleLayer_lower_threshold u hu eta heta

/-- Original R=N specialization of the genuine Suzuki-layer lower bound. -/
theorem exists_actualSmallRosserPlusDensity_oneThird_suzukiLayerThree_lower_threshold
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ (1 / 3 : ℝ) ≤ (cap : ℝ) →
        1 + MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiLayer 1 2 3 3 - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ (1 / 3 : ℝ)) (N : ℝ) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  simpa only [rosserTripleLayerIntegral_eq_suzukiLayer] using
    exists_actualSmallRosserPlusDensity_oneThird_tripleLayer_lower_threshold eta heta

end

end ImbalancedChen
