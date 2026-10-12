import ImbalancedChen.ActualSelectedPrefixOwnCube
import ImbalancedChen.ActualOrdinaryUpperFiveCubeIntegral

/-!
# Exact finite-cell decomposition of the actual selected own-cube saving

Half-open ownership selects one constant rational cap. Outside the adopted
union the selected level is exactly the old level, so the actual gated
density difference is exactly zero. The finite identities below retain
both strict own-cube tests and the original candidate enumeration.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- The rational cap stored in one adopted cell. -/
def selectedPrefixCellCap {d : ℕ} (I : Finset (Fin d)) (old nu a b : ℚ)
    (m : ℕ) (j : Fin d → Fin (m + 1)) : ℚ :=
  selectedBoxCap I old nu (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j)

/-- Any real function of the selected cap decomposes without a remainder.
This uses exact cell ownership, not continuity or a limiting argument. -/
theorem selectedPrefixMeshCap_apply_sub {d : ℕ} (I : Finset (Fin d))
    (old nu a b : ℚ) (hab : a ≤ b) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1))) (t : Fin d → ℝ) (f : ℚ → ℝ) :
    f (selectedPrefixMeshCap I old nu a b m J t) - f old =
      ∑ j ∈ J, if t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j then
        f (selectedPrefixCellCap I old nu a b m j) - f old else 0 := by
  by_cases hex : ∃ j ∈ J, t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j
  · obtain ⟨j, hj, ht⟩ := hex
    rw [selectedPrefixMeshCap_on_cell I old nu a b hab m J t j hj ht,
      Finset.sum_eq_single_of_mem j hj, if_pos ht]
    · rfl
    · intro q _hq hqj
      apply if_neg
      intro hq
      exact hqj (logPrimeMeshCell_unique (by exact_mod_cast hab) hq ht)
  · have hout : ∀ j ∈ J, t ∉ logPrimeMeshCell (a : ℝ) (b : ℝ) m j := by
      simpa only [not_exists, not_and] using hex
    rw [selectedPrefixMeshCap_outside I old nu a b m J t hout, sub_self]
    symm
    exact Finset.sum_eq_zero (fun j hj => if_neg (hout j hj))

/-- The selected history density is exactly the tuple's actual normalized
residual at the cap read from that same history. -/
theorem actualSelectedOwnCube_normalized_history {k : ℕ}
    (N cap : ℕ) (I : Finset (Fin (k + 1))) (old nu a b : ℚ)
    (m : ℕ) (J : Finset (Fin (k + 1) → Fin (m + 1)))
    {history : List ℕ} (hlen : history.length = k + 1) :
    actualOwnCubeGatedMinusDensity N cap (actualSelectedPrefixLevel (N : ℝ) I old nu a b m J)
        history * Real.log (N : ℝ) / singularSeries N =
      actualPrimeTupleOwnCubeMinus N cap
        (selectedPrefixMeshCap I old nu a b m J
          (actualPrimeTupleLog N (primeHistoryTuple (k + 1) history)) : ℝ)
        (primeHistoryTuple (k + 1) history) := by
  rw [actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap _ hlen]
  simp only [actualOwnCubeGatedMinusDensity, actualSelectedPrefixLevel,
    primeHistoryLogCoordinates_eq_actualPrimeTupleLog]
  rfl

/-- Normalizing the literal nested candidate sum gives the exact tuple
sum, before any cell subdivision or asymptotic estimate. -/
theorem actualSelectedPrefixOwnCubeSum_eq_normalized_tuple_sum
    (k : ℕ) (lower : Bool) (N cap : ℕ) (z : ℝ) (I : Finset (Fin (k + 1)))
    (old nu a b : ℚ) (m : ℕ) (J : Finset (Fin (k + 1) → Fin (m + 1))) :
    actualSelectedPrefixOwnCubeSum lower N cap z I old nu a b m J *
        Real.log (N : ℝ) / singularSeries N =
      ∑ p ∈ firstExitFrontierTuples k
        (ordinaryParityRosserPolicy lower ((N : ℝ) ^ (old : ℝ)))
        (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (actualPrimeTupleOwnCubeMinus N cap
            (selectedPrefixMeshCap I old nu a b m J (actualPrimeTupleLog N p) : ℝ) p -
            actualPrimeTupleOwnCubeMinus N cap (old : ℝ) p) := by
  let parent := ordinaryParityRosserPolicy lower ((N : ℝ) ^ (old : ℝ))
  let h (q : ℕ) := 1 / ((q : ℝ) - 1)
  let states := firstExitDepthFrontier k parent h [] true 1 (roughPrimeUniverse N cap 0 z)
  let candidates (s : FirstExitDepthState ℕ) :=
    firstExitNextSelectionCandidates h s.selectedPrefix s.positive s.mass s.remaining
  let D (history : List ℕ) :=
    actualOwnCubeGatedMinusDensity N cap (actualSelectedPrefixLevel (N : ℝ) I old nu a b m J) history -
      actualOwnCubeGatedMinusDensity N cap (fun _ => (N : ℝ) ^ (old : ℝ)) history
  let f (p : Fin (k + 1) → ℕ) :=
    actualPrimeTupleOwnCubeMinus N cap
      (selectedPrefixMeshCap I old nu a b m J (actualPrimeTupleLog N p) : ℝ) p -
      actualPrimeTupleOwnCubeMinus N cap (old : ℝ) p
  have hn : actualSelectedPrefixOwnCubeSum lower N cap z I old nu a b m J *
      Real.log (N : ℝ) / singularSeries N =
      (states.map (fun s => ((candidates s).map (fun c =>
        (c.selectedPrefix.map h).prod * D c.selectedPrefix *
          (Real.log (N : ℝ) / singularSeries N))).sum)).sum := by
    simp only [List.sum_map_mul_right]
    change _ * Real.log (N : ℝ) / singularSeries N =
      actualSelectedPrefixOwnCubeSum lower N cap z I old nu a b m J *
        (Real.log (N : ℝ) / singularSeries N)
    ring
  rw [hn]
  have heq : (states.map (fun s => ((candidates s).map (fun c =>
        (c.selectedPrefix.map h).prod * D c.selectedPrefix *
          (Real.log (N : ℝ) / singularSeries N))).sum)).sum =
      (states.map (fun s => ((candidates s).map (fun c =>
        (c.selectedPrefix.map h).prod * f (primeHistoryTuple (k + 1) c.selectedPrefix))).sum)).sum := by
    congr 1
    apply List.map_congr_left
    intro s hs
    congr 1
    apply List.map_congr_left
    intro c hc
    have hlen := (actualPrimeNextSelection_geometry k parent N cap z s hs c hc).1
    have hnew := actualSelectedOwnCube_normalized_history N cap I old nu a b m J hlen
    have hold := actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap (old : ℝ) hlen
    dsimp [f]
    rw [← hnew, hold]
    dsimp [D]
    ring
  rw [heq]
  exact actualPrimeFrontier_candidates_weighted_sum_eq_tuple_sum k parent h N cap 0 z f

/-- Finite-cell decomposition of the normalized actual tuple summand.
No check or positivity hypothesis is needed for this algebraic identity. -/
theorem actualSelectedOwnCubeTuple_difference_cells {k : ℕ}
    (N cap : ℕ) (I : Finset (Fin (k + 1))) (old nu a b : ℚ)
    (hab : a ≤ b) (m : ℕ) (J : Finset (Fin (k + 1) → Fin (m + 1)))
    (p : Fin (k + 1) → ℕ) :
    actualPrimeTupleOwnCubeMinus N cap
        (selectedPrefixMeshCap I old nu a b m J (actualPrimeTupleLog N p) : ℝ) p -
      actualPrimeTupleOwnCubeMinus N cap (old : ℝ) p =
      ∑ j ∈ J, if actualPrimeTupleLog N p ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j then
        actualPrimeTupleOwnCubeMinus N cap (selectedPrefixCellCap I old nu a b m j : ℝ) p -
          actualPrimeTupleOwnCubeMinus N cap (old : ℝ) p else 0 := by
  exact selectedPrefixMeshCap_apply_sub I old nu a b hab m J (actualPrimeTupleLog N p)
    (fun lambda => actualPrimeTupleOwnCubeMinus N cap (lambda : ℝ) p)

end

end ImbalancedChen
