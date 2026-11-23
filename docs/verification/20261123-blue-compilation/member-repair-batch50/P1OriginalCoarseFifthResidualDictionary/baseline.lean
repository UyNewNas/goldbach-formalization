import ImbalancedChen.P1OriginalCoarseFifthContinuationCells
import ImbalancedChen.ActualHistoricalFifthSavingIntegral

/-!
The original coarse fifth saving on ALL rank-four next candidates.
Both old and new own-cube gates remain inside their actual residuals.
Neither gate is inserted in the candidate carrier. No comparison with a
constant historical old level, density mean or arithmetic limit is assumed.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

namespace P1OriginalCoarseFifthResidual

open P1OriginalCoarseFifthContinuation

def tupleHistory (p : Fin 5 → ℕ) : List ℕ := (List.ofFn p).reverse

theorem tupleHistory_primeHistoryTuple (history : List ℕ) (hlen : history.length = 5) :
    tupleHistory (primeHistoryTuple 5 history) = history := by
  unfold tupleHistory
  rw [primeHistoryTuple_ofFn hlen, List.reverse_reverse]

theorem primeHistoryTuple_tupleHistory (p : Fin 5 → ℕ) :
    primeHistoryTuple 5 (tupleHistory p) = p := by
  apply List.ofFn_injective
  rw [primeHistoryTuple_ofFn (show (tupleHistory p).length = 5 by simp [tupleHistory])]
  simp only [tupleHistory, List.reverse_reverse]

theorem tupleHistory_log (N : ℕ) (p : Fin 5 → ℕ) :
    primeHistoryLogCoordinates (N : ℝ) 5 (tupleHistory p) = actualPrimeTupleLog N p := by
  rw [primeHistoryLogCoordinates_eq_actualPrimeTupleLog, primeHistoryTuple_tupleHistory]

theorem tupleHistory_pos (p : Fin 5 → ℕ) (hp : ∀ i, 0 < p i) :
    ∀ q ∈ tupleHistory p, 0 < q := by
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hq)
  exact hp i

def coarseTupleOwnCubeDifference (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  actualPrimeTupleOwnCubeMinus N cap
      (effectiveExponent5Q e chi m omega J4 cap4 J5 cap5 (N : ℝ) (tupleHistory p) : ℝ) p -
    actualPrimeTupleOwnCubeMinus N cap
      (P1OriginalCoarseContinuation.effectiveExponent4Q e chi m omega J4 cap4 (N : ℝ)
        (rosserAncestor 4 (tupleHistory p)) : ℝ) p

def coarseCellPrimeCorrection (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (z : ℝ) (j : Label5 m) : ℝ :=
  ∑ p ∈ firstExitFrontierTuples 4
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 z),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
        coarseTupleOwnCubeDifference e chi m omega J4 cap4 J5 cap5 N cap p else 0)

theorem newOwnCube_normalized_history (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (history : List ℕ) (hlen : history.length = 5) :
    actualOwnCubeGatedMinusDensity N cap
        (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)) history *
        Real.log (N : ℝ) / singularSeries N =
      actualPrimeTupleOwnCubeMinus N cap
        (effectiveExponent5Q e chi m omega J4 cap4 J5 cap5 (N : ℝ) history : ℝ)
        (primeHistoryTuple 5 history) := by
  rw [actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap _ (k := 4) hlen]
  simp only [actualOwnCubeGatedMinusDensity, level5, effectiveExponent5]

theorem oldOwnCube_normalized_history (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (N cap : ℕ) (history : List ℕ) (hlen : history.length = 5) :
    actualOwnCubeGatedMinusDensity N cap
        (fun pre => P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ)
          (rosserAncestor 4 pre)) history * Real.log (N : ℝ) / singularSeries N =
      actualPrimeTupleOwnCubeMinus N cap
        (P1OriginalCoarseContinuation.effectiveExponent4Q e chi m omega J4 cap4 (N : ℝ)
          (rosserAncestor 4 history) : ℝ) (primeHistoryTuple 5 history) := by
  rw [actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap _ (k := 4) hlen]
  simp only [actualOwnCubeGatedMinusDensity, P1OriginalCoarseContinuation.level4,
    P1OriginalCoarseContinuation.effectiveExponent4]

theorem coarseTupleOwnCubeDifference_history (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (history : List ℕ) (hlen : history.length = 5) :
    coarseTupleOwnCubeDifference e chi m omega J4 cap4 J5 cap5 N cap
        (primeHistoryTuple 5 history) =
      (actualOwnCubeGatedMinusDensity N cap
          (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)) history -
        actualOwnCubeGatedMinusDensity N cap
          (fun pre => P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ)
            (rosserAncestor 4 pre)) history) * Real.log (N : ℝ) / singularSeries N := by
  unfold coarseTupleOwnCubeDifference
  rw [tupleHistory_primeHistoryTuple history hlen,
    ← newOwnCube_normalized_history e chi m omega J4 cap4 J5 cap5 N cap history hlen,
    ← oldOwnCube_normalized_history e chi m omega J4 cap4 N cap history hlen]
  ring

theorem coarseTupleOwnCubeDifference_outside (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (p : Fin 5 → ℕ)
    (hout : ∀ j ∈ selectedFifthCells e chi m omega J5,
      actualPrimeTupleLog N p ∉ logPrimeMeshCell 0 (19 / 96) m j) :
    coarseTupleOwnCubeDifference e chi m omega J4 cap4 J5 cap5 N cap p = 0 := by
  unfold coarseTupleOwnCubeDifference
  rw [effectiveExponent5Q_outside e chi m omega J4 cap4 J5 cap5 (N : ℝ) (tupleHistory p)
    (by simpa only [tupleHistory_log] using hout), sub_self]

/-- Old4 includes its selected cap4 or original active Gamma fallback.
Its own strict gate is not presumed to pass on any next candidate. -/
theorem coarseTupleOwnCubeDifference_on_cell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hp : ∀ i, 0 < p i)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    coarseTupleOwnCubeDifference e chi m omega J4 cap4 J5 cap5 N cap p =
      actualPrimeTupleOwnCubeMinus N cap (cap5 j : ℝ) p -
        actualPrimeTupleOwnCubeMinus N cap (old5 e chi m omega J4 cap4 j : ℝ) p := by
  have hlen : (tupleHistory p).length = 5 := by simp [tupleHistory]
  have ht' : primeHistoryLogCoordinates (N : ℝ) 5 (tupleHistory p) ∈
      logPrimeMeshCell 0 (19 / 96) m j := by simpa only [tupleHistory_log] using ht
  unfold coarseTupleOwnCubeDifference
  rw [effectiveExponent5Q_on_selected_cell e chi m omega J4 cap4 J5 cap5 (N : ℝ)
    (tupleHistory p) hlen j hj ht',
    inherited_fourth_on_selected_fifth_cell e chi m omega J4 cap4 J5 (N : ℝ)
      (tupleHistory p) (by exact_mod_cast hN) hlen (tupleHistory_pos p hp) j hj ht']

theorem coarseTupleOwnCubeDifference_on_unselected_cell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (p : Fin 5 → ℕ) (j : Label5 m)
    (hj : j ∉ selectedFifthCells e chi m omega J5)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    coarseTupleOwnCubeDifference e chi m omega J4 cap4 J5 cap5 N cap p = 0 := by
  apply coarseTupleOwnCubeDifference_outside e chi m omega J4 cap4 J5 cap5 N cap p
  intro q hq htq
  have hqj := logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) htq ht
  exact hj (hqj ▸ hq)

theorem coarseTupleOwnCubeDifference_eq_cell_indicators
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (p : Fin 5 → ℕ) :
    coarseTupleOwnCubeDifference e chi m omega J4 cap4 J5 cap5 N cap p =
      ∑ j ∈ selectedFifthCells e chi m omega J5,
        if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
          coarseTupleOwnCubeDifference e chi m omega J4 cap4 J5 cap5 N cap p else 0 := by
  by_cases hex : ∃ j ∈ selectedFifthCells e chi m omega J5,
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
  · obtain ⟨j, hj, ht⟩ := hex
    rw [Finset.sum_eq_single_of_mem j hj]
    · rw [if_pos ht]
    · intro q _hq hqj
      apply if_neg
      intro htq
      exact hqj (logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) htq ht)
  · have hout : ∀ j ∈ selectedFifthCells e chi m omega J5,
        actualPrimeTupleLog N p ∉ logPrimeMeshCell 0 (19 / 96) m j := by
      simpa only [not_exists, not_and] using hex
    rw [coarseTupleOwnCubeDifference_outside e chi m omega J4 cap4 J5 cap5 N cap p hout]
    symm
    exact Finset.sum_eq_zero (fun j hj => if_neg (hout j hj))

/-- Complete next-candidate reindexing; the old own cube never filters
this carrier, including candidates admitted only at the new level. -/
theorem actualSaving_eq_tupleSum (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (z : ℝ) :
    actualHistoricalFifthSaving (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ))
        (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)) N cap z *
          Real.log (N : ℝ) / singularSeries N =
      ∑ p ∈ firstExitFrontierTuples 4
          (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
          (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          coarseTupleOwnCubeDifference e chi m omega J4 cap4 J5 cap5 N cap p := by
  let base := HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ)
  let parent := HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ)
  let h (q : ℕ) := 1 / ((q : ℝ) - 1)
  let states := firstExitDepthFrontier 4 parent h [] true 1 (roughPrimeUniverse N cap 0 z)
  let candidates (s : FirstExitDepthState ℕ) :=
    firstExitNextSelectionCandidates h s.selectedPrefix s.positive s.mass s.remaining
  let residual (history : List ℕ) :=
    actualOwnCubeGatedMinusDensity N cap
        (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)) history -
      actualOwnCubeGatedMinusDensity N cap
        (fun pre => P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ)
          (rosserAncestor 4 pre)) history
  have hn : actualHistoricalFifthSaving base
      (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
      (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ))
      (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)) N cap z *
      Real.log (N : ℝ) / singularSeries N =
      (states.map (fun s => ((candidates s).map (fun c =>
        (c.selectedPrefix.map h).prod * residual c.selectedPrefix *
          (Real.log (N : ℝ) / singularSeries N))).sum)).sum := by
    simp only [List.sum_map_mul_right]
    change _ * Real.log (N : ℝ) / singularSeries N =
      actualHistoricalFifthSaving base
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ))
        (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)) N cap z *
        (Real.log (N : ℝ) / singularSeries N)
    ring
  rw [hn]
  have heq : (states.map (fun s => ((candidates s).map (fun c =>
      (c.selectedPrefix.map h).prod * residual c.selectedPrefix *
        (Real.log (N : ℝ) / singularSeries N))).sum)).sum =
      (states.map (fun s => ((candidates s).map (fun c => (c.selectedPrefix.map h).prod *
        coarseTupleOwnCubeDifference e chi m omega J4 cap4 J5 cap5 N cap
          (primeHistoryTuple 5 c.selectedPrefix))).sum)).sum := by
    congr 1
    apply List.map_congr_left
    intro s hs
    congr 1
    apply List.map_congr_left
    intro c hc
    have hlen := (actualPrimeNextSelection_geometry 4 parent N cap z s hs c hc).1
    rw [coarseTupleOwnCubeDifference_history e chi m omega J4 cap4 J5 cap5 N cap _ hlen]
    dsimp [h, residual]
    ring
  rw [heq]
  exact actualPrimeFrontier_candidates_weighted_sum_eq_tuple_sum 4 parent h N cap 0 z
    (coarseTupleOwnCubeDifference e chi m omega J4 cap4 J5 cap5 N cap)

theorem actualSaving_eq_cells (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (z : ℝ) :
    actualHistoricalFifthSaving (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ))
        (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)) N cap z *
          Real.log (N : ℝ) / singularSeries N =
      ∑ j ∈ selectedFifthCells e chi m omega J5,
        coarseCellPrimeCorrection e chi m omega J4 cap4 J5 cap5 N cap z j := by
  rw [actualSaving_eq_tupleSum]
  calc
    _ = ∑ p ∈ firstExitFrontierTuples 4
        (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
        (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          ∑ j ∈ selectedFifthCells e chi m omega J5,
            if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
              coarseTupleOwnCubeDifference e chi m omega J4 cap4 J5 cap5 N cap p else 0 := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact congrArg (fun x : ℝ => (∏ i, 1 / ((p i : ℝ) - 1)) * x)
        (coarseTupleOwnCubeDifference_eq_cell_indicators e chi m omega J4 cap4 J5 cap5 N cap p)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      rfl

theorem candidateTuple_pos (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (z : ℝ) (p : Fin 5 → ℕ)
    (hp : p ∈ firstExitFrontierTuples 4
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 z)) : ∀ i, 0 < p i := by
  have hsub := (mem_firstExitFrontierTuples_iff 4 _ _ p).mp hp
  intro i
  exact (mem_roughPrimeUniverse_prime
    (hsub.1.subset (List.mem_ofFn.mpr ⟨i, rfl⟩))).pos

theorem cellCorrection_eq_capResidualSum (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5) :
    coarseCellPrimeCorrection e chi m omega J4 cap4 J5 cap5 N cap z j =
      ∑ p ∈ firstExitFrontierTuples 4
          (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
          (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
            actualPrimeTupleOwnCubeMinus N cap (cap5 j : ℝ) p -
              actualPrimeTupleOwnCubeMinus N cap (old5 e chi m omega J4 cap4 j : ℝ) p else 0) := by
  unfold coarseCellPrimeCorrection
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
  · rw [if_pos ht, if_pos ht,
      coarseTupleOwnCubeDifference_on_cell e chi m omega J4 cap4 J5 cap5 N cap hN p
        (candidateTuple_pos e chi m omega N cap z p hp) j hj ht]
  · rw [if_neg ht, if_neg ht]

theorem coarseCellPrimeCorrection_eq_zero_of_unselected
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (z : ℝ) (j : Label5 m)
    (hj : j ∉ selectedFifthCells e chi m omega J5) :
    coarseCellPrimeCorrection e chi m omega J4 cap4 J5 cap5 N cap z j = 0 := by
  unfold coarseCellPrimeCorrection
  apply Finset.sum_eq_zero
  intro p _hp
  by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
  · rw [if_pos ht,
      coarseTupleOwnCubeDifference_on_unselected_cell e chi m omega J4 cap4 J5 cap5 N cap p j hj ht,
      mul_zero]
  · rw [if_neg ht, mul_zero]

theorem actualSaving_eq_capResidualCells (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) :
    actualHistoricalFifthSaving (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ))
        (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)) N cap z *
          Real.log (N : ℝ) / singularSeries N =
      ∑ j ∈ selectedFifthCells e chi m omega J5,
        ∑ p ∈ firstExitFrontierTuples 4
            (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
            (roughPrimeUniverse N cap 0 z),
          (∏ i, 1 / ((p i : ℝ) - 1)) *
            (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
              actualPrimeTupleOwnCubeMinus N cap (cap5 j : ℝ) p -
                actualPrimeTupleOwnCubeMinus N cap (old5 e chi m omega J4 cap4 j : ℝ) p else 0) := by
  rw [actualSaving_eq_cells]
  apply Finset.sum_congr rfl
  intro j hj
  exact cellCorrection_eq_capResidualSum e chi m omega J4 cap4 J5 cap5 N cap hN z j hj

/-- Compact positive-a tuples and the literal small-coordinate remainder
partition the SAME full candidate carrier, with both own-cube gates intact. -/
theorem cellCorrection_eq_positiveTruncation_add_smallRemainder
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (z a : ℝ) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5) :
    coarseCellPrimeCorrection e chi m omega J4 cap4 J5 cap5 N cap z j =
      (∑ p ∈ (firstExitFrontierTuples 4
          (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
          (roughPrimeUniverse N cap 0 z)).filter
            (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
            actualPrimeTupleOwnCubeMinus N cap (cap5 j : ℝ) p -
              actualPrimeTupleOwnCubeMinus N cap (old5 e chi m omega J4 cap4 j : ℝ) p else 0)) +
      ∑ p ∈ (firstExitFrontierTuples 4
          (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
          (roughPrimeUniverse N cap 0 z)).filter
            (fun p => ∃ i, actualPrimeTupleLog N p i < a),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
            actualPrimeTupleOwnCubeMinus N cap (cap5 j : ℝ) p -
              actualPrimeTupleOwnCubeMinus N cap (old5 e chi m omega J4 cap4 j : ℝ) p else 0) := by
  rw [cellCorrection_eq_capResidualSum e chi m omega J4 cap4 J5 cap5 N cap hN z j hj]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hlarge : ∀ i, a ≤ actualPrimeTupleLog N p i
  · have hsmall : ¬∃ i, actualPrimeTupleLog N p i < a := by
      rintro ⟨i, hi⟩
      exact not_lt_of_ge (hlarge i) hi
    rw [if_pos hlarge, if_neg hsmall, add_zero]
  · have hsmall : ∃ i, actualPrimeTupleLog N p i < a := by
      simpa only [not_forall, not_le] using hlarge
    rw [if_neg hlarge, if_pos hsmall, zero_add]

end P1OriginalCoarseFifthResidual

end

end ImbalancedChen
