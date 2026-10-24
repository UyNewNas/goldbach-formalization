import ImbalancedChen.HistoricalPrefixCertificate
import ImbalancedChen.FirstExitAdmittedFrontierTuples
import ImbalancedChen.ActualOwnCubeTupleDictionary

/-!
# Fourth residual dictionary on the actual historical third parent

All four primes have passed the historical third-capped policy.  The
fourth saving compares upper residuals, old third ancestor minus new fourth
level.  The carrier is `firstExitAdmittedTuples 4`, not the untested next
candidate carrier used for the fifth saving.  These are exact finite
identities; no mean value or integral convergence is postulated.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- Actual normalized upper residual, at the literal natural tuple product
and last selected prime.  No extra own-cube gate is inserted. -/
def fourthTuplePlusResidualP1 (N cap : ℕ) (lambda : ℝ) (p : Fin 4 → ℕ) : ℝ :=
  actualSmallRosserPlusDensity N cap (p (Fin.last 3) : ℝ)
      ((N : ℝ) ^ lambda / (∏ i, p i : ℕ)) *
    Real.log (N : ℝ) / singularSeries N

/-- Rank four has positive mass and an upper residual. -/
theorem actualFrozenFrontierDensityTerm_four_eq_plusP1
    (N cap : ℕ) (Q : List ℕ → ℝ) (history : List ℕ)
    (hlen : history.length = 4) :
    actualFrozenFrontierDensityTerm false N cap Q history =
      (history.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
        actualSmallRosserPlusDensity N cap (history.headD 0 : ℝ)
          (Q history / (history.prod : ℝ)) := by
  unfold actualFrozenFrontierDensityTerm
  rw [signedTreeCoefficient_evenListLength_eq_negOnePow, hlen]
  norm_num [ordinaryRosserResidualLower, hlen]

namespace HistoricalPrefixCapData

/-- Old effective third level minus the fourth level on the same tuple. -/
def fourthTupleResidualDifferenceP1 (D : HistoricalPrefixCapData)
    (N cap : ℕ) (p : Fin 4 → ℕ) : ℝ :=
  fourthTuplePlusResidualP1 N cap
      (D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4)
        (actualPrimeTupleLog N p)) : ℝ) p -
    fourthTuplePlusResidualP1 N cap
      (D.exponent4 (actualPrimeTupleLog N p) : ℝ) p

/-- The actual T3 frontier, including all inherited third histories. -/
def fourthPrimeCorrectionP1 (D : HistoricalPrefixCapData) (N cap : ℕ) : ℝ :=
  ∑ p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
    (∏ i, 1 / ((p i : ℝ) - 1)) * D.fourthTupleResidualDifferenceP1 N cap p

/-- A half-open fourth cell cuts the same admitted historical frontier. -/
def fourthCellPrimeCorrectionP1 (D : HistoricalPrefixCapData)
    (N cap : ℕ) (j : Fin 4 → Fin (D.m + 1)) : ℝ :=
  ∑ p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
        then D.fourthTupleResidualDifferenceP1 N cap p else 0)

theorem fourthTupleResidualDifference_on_cellP1 (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4)
    (p : Fin 4 → ℕ)
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.fourthTupleResidualDifferenceP1 N cap p =
      fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p -
        fourthTuplePlusResidualP1 N cap (D.cap4 j : ℝ) p := by
  unfold fourthTupleResidualDifferenceP1
  rw [D.exponent4_on_cell hab _ j ht,
    D.exponent3_on_cell hab _ _
      (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht)]
  simp only [cell4, if_pos hj, old4]

theorem fourthTupleResidualDifference_on_unselected_cellP1
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∉ D.cells4)
    (p : Fin 4 → ℕ)
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.fourthTupleResidualDifferenceP1 N cap p = 0 := by
  unfold fourthTupleResidualDifferenceP1
  rw [D.exponent4_on_cell hab _ j ht,
    D.exponent3_on_cell hab _ _
      (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht)]
  simp only [cell4, if_neg hj, old4, sub_self]

/-- Outside selected fourth cells the effective third ancestor survives
exactly, without a discrete boundary remainder. -/
theorem fourthTupleResidualDifference_outsideP1 (D : HistoricalPrefixCapData)
    (N cap : ℕ) (p : Fin 4 → ℕ)
    (hout : ∀ j ∈ D.cells4, actualPrimeTupleLog N p ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.fourthTupleResidualDifferenceP1 N cap p = 0 := by
  unfold fourthTupleResidualDifferenceP1
  rw [D.exponent4_outside _ hout, sub_self]

theorem fourthTupleResidualDifference_eq_cell_indicatorsP1
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N cap : ℕ) (p : Fin 4 → ℕ) :
    D.fourthTupleResidualDifferenceP1 N cap p =
      ∑ j ∈ D.cells4,
        if actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
          then D.fourthTupleResidualDifferenceP1 N cap p else 0 := by
  have h := D.exponent4_apply_sub hab (actualPrimeTupleLog N p)
    (fun lambda => -fourthTuplePlusResidualP1 N cap (lambda : ℝ) p)
  simp only [neg_sub_neg] at h
  calc
    _ = ∑ j ∈ D.cells4,
        if actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p -
            fourthTuplePlusResidualP1 N cap (D.cap4 j : ℝ) p else 0 := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases ht : actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
      · rw [if_pos ht, if_pos ht]
        exact (D.fourthTupleResidualDifference_on_cellP1 hab N cap j hj p ht).symm
      · rw [if_neg ht, if_neg ht]

theorem fourthCellPrimeCorrection_eq_zero_of_not_memP1
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∉ D.cells4) :
    D.fourthCellPrimeCorrectionP1 N cap j = 0 := by
  unfold fourthCellPrimeCorrectionP1
  apply Finset.sum_eq_zero
  intro p _hp
  by_cases ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
  · rw [if_pos ht,
      D.fourthTupleResidualDifference_on_unselected_cellP1 hab N cap j hj p ht, mul_zero]
  · rw [if_neg ht, mul_zero]

/-- Both residual sums retain exactly the same admitted T3 tuples and the
same half-open cell, while their quotient levels are kept distinct. -/
theorem fourthCellPrimeCorrection_eq_residual_sumsP1
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4) :
    D.fourthCellPrimeCorrectionP1 N cap j =
      (∑ p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
          (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈
              logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
            fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p else 0)) -
      (∑ p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
          (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈
              logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
            fourthTuplePlusResidualP1 N cap (D.cap4 j : ℝ) p else 0)) := by
  rw [← Finset.sum_sub_distrib]
  unfold fourthCellPrimeCorrectionP1
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
  · rw [if_pos ht, if_pos ht, if_pos ht,
      D.fourthTupleResidualDifference_on_cellP1 hab N cap j hj p ht]
    ring
  · rw [if_neg ht, if_neg ht, if_neg ht]
    ring

/-- Exact finite partition on the original T3 parent. -/
theorem fourthPrimeCorrection_eq_cellsP1 (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ) :
    D.fourthPrimeCorrectionP1 N cap =
      ∑ j ∈ D.cells4, D.fourthCellPrimeCorrectionP1 N cap j := by
  calc
    _ = ∑ p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          ∑ j ∈ D.cells4,
            if actualPrimeTupleLog N p ∈
                logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
              then D.fourthTupleResidualDifferenceP1 N cap p else 0 := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact congrArg (fun x : ℝ => (∏ i, 1 / ((p i : ℝ) - 1)) * x)
        (D.fourthTupleResidualDifference_eq_cell_indicatorsP1 hab N cap p)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      rfl

/-- The reverse-history dictionary preserves the cutoff, natural product,
and effective third ancestor separately from the fourth replacement. -/
theorem fourthTupleResidualDifference_historyP1 (D : HistoricalPrefixCapData)
    (N cap : ℕ) (history : List ℕ) (hlen : history.length = 4) :
    D.fourthTupleResidualDifferenceP1 N cap (primeHistoryTuple 4 history) =
      (actualSmallRosserPlusDensity N cap (history.headD 0 : ℝ)
          (D.level3 (N : ℝ) (rosserAncestor 3 history) / (history.prod : ℝ)) -
        actualSmallRosserPlusDensity N cap (history.headD 0 : ℝ)
          (D.level4 (N : ℝ) history / (history.prod : ℝ))) *
        Real.log (N : ℝ) / singularSeries N := by
  have hcoords : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 history) =
      historicalPrefixProject (by omega : 3 ≤ 4)
        (actualPrimeTupleLog N (primeHistoryTuple 4 history)) := by
    rw [primeHistoryLogCoordinates_eq_historicalPrefixProject
      (N : ℝ) (by omega : 3 ≤ 4) hlen,
      primeHistoryLogCoordinates_eq_actualPrimeTupleLog]
  unfold fourthTupleResidualDifferenceP1 fourthTuplePlusResidualP1 level3 level4
  simp only [hcoords, primeHistoryLogCoordinates_eq_actualPrimeTupleLog,
    primeHistoryTuple_last (k := 3) hlen, primeHistoryTuple_prod hlen]
  ring

/-- Exact normalization and tuple reindexing at any outer rough cutoff.
No cap coverage, level check, or limiting hypothesis is required. -/
theorem actualHistoricalFourthSaving_eq_tupleSum_at_cutoffP1
    (D : HistoricalPrefixCapData) (N cap : ℕ) (z : ℝ) :
    actualHistoricalFourthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z *
        Real.log (N : ℝ) / singularSeries N =
      ∑ p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) * D.fourthTupleResidualDifferenceP1 N cap p := by
  let parent := D.upperThirdPolicy (N : ℝ)
  let h (q : ℕ) := 1 / ((q : ℝ) - 1)
  let states := firstExitDepthFrontier 4 parent h [] true 1 (roughPrimeUniverse N cap 0 z)
  have hn : actualHistoricalFourthSaving
      (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
      (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z *
      Real.log (N : ℝ) / singularSeries N =
      (states.map (fun s =>
        (actualFrozenFrontierDensityTerm false N cap
            (fun pre => D.level3 (N : ℝ) (rosserAncestor 3 pre)) s.selectedPrefix -
          actualFrozenFrontierDensityTerm false N cap (D.level4 (N : ℝ))
            s.selectedPrefix) * (Real.log (N : ℝ) / singularSeries N))).sum := by
    simp only [List.sum_map_mul_right]
    change _ * Real.log (N : ℝ) / singularSeries N =
      actualHistoricalFourthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z *
        (Real.log (N : ℝ) / singularSeries N)
    ring
  rw [hn]
  have heq : (states.map (fun s =>
        (actualFrozenFrontierDensityTerm false N cap
            (fun pre => D.level3 (N : ℝ) (rosserAncestor 3 pre)) s.selectedPrefix -
          actualFrozenFrontierDensityTerm false N cap (D.level4 (N : ℝ))
            s.selectedPrefix) * (Real.log (N : ℝ) / singularSeries N))).sum =
      (states.map (fun s => (s.selectedPrefix.map h).prod *
        D.fourthTupleResidualDifferenceP1 N cap (primeHistoryTuple 4 s.selectedPrefix))).sum := by
    congr 1
    apply List.map_congr_left
    intro s hs
    have hlen : s.selectedPrefix.length = 4 :=
      firstExitDepthFrontier_selected_length 4 parent h []
        (roughPrimeUniverse N cap 0 z) true 1 (by simp) s hs
    rw [actualFrozenFrontierDensityTerm_four_eq_plusP1 N cap _ _ hlen,
      actualFrozenFrontierDensityTerm_four_eq_plusP1 N cap _ _ hlen,
      D.fourthTupleResidualDifference_historyP1 N cap _ hlen]
    dsimp [h]
    ring
  rw [heq]
  exact firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 4 parent h
    (roughPrimeUniverse N cap 0 z) (roughPrimeUniverse_nodup N cap 0 z)
    (D.fourthTupleResidualDifferenceP1 N cap)

theorem actualHistoricalFourthSaving_eq_fourthPrimeCorrectionP1
    (D : HistoricalPrefixCapData) (N cap : ℕ) :
    actualHistoricalFourthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ))
        N cap ((N : ℝ) ^ (D.b : ℝ)) *
        Real.log (N : ℝ) / singularSeries N = D.fourthPrimeCorrectionP1 N cap := by
  simpa only [fourthPrimeCorrectionP1] using
    D.actualHistoricalFourthSaving_eq_tupleSum_at_cutoffP1 N cap ((N : ℝ) ^ (D.b : ℝ))

theorem actualHistoricalFourthSaving_eq_cellsP1
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (N cap : ℕ) :
    actualHistoricalFourthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ))
        N cap ((N : ℝ) ^ (D.b : ℝ)) *
        Real.log (N : ℝ) / singularSeries N =
      ∑ j ∈ D.cells4, D.fourthCellPrimeCorrectionP1 N cap j := by
  rw [D.actualHistoricalFourthSaving_eq_fourthPrimeCorrectionP1,
    D.fourthPrimeCorrection_eq_cellsP1 hab]

/-- Finite historical level checks identify the actual policy saving. -/
theorem upperThirdToFourthSaving_eqP1 (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    firstExitRetainedPolynomial (D.upperThirdPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z := by
  apply actualHistoricalFourthSaving_eq
  intro state hstate
  apply D.level3_ancestor_le_level4 hab hcheck (N : ℝ) hN
  exact firstExitDepthFrontier_selected_length 4 _ _ [] _ true 1 (by simp) state hstate

theorem upperThirdToFourthSaving_normalized_eq_fourthPrimeCorrectionP1
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N cap : ℕ) (hN : 1 < (N : ℝ)) :
    (firstExitRetainedPolynomial (D.upperThirdPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))) -
      firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))) *
      Real.log (N : ℝ) / singularSeries N = D.fourthPrimeCorrectionP1 N cap := by
  rw [D.upperThirdToFourthSaving_eqP1 hab hcheck N cap hN,
    D.actualHistoricalFourthSaving_eq_fourthPrimeCorrectionP1]

end HistoricalPrefixCapData

end

end ImbalancedChen
