import ImbalancedChen.P2Saving16SevenOrderRowsCarrier

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED. The four original odd-history
rows on a fine box, coupled to the same actual compiled product. -/
namespace ImbalancedChen.P2Saving16FourHistoryRows
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AFull87SamePieceCapVariation (coord_ancestor)
open P4AFull87CompilerChangedPartition P4AUpperTaggedFrozenAdmissionCatalogue
open P2CanonicalWallFullResidualPayment
open P4AOrderedThirdEighthTrimProgram
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87HistoryCore (width oldHistory)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P2OriginalSaving16Full87SourceBinding (sourceCell)
open P4AOriginalOrderedThirdActualCoefficient (keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P2Saving16FirstRowCompilerFibre P2Saving16SevenOrderRowsCarrier

def historyRow (j : Fin 4) : Fin 96 := ⟨10 + j.val, by omega⟩

/-- The literal four descending affine slacks, retaining their order. -/
def historyExpr (j : Fin 4) (t : Fin 8 → ℝ) : ℝ :=
  ![57/64 - 3*t 0 - (3/2)*t 1 - (3/2)*t 2,
    57/64 - t 0 - (5/2)*t 1 - (9/2)*t 2,
    57/64 - t 0 - (5/2)*t 1 - (5/2)*t 2 - t 3 - 3*t 4,
    57/64 - t 0 - (5/2)*t 1 - (5/2)*t 2 - t 3 - t 4 - t 5 - 3*t 6] j

/-- Actual original rows 10,11,12,13, not a sorted or deduplicated list. -/
theorem original_history_row (i : Fin 14) (j : Fin 4) (t : Fin 8 → ℝ) :
    (rowForm (sourceCell i) (historyRow j)).eval t = historyExpr j t := by
  fin_cases j <;> fin_cases i <;>
    norm_num [historyRow, historyExpr, rowForm, rowCoeffs, sourceCell,
      P4AOriginalRemainingEighthSources.row, P4AOriginalRemainingEighthSources.rowCount,
      P4AOriginalFull87StrictActionTrim.rowCount,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P1FiniteAffineDecisionProgram.Affine.eval, Fin.sum_univ_succ] <;> ring

/-- Each literal row is comparison cap minus the corresponding original
odd-history expression; this is not an actual fourth-parent equality. -/
theorem history_row_is_comparison_minus_old (i : Fin 14) (j : Fin 4) (t : Fin 8 → ℝ) :
    (rowForm (sourceCell i) (historyRow j)).eval t =
      P4AOriginalFull87SourceDictionary.comparison (sourceCell i) t - oldHistory t j := by
  rw [original_history_row]
  fin_cases j <;>
    simp [historyExpr, sourceCell, P4AOriginalFull87SourceDictionary.comparison,
      P4AOriginalRemainingEighthSources.comparison, oldHistory,
      P4AOriginalRemainingEighthSources.history, VariableEnvelope.C] <;> ring

theorem history_row_margin (i : Fin 14) (j : Fin 4) (delta : ℝ) (t : Fin 8 → ℝ)
    (ht : t ∈ trim (sourceCell i) delta) : delta ≤ historyExpr j t := by
  have hp := (trim_exact delta (sourceCell i) t).mpr ht
  simp only [trimTests, passed_append, passed_indexed, Finset.mem_univ,
    true_implies, holds_LE, Program.eval, Affine.eval_const] at hp
  have h := hp.1.2 (historyRow j)
  simpa only [original_history_row] using h

/-- The coefficient sums are 6, 8, 10 and 12. Only coordinate upper
bounds are needed, and `12*tau<delta` preserves strictness. -/
theorem history_rows_of_coordinate_upper (i : Fin 14) (delta tau : ℝ)
    (htau : 0 < tau) (hwidth : 12 * tau < delta) (t u : Fin 8 → ℝ)
    (ht : t ∈ trim (sourceCell i) delta) (hu : ∀ k : Fin 8, u k ≤ t k + tau) :
    ∀ j : Fin 4, 0 < (rowForm (sourceCell i) (historyRow j)).eval u := by
  intro j
  have hm := history_row_margin i j delta t ht
  have h0 := hu 0
  have h1 := hu 1
  have h2 := hu 2
  have h3 := hu 3
  have h4 := hu 4
  have h5 := hu 5
  have h6 := hu 6
  rw [original_history_row]
  fin_cases j <;> norm_num [historyExpr] at hm ⊢ <;> linarith

/-- All original odd-history rows remain strict at every point of the
same closed label box; the displayed direction is history < comparison. -/
theorem four_history_rows_on_closed_box (i : Fin 14) (N d : ℕ) (tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 12 * tau < delta)
    (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) delta)
    (u : Fin 8 → ℝ)
    (hu : ∀ k : Fin 8, slotLower N tau d k ≤ u k ∧ u k ≤ slotUpper N tau d k) :
    ∀ j : Fin 4, oldHistory u j < P4AOriginalFull87SourceDictionary.comparison (sourceCell i) u := by
  have hup : ∀ k : Fin 8, u k ≤ firstEightCoordinates N d k + tau := by
    intro k
    have hl := (P2LowerFiniteCellRounding.primeLabel_halfopen N htau (canonicalPrefix 8 d k)).1
    have he : firstEightCoordinates N d k =
        Real.log (canonicalPrefix 8 d k : ℝ) / Real.log (N : ℝ) := by
      dsimp only [firstEightCoordinates]
      rw [coord_ancestor hrank]
      rfl
    rw [← he] at hl
    have hk := (hu k).2
    dsimp only [slotUpper] at hk
    linarith
  have hh := history_rows_of_coordinate_upper i delta tau htau hwidth
    (firstEightCoordinates N d) u htrim hup
  intro j
  have hj := hh j
  rw [history_row_is_comparison_minus_old] at hj
  linarith

/-- The same four literal rows stay strict on every actual fibre member. -/
theorem four_history_rows_on_fibre (i : Fin 14) (N : ℕ) (w tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 12 * tau < delta) {x y : ℕ}
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) delta)
    (hy : y ∈ cell (fun _ => []) N N w (cutoff N) tau x) :
    ∀ j : Fin 4, 0 < (rowForm (sourceCell i) (historyRow j)).eval (firstEightCoordinates N y) := by
  have hyrank : 8 ≤ y.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hy]
    exact hrank
  have hu : ∀ k : Fin 8, firstEightCoordinates N y k ≤ firstEightCoordinates N x k + tau := by
    intro k
    have hc : |firstEightCoordinates N x k - firstEightCoordinates N y k| < tau := by
      dsimp only [firstEightCoordinates]
      rw [coord_ancestor hrank, coord_ancestor hyrank]
      exact same_primeLabel_coordinate_distance_lt N htau
        (cell_canonicalPrefix_label_eq _ _ _ _ _ _ hy hrank k)
    have h := (abs_lt.mp hc).1
    linarith
  exact history_rows_of_coordinate_upper i delta tau htau hwidth
    (firstEightCoordinates N x) (firstEightCoordinates N y) htrim hu

/-- Same witness, four history rows, existing seven order rows, physical
Q membership, actual fourth exponent and the same signed beta product. -/
theorem four_history_rows_same_Q_signed_product
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta ^ 2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (htau : 0 < tau) (hwidth : 12 * tau < width r)
    (i : Fin 14) {x y b : ℕ}
    (hx : x ∈ universe N N ((N : ℝ) ^ (nu * beta ^ 2)) (cutoff N))
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) (width r))
    (hy : y ∈ cell (fun _ => []) N N ((N : ℝ) ^ (nu * beta ^ 2)) (cutoff N) tau x)
    (hb : b ∈ actualSmallRosserSupport N N ((N : ℝ) ^ (nu * beta ^ 2))) (G : ℕ → ℝ) :
    let omega := nu * beta ^ 2
    let w := (N : ℝ) ^ omega
    let z := cutoff N
    let L := (N : ℝ) ^ (nu * beta)
    let f := keep r n e q a omega N
    let word := rosserAncestor 8 x.primeFactorsList
    let bank := P4AOriginalFull87UnionHistory.bank e q a
    (∀ u : Fin 8 → ℝ, (∀ k : Fin 8, slotLower N tau x k ≤ u k ∧ u k ≤ slotUpper N tau x k) →
      ∀ j : Fin 4, oldHistory u j < P4AOriginalFull87SourceDictionary.comparison (sourceCell i) u) ∧
    (∀ j : Fin 4, 0 < (rowForm (sourceCell i) (historyRow j)).eval (firstEightCoordinates N y)) ∧
    (∀ j : Fin 7, 0 < (rowForm (sourceCell i) (orderRow j)).eval (firstEightCoordinates N y)) ∧
    b * y ∈ P4AOriginalFull87CompiledCounting.moduli N w ∧
    P4AOriginalFull87DataPolicy.level4Exponent n bank N (rosserAncestor 4 word) ≤
      P4AOriginalR17EighthParent.parent n e q a omega N word ∧
    P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L (b * y) * G (b * y) =
      (actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L (b * y) -
        (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L (b * y) -
         actualSmallRoughRho (policy (width r) n e q a N false) N N w z L (b * y)) +
       (if changed f (fun _ => []) N N w z tau y then
        (if 0 ≤ (ArithmeticFunction.moebius y : ℝ) then actualSmallRosserPlus N N w L b
         else actualSmallRosserMinus N N w L b)
       else 0)) * G (b * y) := by
  have hsmall : 2 * tau ≤ width r := by linarith
  have hs := seven_rows_same_Q_signed_product r n e q a nu beta tau he hcut hh
    N hN htau hsmall i hx hrank htrim hy hb G
  refine ⟨fun u hu => four_history_rows_on_closed_box i N x tau (width r) htau hwidth hrank htrim u hu,
    four_history_rows_on_fibre i N ((N : ℝ) ^ (nu * beta ^ 2)) tau (width r) htau hwidth hrank htrim hy,
    hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2⟩

end
end ImbalancedChen.P2Saving16FourHistoryRows
