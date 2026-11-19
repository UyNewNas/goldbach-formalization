import ImbalancedChen.P2Saving16FourHistoryRows

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED. Three original branch and cap
rows on a single fine box and the existing signed full-q product. -/
namespace ImbalancedChen.P2Saving16ThreeCapRows
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
open P2Saving16FourHistoryRows

def capRow (j : Fin 3) : Fin 96 := ⟨14 + j.val, by omega⟩

def capExpr (j : Fin 3) (t : Fin 8 → ℝ) : ℝ :=
  ![2*(t 1+t 2-VariableEnvelope.mu),
    75/256-(3/2)*t 1-(9/8)*t 2,
    -(195313/500000:ℝ)+(1/2)*t 0+(3/2)*t 1+(3/2)*t 2+(1/2)*t 7] j

/-- Original ordered source rows 14,15,16 for each of the 14 cells. -/
theorem original_cap_row (i : Fin 14) (j : Fin 3) (t : Fin 8 → ℝ) :
    (rowForm (sourceCell i) (capRow j)).eval t = capExpr j t := by
  fin_cases j <;> fin_cases i <;>
    norm_num [capRow, capExpr, rowForm, rowCoeffs, sourceCell,
      P4AOriginalRemainingEighthSources.row, P4AOriginalRemainingEighthSources.rowCount,
      P4AOriginalFull87StrictActionTrim.rowCount,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P1FiniteAffineDecisionProgram.Affine.eval, VariableEnvelope.mu, Fin.sum_univ_succ] <;> ring

/-- Preserve the original source comparisons, including their directions. -/
theorem original_cap_rows_semantics (i : Fin 14) (t : Fin 8 → ℝ) :
    (rowForm (sourceCell i) (capRow 0)).eval t = 2*(t 1+t 2-VariableEnvelope.mu) ∧
    (rowForm (sourceCell i) (capRow 1)).eval t =
      P4AOriginalFull87SourceDictionary.comparison (sourceCell i) t - VariableEnvelope.B (t 2) ∧
    (rowForm (sourceCell i) (capRow 2)).eval t =
      P4AOriginalFull87SourceDictionary.newCap (sourceCell i) t -
        P4AOriginalFull87SourceDictionary.comparison (sourceCell i) t := by
  rw [original_cap_row, original_cap_row, original_cap_row]
  norm_num [capExpr, sourceCell, P4AOriginalFull87SourceDictionary.comparison,
    P4AOriginalFull87SourceDictionary.newCap, P4AOriginalRemainingEighthSources.comparison,
    P4AOriginalRemainingEighthSources.newCap, P4AOriginalRemainingEighthSources.descendingNew,
    P4AOriginalRemainingEighthSources.selectedSum, P4AOriginalRemainingEighthSources.selected,
    P4AOriginalRemainingEighthSources.eta, VariableEnvelope.A, VariableEnvelope.B,
    VariableEnvelope.C, VariableEnvelope.cap, Fin.sum_univ_succ] <;> ring

theorem cap_row_margin (i : Fin 14) (j : Fin 3) (delta : ℝ) (t : Fin 8 → ℝ)
    (ht : t ∈ trim (sourceCell i) delta) : delta ≤ capExpr j t := by
  have hp := (trim_exact delta (sourceCell i) t).mpr ht
  simp only [trimTests, passed_append, passed_indexed, Finset.mem_univ,
    true_implies, holds_LE, Program.eval, Affine.eval_const] at hp
  have h := hp.1.2 (capRow j)
  simpa only [original_cap_row] using h

/-- Mixed signs require both coordinate directions. The coefficient
absolute sums are 4, 21/8 and 4, all bounded by the existing 12. -/
theorem cap_rows_of_coordinate_bounds (i : Fin 14) (delta tau : ℝ)
    (htau : 0 < tau) (hwidth : 12*tau < delta) (t u : Fin 8 → ℝ)
    (ht : t ∈ trim (sourceCell i) delta)
    (hl : ∀ k : Fin 8, t k - tau ≤ u k) (hu : ∀ k : Fin 8, u k ≤ t k + tau) :
    ∀ j : Fin 3, 0 < (rowForm (sourceCell i) (capRow j)).eval u := by
  intro j
  have hm := cap_row_margin i j delta t ht
  have l0 := hl 0
  have l1 := hl 1
  have l2 := hl 2
  have l7 := hl 7
  have u1 := hu 1
  have u2 := hu 2
  rw [original_cap_row]
  fin_cases j <;> norm_num [capExpr] at hm ⊢ <;> linarith

/-- All three literal rows hold at every point of the closed label box. -/
theorem three_cap_rows_on_closed_box (i : Fin 14) (N d : ℕ) (tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 12*tau < delta) (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) delta)
    (u : Fin 8 → ℝ)
    (hu : ∀ k : Fin 8, slotLower N tau d k ≤ u k ∧ u k ≤ slotUpper N tau d k) :
    ∀ j : Fin 3, 0 < (rowForm (sourceCell i) (capRow j)).eval u := by
  have hl : ∀ k : Fin 8, firstEightCoordinates N d k - tau ≤ u k := by
    intro k
    have hh := (P2LowerFiniteCellRounding.primeLabel_halfopen N htau (canonicalPrefix 8 d k)).2
    have he : firstEightCoordinates N d k =
        Real.log (canonicalPrefix 8 d k : ℝ) / Real.log (N : ℝ) := by
      dsimp only [firstEightCoordinates]
      rw [coord_ancestor hrank]
      rfl
    rw [← he] at hh
    have h := (hu k).1
    dsimp only [slotLower] at h
    linarith
  have hh : ∀ k : Fin 8, u k ≤ firstEightCoordinates N d k + tau := by
    intro k
    have hl := (P2LowerFiniteCellRounding.primeLabel_halfopen N htau (canonicalPrefix 8 d k)).1
    have he : firstEightCoordinates N d k =
        Real.log (canonicalPrefix 8 d k : ℝ) / Real.log (N : ℝ) := by
      dsimp only [firstEightCoordinates]
      rw [coord_ancestor hrank]
      rfl
    rw [← he] at hl
    have h := (hu k).2
    dsimp only [slotUpper] at h
    linarith
  exact cap_rows_of_coordinate_bounds i delta tau htau hwidth (firstEightCoordinates N d) u htrim hl hh

/-- Original semantic directions on every point of that same box. -/
theorem three_cap_semantics_on_closed_box (i : Fin 14) (N d : ℕ) (tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 12*tau < delta) (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) delta)
    (u : Fin 8 → ℝ)
    (hu : ∀ k : Fin 8, slotLower N tau d k ≤ u k ∧ u k ≤ slotUpper N tau d k) :
    P4AOriginalFull87SourceDictionary.comparison (sourceCell i) u = VariableEnvelope.v (u 1+u 2) ∧
    VariableEnvelope.B (u 2) < P4AOriginalFull87SourceDictionary.comparison (sourceCell i) u ∧
    P4AOriginalFull87SourceDictionary.comparison (sourceCell i) u <
      P4AOriginalFull87SourceDictionary.newCap (sourceCell i) u := by
  have h := three_cap_rows_on_closed_box i N d tau delta htau hwidth hrank htrim u hu
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  obtain ⟨e0,e1,e2⟩ := original_cap_rows_semantics i u
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  have hs : VariableEnvelope.mu ≤ u 1+u 2 := by linarith
  refine ⟨?_, by linarith, by linarith⟩
  rw [VariableEnvelope.v_eq_C hs]
  rfl

/-- The three original row occurrences remain strict on the actual fibre. -/
theorem three_cap_rows_on_fibre (i : Fin 14) (N : ℕ) (w tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 12*tau < delta) {x y : ℕ}
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) delta)
    (hy : y ∈ cell (fun _ => []) N N w (cutoff N) tau x) :
    ∀ j : Fin 3, 0 < (rowForm (sourceCell i) (capRow j)).eval (firstEightCoordinates N y) := by
  have hyrank : 8 ≤ y.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hy]
    exact hrank
  have hdist : ∀ k : Fin 8, |firstEightCoordinates N x k - firstEightCoordinates N y k| < tau := by
    intro k
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank, coord_ancestor hyrank]
    exact same_primeLabel_coordinate_distance_lt N htau
      (cell_canonicalPrefix_label_eq _ _ _ _ _ _ hy hrank k)
  have hl : ∀ k : Fin 8, firstEightCoordinates N x k - tau ≤ firstEightCoordinates N y k := by
    intro k
    have h := (abs_lt.mp (hdist k)).2
    linarith
  have hu : ∀ k : Fin 8, firstEightCoordinates N y k ≤ firstEightCoordinates N x k + tau := by
    intro k
    have h := (abs_lt.mp (hdist k)).1
    linarith
  exact cap_rows_of_coordinate_bounds i delta tau htau hwidth
    (firstEightCoordinates N x) (firstEightCoordinates N y) htrim hl hu

/-- One actual witness and product, retaining the earlier history rows,
physical Q, actual fourth exponent and the same sign-selected beta term. -/
theorem cap_rows_same_Q_signed_product
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta ^ 2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (htau : 0 < tau) (hwidth : 12*tau < width r)
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
      P4AOriginalFull87SourceDictionary.comparison (sourceCell i) u = VariableEnvelope.v (u 1+u 2) ∧
      VariableEnvelope.B (u 2) < P4AOriginalFull87SourceDictionary.comparison (sourceCell i) u ∧
      P4AOriginalFull87SourceDictionary.comparison (sourceCell i) u < P4AOriginalFull87SourceDictionary.newCap (sourceCell i) u) ∧
    (∀ j : Fin 3, 0 < (rowForm (sourceCell i) (capRow j)).eval (firstEightCoordinates N y)) ∧
    (∀ j : Fin 4, 0 < (rowForm (sourceCell i) (historyRow j)).eval (firstEightCoordinates N y)) ∧
    b*y ∈ P4AOriginalFull87CompiledCounting.moduli N w ∧
    P4AOriginalFull87DataPolicy.level4Exponent n bank N (rosserAncestor 4 word) ≤
      P4AOriginalR17EighthParent.parent n e q a omega N word ∧
    P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L (b*y) * G (b*y) =
      (actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L (b*y) -
        (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L (b*y) -
         actualSmallRoughRho (policy (width r) n e q a N false) N N w z L (b*y)) +
       (if changed f (fun _ => []) N N w z tau y then
        (if 0 ≤ (ArithmeticFunction.moebius y : ℝ) then actualSmallRosserPlus N N w L b
         else actualSmallRosserMinus N N w L b)
       else 0)) * G (b*y) := by
  have hs := four_history_rows_same_Q_signed_product r n e q a nu beta tau he hcut hh
    N hN htau hwidth i hx hrank htrim hy hb G
  exact ⟨fun u hu => three_cap_semantics_on_closed_box i N x tau (width r) htau hwidth hrank htrim u hu,
    three_cap_rows_on_fibre i N ((N : ℝ) ^ (nu * beta ^ 2)) tau (width r) htau hwidth hrank htrim hy,
    hs.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩

end
end ImbalancedChen.P2Saving16ThreeCapRows
