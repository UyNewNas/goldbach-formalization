import ImbalancedChen.P2Saving16SecondRowCompilerFibre

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED. The third ordered row and the
actual level-four exponent on the same eighth history. No PP estimate. -/
namespace ImbalancedChen.P2Saving16ThirdRowFourthParent
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AFull87SamePieceCapVariation (coord_ancestor)
open P4AFull87CompilerChangedPartition P4AUpperTaggedFrozenAdmissionCatalogue
open P2CanonicalWallFullResidualPayment
open P4AOrderedThirdEighthTrimProgram
open P4AOriginalFull87StrictActionTrim (trim trim_subset_source)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P2OriginalSaving16Full87SourceBinding (sourceCell)
open P4AOriginalOrderedThirdActualCoefficient (keep)
open P4AOriginalFull87RawChronology (cutoff)
open P2Saving16FirstRowCompilerFibre P2Saving16SecondRowCompilerFibre

/-- Lower endpoint of the eighth original fine-label slot. -/
def eighthLowerEndpoint (N : ℕ) (tau : ℝ) (d : ℕ) : ℝ :=
  (P2LowerFiniteCellRounding.primeLabel N tau (canonicalPrefix 8 d 7) : ℝ) * tau

/-- Row number 2 is the original strict last-prime threshold. -/
theorem original_third_row (i : Fin 14) (t : Fin 8 → ℝ) :
    (rowForm (sourceCell i) (2 : Fin 96)).eval t = t 7 - 53/13824 := by
  fin_cases i <;>
    norm_num [rowForm, rowCoeffs, sourceCell,
      P4AOriginalRemainingEighthSources.row, P4AOriginalRemainingEighthSources.rowCount,
      P4AOriginalFull87StrictActionTrim.rowCount,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P1FiniteAffineDecisionProgram.Affine.eval, Fin.sum_univ_succ] <;> ring

theorem third_row_margin (i : Fin 14) (delta : ℝ) (t : Fin 8 → ℝ)
    (ht : t ∈ trim (sourceCell i) delta) : delta ≤ t 7 - 53/13824 := by
  have hp := (trim_exact delta (sourceCell i) t).mpr ht
  simp only [trimTests, passed_append, passed_indexed, Finset.mem_univ,
    true_implies, holds_LE, Program.eval, Affine.eval_const] at hp
  have h := hp.1.2 (2 : Fin 96)
  simpa only [original_third_row] using h

theorem eighth_lower_endpoint_strict (i : Fin 14) (N d : ℕ) (tau delta : ℝ)
    (htau : 0 < tau) (hwidth : tau < delta) (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) delta) :
    0 < eighthLowerEndpoint N tau d - 53/13824 := by
  have hm := third_row_margin i delta (firstEightCoordinates N d) htrim
  have hu := (P2LowerFiniteCellRounding.primeLabel_halfopen N htau (canonicalPrefix 8 d 7)).2
  have he : firstEightCoordinates N d 7 =
      Real.log (canonicalPrefix 8 d 7 : ℝ) / Real.log (N : ℝ) := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank]
    rfl
  rw [← he] at hu
  dsimp only [eighthLowerEndpoint]
  linarith

/-- The actual fourth-layer exponent of the same eighth source word is
below the physical sixth parent. This is an order bound; it does not
identify their full-q signed coefficients. -/
theorem actual_fourth_le_sixth_parent
    (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (he : 0 ≤ e) (hcut : omega ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (i : Fin 14) (x : ℕ)
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) (width r)) :
    let word := rosserAncestor 8 x.primeFactorsList
    let d := P4AOriginalFull87UnionHistory.bank e q a
    P4AOriginalFull87DataPolicy.level4Exponent n d N (rosserAncestor 4 word) ≤
      P4AOriginalR17EighthParent.parent n e q a omega N word := by
  let word := rosserAncestor 8 x.primeFactorsList
  let d := P4AOriginalFull87UnionHistory.bank e q a
  have hlen : word.length = 8 := by
    dsimp only [word]
    rw [rosserAncestor_length, min_eq_left hrank]
  have hp : ∀ p ∈ word, 0 < p := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactorsList ((List.drop_sublist _ _).subset hp)).pos
  have hs := trim_subset_source (sourceCell i) (width_pos r) htrim
  have hr := hh N hN word hlen hp (sourceCell i) htrim
  have ha := P4AOriginalFull87UnionHistory.source_active hlen hs hr
  have ha4 : P4AOriginalFull87DataPolicy.active d N (rosserAncestor 4 word) :=
    (P4AOriginalFull87DataPolicy.active_ancestor d N 4 (by decide) word).mpr ha
  have ha6 : P4AOriginalFull87DataPolicy.active d N (rosserAncestor 6 word) :=
    (P4AOriginalFull87DataPolicy.active_ancestor d N 6 (by decide) word).mpr ha
  have h45 : P4AOriginalFull87DataPolicy.cap4 n d N (rosserAncestor 4 word) ≤
      P4AOriginalFull87DataPolicy.cap5 n d N (rosserAncestor 5 word) := by
    unfold P4AOriginalFull87DataPolicy.cap5
    rw [rosserAncestor_nested 4 5 (by decide)]
    exact le_max_left _ _
  have h56 := P4AOriginalFull87DataPolicy.cap5_le_licensed n d N (rosserAncestor 6 word)
  rw [rosserAncestor_nested 5 6 (by decide)] at h56
  have hp6 : P4AOriginalR17EighthParent.parent n e q a omega N word =
      P4AOriginalFull87DataPolicy.licensedCap n d N (rosserAncestor 6 word) := by
    rw [P4AOriginalR17EighthParent.parent_on_owner n e q a omega N he hN.le hcut word hr.2.1]
    simp only [P4AOriginalFull87UnionHistory.actualParent,
      P4AOriginalFull87DataPolicy.actualParent, P4AOriginalFull87DataPolicy.level6Exponent,
      if_pos ha6]
  change P4AOriginalFull87DataPolicy.level4Exponent n d N (rosserAncestor 4 word) ≤ _
  rw [P4AOriginalFull87DataPolicy.level4Exponent, if_pos ha4, hp6]
  exact h45.trans h56

/-- The third source-row lower endpoint and its actual fibre occurrence,
with the same signed coefficient used by the existing two-row result. -/
theorem third_row_and_signed_fibre
    (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ)
    (tau delta L : ℝ) (htau : 0 < tau) (hwidth : tau < delta)
    (i : Fin 14) {x y b : ℕ}
    (hx : x ∈ universe N N ((N : ℝ) ^ omega) (cutoff N))
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) delta)
    (hy : y ∈ cell (fun _ => []) N N ((N : ℝ) ^ omega) (cutoff N) tau x)
    (hb : b ∈ actualSmallRosserSupport N N ((N : ℝ) ^ omega)) (G : ℕ → ℝ) :
    let rough := (ArithmeticFunction.moebius y : ℝ) *
      P4AFull87TaggedAtomValue.occupied (keep r n e q a omega N) (fun _ => [])
        N N ((N : ℝ) ^ omega) (cutoff N) tau x
    0 < eighthLowerEndpoint N tau x - 53/13824 ∧
    0 < (rowForm (sourceCell i) (2 : Fin 96)).eval (firstEightCoordinates N y) ∧
    P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L (b * y) * G (b * y) =
      rough * (if 0 ≤ rough then actualSmallRosserPlus N N ((N : ℝ) ^ omega) L b
        else actualSmallRosserMinus N N ((N : ℝ) ^ omega) L b) * G (b * y) := by
  have hfirst := two_rows_full_modulus r n e q a omega N tau delta L htau hwidth
    i hx hrank htrim hy hb G
  have hyrank : 8 ≤ y.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hy]
    exact hrank
  have hclose : |firstEightCoordinates N x 7 - firstEightCoordinates N y 7| < tau := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank, coord_ancestor hyrank]
    exact same_primeLabel_coordinate_distance_lt N htau
      (cell_canonicalPrefix_label_eq _ _ _ _ _ _ hy hrank (7 : Fin 8))
  have hmargin := third_row_margin i delta (firstEightCoordinates N x) htrim
  refine ⟨eighth_lower_endpoint_strict i N x tau delta htau hwidth hrank htrim, ?_, hfirst.2.2.2.2⟩
  rw [original_third_row]
  have hh := (abs_lt.mp hclose).2
  linarith


/-- Same source witness for the fourth exponent, third row and the
actual signed full-modulus fibre coefficient. -/
theorem third_row_fourth_parent_signed
    (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (he : 0 ≤ e) (hcut : omega ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (tau L : ℝ)
    (htau : 0 < tau) (hwidth : tau < width r) (i : Fin 14) {x y b : ℕ}
    (hx : x ∈ universe N N ((N : ℝ) ^ omega) (cutoff N))
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) (width r))
    (hy : y ∈ cell (fun _ => []) N N ((N : ℝ) ^ omega) (cutoff N) tau x)
    (hb : b ∈ actualSmallRosserSupport N N ((N : ℝ) ^ omega)) (G : ℕ → ℝ) :
    let word := rosserAncestor 8 x.primeFactorsList
    let d := P4AOriginalFull87UnionHistory.bank e q a
    let rough := (ArithmeticFunction.moebius y : ℝ) *
      P4AFull87TaggedAtomValue.occupied (keep r n e q a omega N) (fun _ => [])
        N N ((N : ℝ) ^ omega) (cutoff N) tau x
    0 < eighthLowerEndpoint N tau x - 53/13824 ∧
    0 < (rowForm (sourceCell i) (2 : Fin 96)).eval (firstEightCoordinates N y) ∧
    P4AOriginalFull87DataPolicy.level4Exponent n d N (rosserAncestor 4 word) ≤
      P4AOriginalR17EighthParent.parent n e q a omega N word ∧
    P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L (b * y) * G (b * y) =
      rough * (if 0 ≤ rough then actualSmallRosserPlus N N ((N : ℝ) ^ omega) L b
        else actualSmallRosserMinus N N ((N : ℝ) ^ omega) L b) * G (b * y) := by
  have h := third_row_and_signed_fibre r n e q a omega N tau (width r) L htau hwidth
    i hx hrank htrim hy hb G
  exact ⟨h.1, h.2.1,
    actual_fourth_le_sixth_parent r n e q a omega he hcut hh N hN i x hrank htrim,
    h.2.2⟩

end
end ImbalancedChen.P2Saving16ThirdRowFourthParent
