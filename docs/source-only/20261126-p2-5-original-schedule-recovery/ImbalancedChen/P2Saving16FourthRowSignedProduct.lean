import ImbalancedChen.P2Saving16ThirdRowFourthParent
import ImbalancedChen.P2Saving16ActualCompilerDifference

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED. The fourth original row on
its worst fine-cell corner, with the actual same-beta signed product. -/
namespace ImbalancedChen.P2Saving16FourthRowSignedProduct
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AFull87SamePieceCapVariation (coord_ancestor)
open P4AFull87CompilerChangedPartition P4AUpperTaggedFrozenAdmissionCatalogue
open P2CanonicalWallFullResidualPayment
open P4AOrderedThirdEighthTrimProgram
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P2OriginalSaving16Full87SourceBinding (sourceCell)
open P4AOriginalOrderedThirdActualCoefficient (keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P2Saving16FirstRowCompilerFibre P2Saving16ThirdRowFourthParent

/-- The first lower and second upper endpoints of the actual labels. -/
def firstLower (N : ℕ) (tau : ℝ) (d : ℕ) : ℝ :=
  (P2LowerFiniteCellRounding.primeLabel N tau (canonicalPrefix 8 d 0) : ℝ) * tau

def secondUpper (N : ℕ) (tau : ℝ) (d : ℕ) : ℝ :=
  ((P2LowerFiniteCellRounding.primeLabel N tau (canonicalPrefix 8 d 1) : ℝ) + 1) * tau

/-- Original fourth row in each of the fourteen ordered tables. -/
theorem original_fourth_row (i : Fin 14) (t : Fin 8 → ℝ) :
    (rowForm (sourceCell i) (3 : Fin 96)).eval t = t 0 - t 1 := by
  fin_cases i <;>
    norm_num [rowForm, rowCoeffs, sourceCell,
      P4AOriginalRemainingEighthSources.row, P4AOriginalRemainingEighthSources.rowCount,
      P4AOriginalFull87StrictActionTrim.rowCount,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P1FiniteAffineDecisionProgram.Affine.eval, Fin.sum_univ_succ] <;> ring

theorem fourth_row_margin (i : Fin 14) (delta : ℝ) (t : Fin 8 → ℝ)
    (ht : t ∈ trim (sourceCell i) delta) : delta ≤ t 0 - t 1 := by
  have hp := (trim_exact delta (sourceCell i) t).mpr ht
  simp only [trimTests, passed_append, passed_indexed, Finset.mem_univ,
    true_implies, holds_LE, Program.eval, Affine.eval_const] at hp
  have h := hp.1.2 (3 : Fin 96)
  simpa only [original_fourth_row] using h

/-- The strict row holds at its worst closed corner. Equality in the
width condition is allowed because the label's upper endpoint is strict. -/
theorem fourth_row_worst_corner (i : Fin 14) (N d : ℕ) (tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 2 * tau ≤ delta)
    (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) delta) :
    0 < firstLower N tau d - secondUpper N tau d := by
  have hm := fourth_row_margin i delta (firstEightCoordinates N d) htrim
  have h0 := (P2LowerFiniteCellRounding.primeLabel_halfopen N htau (canonicalPrefix 8 d 0)).2
  have h1 := (P2LowerFiniteCellRounding.primeLabel_halfopen N htau (canonicalPrefix 8 d 1)).1
  have he0 : firstEightCoordinates N d 0 =
      Real.log (canonicalPrefix 8 d 0 : ℝ) / Real.log (N : ℝ) := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank]
    rfl
  have he1 : firstEightCoordinates N d 1 =
      Real.log (canonicalPrefix 8 d 1 : ℝ) / Real.log (N : ℝ) := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank]
    rfl
  rw [← he0] at h0
  rw [← he1] at h1
  dsimp only [firstLower, secondUpper]
  linarith

/-- The row also holds for every y in the same actual untagged fibre. -/
theorem fourth_row_on_fibre
    (i : Fin 14) (N : ℕ) (w tau delta : ℝ) (htau : 0 < tau) (hwidth : 2 * tau ≤ delta)
    {x y : ℕ} (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) delta)
    (hy : y ∈ cell (fun _ => []) N N w (cutoff N) tau x) :
    0 < (rowForm (sourceCell i) (3 : Fin 96)).eval (firstEightCoordinates N y) := by
  have hyrank : 8 ≤ y.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hy]
    exact hrank
  have h0 : |firstEightCoordinates N x 0 - firstEightCoordinates N y 0| < tau := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank, coord_ancestor hyrank]
    exact same_primeLabel_coordinate_distance_lt N htau
      (cell_canonicalPrefix_label_eq _ _ _ _ _ _ hy hrank (0 : Fin 8))
  have h1 : |firstEightCoordinates N x 1 - firstEightCoordinates N y 1| < tau := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank, coord_ancestor hyrank]
    exact same_primeLabel_coordinate_distance_lt N htau
      (cell_canonicalPrefix_label_eq _ _ _ _ _ _ hy hrank (1 : Fin 8))
  have hm := fourth_row_margin i delta (firstEightCoordinates N x) htrim
  have h0' := (abs_lt.mp h0).2
  have h1' := (abs_lt.mp h1).1
  rw [original_fourth_row]
  linarith

/-- Same source witness, same physical full modulus and the existing
same-beta R17 signed product decomposition. No PP is assumed. -/
theorem fourth_row_same_beta_signed_product
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta ^ 2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (htau : 0 < tau) (hwidth : 2 * tau ≤ width r)
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
    0 < firstLower N tau x - secondUpper N tau x ∧
    0 < (rowForm (sourceCell i) (3 : Fin 96)).eval (firstEightCoordinates N y) ∧
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
  have hyu : y ∈ universe N N ((N : ℝ) ^ (nu * beta ^ 2)) (cutoff N) :=
    (Finset.mem_filter.mp hy).1
  have hcoeff := P2Saving16ActualCompilerDifference.r17_actual_coefficient_at_product
    r n e q a nu beta tau he hcut hh N hN hb hyu
  refine ⟨fourth_row_worst_corner i N x tau (width r) htau hwidth hrank htrim,
    fourth_row_on_fibre i N ((N : ℝ) ^ (nu * beta ^ 2)) tau (width r) htau hwidth hrank htrim hy,
    actual_fourth_le_sixth_parent r n e q a (nu * beta ^ 2) he hcut hh N hN i x hrank htrim, ?_⟩
  exact congrArg (fun v : ℝ => v * G (b * y)) hcoeff

end
end ImbalancedChen.P2Saving16FourthRowSignedProduct
