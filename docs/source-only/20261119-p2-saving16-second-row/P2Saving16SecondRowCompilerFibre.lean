import ImbalancedChen.P2Saving16FirstRowCompilerFibre
import ImbalancedChen.P4AOriginalR17EighthParent

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
The second original row and the same actual compiler fibre. This is a
single-row endpoint statement, not the full ordered-corner comparison. -/
namespace ImbalancedChen.P2Saving16SecondRowCompilerFibre
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
open P2Saving16FirstRowCompilerFibre

/-- The lower endpoint of the third original fine-label slot. -/
def thirdLowerEndpoint (N : ℕ) (tau : ℝ) (d : ℕ) : ℝ :=
  (P2LowerFiniteCellRounding.primeLabel N tau (canonicalPrefix 8 d 2) : ℝ) * tau

/-- The second literal row, in original order, for each of the fourteen
ascending source members. -/
theorem original_second_row (i : Fin 14) (t : Fin 8 → ℝ) :
    (rowForm (sourceCell i) (1 : Fin 96)).eval t = t 2 - 1/100 := by
  fin_cases i <;>
    norm_num [rowForm, rowCoeffs, sourceCell,
      P4AOriginalRemainingEighthSources.row, P4AOriginalRemainingEighthSources.rowCount,
      P4AOriginalFull87StrictActionTrim.rowCount,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P1FiniteAffineDecisionProgram.Affine.eval, Fin.sum_univ_succ] <;> ring

/-- The original trim imposes the margin on this very row occurrence. -/
theorem second_row_margin (i : Fin 14) (delta : ℝ) (t : Fin 8 → ℝ)
    (ht : t ∈ trim (sourceCell i) delta) : delta ≤ t 2 - 1/100 := by
  have hp := (trim_exact delta (sourceCell i) t).mpr ht
  simp only [trimTests, passed_append, passed_indexed, Finset.mem_univ,
    true_implies, holds_LE, Program.eval, Affine.eval_const] at hp
  have h := hp.1.2 (1 : Fin 96)
  simpa only [original_second_row] using h

/-- The lower geometric endpoint, not just the labelled primes, lies
strictly inside the second original row. -/
theorem second_lower_endpoint_strict (i : Fin 14) (N d : ℕ) (tau delta : ℝ)
    (htau : 0 < tau) (hwidth : tau < delta) (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) delta) :
    0 < thirdLowerEndpoint N tau d - 1/100 := by
  have hm := second_row_margin i delta (firstEightCoordinates N d) htrim
  have hu := (P2LowerFiniteCellRounding.primeLabel_halfopen N htau (canonicalPrefix 8 d 2)).2
  have he : firstEightCoordinates N d 2 =
      Real.log (canonicalPrefix 8 d 2 : ℝ) / Real.log (N : ℝ) := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank]
    rfl
  rw [← he] at hu
  dsimp only [thirdLowerEndpoint]
  linarith

/-- Both original row occurrences and the literal signed full-modulus
coefficient, with one source witness and one actual compiler fibre. -/
theorem two_rows_full_modulus
    (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ)
    (tau delta L : ℝ) (htau : 0 < tau) (hwidth : tau < delta)
    (i : Fin 14) {x y b : ℕ}
    (hx : x ∈ universe N N ((N : ℝ) ^ omega) (cutoff N))
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) delta)
    (hy : y ∈ cell (fun _ => []) N N ((N : ℝ) ^ omega) (cutoff N) tau x)
    (hb : b ∈ actualSmallRosserSupport N N ((N : ℝ) ^ omega)) (G : ℕ → ℝ) :
    let f := keep r n e q a omega N
    let rough := (ArithmeticFunction.moebius y : ℝ) *
      P4AFull87TaggedAtomValue.occupied f (fun _ => []) N N ((N : ℝ) ^ omega) (cutoff N) tau x
    0 < VariableEnvelope.mu - firstUpperEndpoint N tau x ∧
    0 < thirdLowerEndpoint N tau x - 1/100 ∧
    0 < (rowForm (sourceCell i) (0 : Fin 96)).eval (firstEightCoordinates N y) ∧
    0 < (rowForm (sourceCell i) (1 : Fin 96)).eval (firstEightCoordinates N y) ∧
    P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L (b * y) * G (b * y) =
      rough * (if 0 ≤ rough then actualSmallRosserPlus N N ((N : ℝ) ^ omega) L b
        else actualSmallRosserMinus N N ((N : ℝ) ^ omega) L b) * G (b * y) := by
  have hfirst := first_row_full_modulus r n e q a omega N tau delta L htau hwidth
    i hx hrank htrim hy hb G
  have hyrank : 8 ≤ y.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hy]
    exact hrank
  have hclose : |firstEightCoordinates N x 2 - firstEightCoordinates N y 2| < tau := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank, coord_ancestor hyrank]
    exact same_primeLabel_coordinate_distance_lt N htau
      (cell_canonicalPrefix_label_eq _ _ _ _ _ _ hy hrank (2 : Fin 8))
  have hmargin := second_row_margin i delta (firstEightCoordinates N x) htrim
  have hsecond : 0 < (rowForm (sourceCell i) (1 : Fin 96)).eval (firstEightCoordinates N y) := by
    rw [original_second_row]
    have hh := (abs_lt.mp hclose).2
    linarith
  exact ⟨hfirst.1, second_lower_endpoint_strict i N x tau delta htau hwidth hrank htrim,
    hfirst.2.1, hsecond, hfirst.2.2⟩

/-- On the very same eighth history, the existing physical sixth parent
is bounded below by the inherited third scalar at its fourth ancestor.
This does not identify the actual fourth parent with that scalar. -/
theorem source_witness_inherited_parent
    (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (he : 0 ≤ e) (hcut : omega ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (i : Fin 14) (x : ℕ)
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) (width r)) :
    let word := rosserAncestor 8 x.primeFactorsList
    P5OriginalCommonRefinedConstructor.lambda3
        (P4AOriginalFull87UnionHistory.oldBank e q a) N (rosserAncestor 4 word) ≤
      P4AOriginalR17EighthParent.parent n e q a omega N word ∧
    P4AOriginalR17EighthParent.parent n e q a omega N word ≤
      P4AOriginalFull87SourceDictionary.comparison (sourceCell i) (firstEightCoordinates N x) := by
  have hlen : (rosserAncestor 8 x.primeFactorsList).length = 8 := by
    rw [rosserAncestor_length, min_eq_left hrank]
  have hp : ∀ p ∈ rosserAncestor 8 x.primeFactorsList, 0 < p := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactorsList ((List.drop_sublist _ _).subset hp)).pos
  have h := P4AOriginalR17EighthParent.compact_parent r n e q a omega he hcut hh
    N hN (rosserAncestor 8 x.primeFactorsList) hlen hp (sourceCell i) htrim
  exact ⟨h.2.1, h.2.2⟩


/-- A single actual source witness supplies both endpoint rows, the
inherited fourth-ancestor bound on its physical sixth parent, and the
signed full-modulus coefficient of a member of its compiler fibre. -/
theorem two_rows_with_inherited_parent
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
    let rough := (ArithmeticFunction.moebius y : ℝ) *
      P4AFull87TaggedAtomValue.occupied (keep r n e q a omega N) (fun _ => [])
        N N ((N : ℝ) ^ omega) (cutoff N) tau x
    0 < VariableEnvelope.mu - firstUpperEndpoint N tau x ∧
    0 < thirdLowerEndpoint N tau x - 1/100 ∧
    0 < (rowForm (sourceCell i) (0 : Fin 96)).eval (firstEightCoordinates N y) ∧
    0 < (rowForm (sourceCell i) (1 : Fin 96)).eval (firstEightCoordinates N y) ∧
    P5OriginalCommonRefinedConstructor.lambda3
        (P4AOriginalFull87UnionHistory.oldBank e q a) N (rosserAncestor 4 word) ≤
      P4AOriginalR17EighthParent.parent n e q a omega N word ∧
    P4AOriginalR17EighthParent.parent n e q a omega N word ≤
      P4AOriginalFull87SourceDictionary.comparison (sourceCell i) (firstEightCoordinates N x) ∧
    P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L (b * y) * G (b * y) =
      rough * (if 0 ≤ rough then actualSmallRosserPlus N N ((N : ℝ) ^ omega) L b
        else actualSmallRosserMinus N N ((N : ℝ) ^ omega) L b) * G (b * y) := by
  have hf := two_rows_full_modulus r n e q a omega N tau (width r) L htau hwidth
    i hx hrank htrim hy hb G
  have hp := source_witness_inherited_parent r n e q a omega he hcut hh N hN i x hrank htrim
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hp.1, hp.2, hf.2.2.2.2⟩

end
end ImbalancedChen.P2Saving16SecondRowCompilerFibre
