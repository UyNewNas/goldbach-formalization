import ImbalancedChen.P2Saving16ThreeCapRows

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED. The 104-row coefficient
pool gives one 12-Lipschitz bound for every ordered original 96-row
source, on the same closed box and actual signed compiler product. -/
namespace ImbalancedChen.P2Saving16All96ClosedBox
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
open P2OriginalSaving16Full87SourceBinding (sourceCell atlasCell sourceRows_iff_full87_source)
open P4AOriginalOrderedThirdActualCoefficient (keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P2Saving16FirstRowCompilerFibre P2Saving16SevenOrderRowsCarrier
open P2Saving16ThreeCapRows

/-- A closed rational coefficient-pool calculation, UNEVALUATED. -/
theorem original_pool_l1_le_twelve (m : Fin 104) :
    (∑ k : Fin 8, |(P4AOriginalAscendingFourteenAffineSource.literalPool m k.succ : ℝ)|) ≤ 12 := by
  fin_cases m <;>
    norm_num [P4AOriginalAscendingFourteenAffineSource.literalPool, Fin.sum_univ_succ]

/-- The original index is used with its full cell and occurrence index. -/
theorem original_row_l1_le_twelve (i : Fin 14) (r : Fin 96) :
    (∑ k : Fin 8, |(P4AOriginalAscendingFourteenAffineSource.rows i r k.succ : ℝ)|) ≤ 12 := by
  simpa only [P4AOriginalAscendingFourteenAffineSource.rows] using
    original_pool_l1_le_twelve (P4AOriginalAscendingFourteenAffineSource.literalIndex i r)

/-- Weighted Lipschitz bound for the literal row; no row or coefficient
is replaced by an unsigned set or detached from its original index. -/
theorem original_row_change_le (i : Fin 14) (r : Fin 96) (tau : ℝ)
    (htau : 0 ≤ tau) (t u : Fin 8 → ℝ) (hd : ∀ k, |u k - t k| ≤ tau) :
    |P4AOriginalRemainingEighthSources.evalRow (P4AOriginalAscendingFourteenAffineSource.rows i r) u -
      P4AOriginalRemainingEighthSources.evalRow (P4AOriginalAscendingFourteenAffineSource.rows i r) t| ≤ 12*tau := by
  let a := P4AOriginalAscendingFourteenAffineSource.rows i r
  have heq : P4AOriginalRemainingEighthSources.evalRow a u -
      P4AOriginalRemainingEighthSources.evalRow a t =
      ∑ k : Fin 8, (a k.succ : ℝ) * (u k - t k) := by
    simp only [P4AOriginalRemainingEighthSources.evalRow, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    |∑ k : Fin 8, (a k.succ : ℝ) * (u k - t k)| ≤
        ∑ k : Fin 8, |(a k.succ : ℝ)| * |u k - t k| := by
          simpa only [abs_mul] using
            (Finset.abs_sum_le_sum_abs (fun k : Fin 8 => (a k.succ : ℝ) * (u k - t k)) Finset.univ)
    _ ≤ ∑ k : Fin 8, |(a k.succ : ℝ)| * tau := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hd k) (abs_nonneg _)
    _ = (∑ k : Fin 8, |(a k.succ : ℝ)|) * tau := by rw [Finset.sum_mul]
    _ ≤ 12*tau := mul_le_mul_of_nonneg_right (original_row_l1_le_twelve i r) htau

/-- Every one of the original 96 row occurrences stays strict under
the same coordinate perturbation and one strictly positive margin. -/
theorem original_all96_of_coordinate_distance (i : Fin 14) (delta tau : ℝ)
    (htau : 0 ≤ tau) (hwidth : 12*tau < delta) (t u : Fin 8 → ℝ)
    (ht : t ∈ trim (sourceCell i) delta) (hd : ∀ k, |u k - t k| ≤ tau) :
    P4AOriginalFull87SourceDictionary.Source (sourceCell i) u := by
  have hp := (trim_exact delta (sourceCell i) t).mpr ht
  simp only [trimTests, passed_append, passed_indexed, Finset.mem_univ,
    true_implies, holds_LE, Program.eval, Affine.eval_const] at hp
  change ∀ r : Fin 96, 0 < P4AOriginalRemainingEighthSources.evalRow
    (P4AOriginalAscendingFourteenAffineSource.rows i r) u
  intro r
  have hm : delta ≤ (rowForm (sourceCell i) r).eval t := hp.1.2 r
  rw [row_exact] at hm
  change delta ≤ P4AOriginalRemainingEighthSources.evalRow
    (P4AOriginalAscendingFourteenAffineSource.rows i r) t at hm
  have hc := original_row_change_le i r tau htau t u hd
  have hl := (abs_le.mp hc).1
  linarith

/-- Every point, including every corner, belongs to the same original
96-row source cell. No statement about compiler ALL/ANY follows. -/
theorem original_all96_closed_box (i : Fin 14) (N d : ℕ) (tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 12*tau < delta) (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) delta)
    (u : Fin 8 → ℝ)
    (hu : ∀ k : Fin 8, slotLower N tau d k ≤ u k ∧ u k ≤ slotUpper N tau d k) :
    P2OriginalSaving16FourteenPhysicalAtlas.sourceRows (atlasCell i) u := by
  apply (sourceRows_iff_full87_source i u).mpr
  apply original_all96_of_coordinate_distance i delta tau htau.le hwidth
    (firstEightCoordinates N d) u htrim
  intro k
  have hlabel := P2LowerFiniteCellRounding.primeLabel_halfopen N htau (canonicalPrefix 8 d k)
  have he : firstEightCoordinates N d k =
      Real.log (canonicalPrefix 8 d k : ℝ) / Real.log (N : ℝ) := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank]
    rfl
  rw [← he] at hlabel
  have hlow := (hu k).1
  have hhigh := (hu k).2
  dsimp only [slotLower] at hlow
  dsimp only [slotUpper] at hhigh
  apply abs_le.mpr
  constructor <;> linarith [hlabel.1, hlabel.2]

/-- The original ordered source membership holds for every y in the
same actual untagged compiler fibre. -/
theorem original_all96_on_fibre (i : Fin 14) (N : ℕ) (w tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 12*tau < delta) {x y : ℕ}
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) delta)
    (hy : y ∈ cell (fun _ => []) N N w (cutoff N) tau x) :
    P2OriginalSaving16FourteenPhysicalAtlas.sourceRows (atlasCell i) (firstEightCoordinates N y) := by
  have hyrank : 8 ≤ y.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hy]
    exact hrank
  apply (sourceRows_iff_full87_source i _).mpr
  apply original_all96_of_coordinate_distance i delta tau htau.le hwidth
    (firstEightCoordinates N x) (firstEightCoordinates N y) htrim
  intro k
  have hc : |firstEightCoordinates N x k - firstEightCoordinates N y k| < tau := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank, coord_ancestor hyrank]
    exact same_primeLabel_coordinate_distance_lt N htau
      (cell_canonicalPrefix_label_eq _ _ _ _ _ _ hy hrank k)
  rw [abs_sub_comm]
  exact hc.le

/-- The exact local 96-row source, actual Q, fourth-exponent bound and
same-beta signed product, all on one source witness and one product. -/
theorem all96_same_Q_signed_product
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
      P2OriginalSaving16FourteenPhysicalAtlas.sourceRows (atlasCell i) u) ∧
    P2OriginalSaving16FourteenPhysicalAtlas.sourceRows (atlasCell i) (firstEightCoordinates N y) ∧
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
  have hs := cap_rows_same_Q_signed_product r n e q a nu beta tau he hcut hh
    N hN htau hwidth i hx hrank htrim hy hb G
  exact ⟨fun u hu => original_all96_closed_box i N x tau (width r) htau hwidth hrank htrim u hu,
    original_all96_on_fibre i N ((N : ℝ) ^ (nu * beta ^ 2)) tau (width r) htau hwidth hrank htrim hy,
    hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩

end
end ImbalancedChen.P2Saving16All96ClosedBox
