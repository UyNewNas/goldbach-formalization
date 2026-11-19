import ImbalancedChen.P2Saving16FourthRowSignedProduct
import ImbalancedChen.P4AOriginalFull87CompiledCounting

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED. Seven ordered row occurrences
on the same actual fine fibre and the unique physical product carrier. -/
namespace ImbalancedChen.P2Saving16SevenOrderRowsCarrier
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
open P2Saving16FourthRowSignedProduct

/-- Row indices 3,...,9 in their original order. -/
def orderRow (j : Fin 7) : Fin 96 := ⟨j.val + 3, by omega⟩

def slotLower (N : ℕ) (tau : ℝ) (d : ℕ) (j : Fin 8) : ℝ :=
  (P2LowerFiniteCellRounding.primeLabel N tau (canonicalPrefix 8 d j) : ℝ) * tau

def slotUpper (N : ℕ) (tau : ℝ) (d : ℕ) (j : Fin 8) : ℝ :=
  ((P2LowerFiniteCellRounding.primeLabel N tau (canonicalPrefix 8 d j) : ℝ) + 1) * tau

/-- Every one of the seven original row occurrences is the adjacent
coordinate difference, for each original ascending-family index. -/
theorem original_order_row (i : Fin 14) (j : Fin 7) (t : Fin 8 → ℝ) :
    (rowForm (sourceCell i) (orderRow j)).eval t = t j.castSucc - t j.succ := by
  fin_cases j <;> fin_cases i <;>
    norm_num [orderRow, rowForm, rowCoeffs, sourceCell,
      P4AOriginalRemainingEighthSources.row, P4AOriginalRemainingEighthSources.rowCount,
      P4AOriginalFull87StrictActionTrim.rowCount,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P1FiniteAffineDecisionProgram.Affine.eval, Fin.sum_univ_succ] <;> ring

theorem order_row_margin (i : Fin 14) (j : Fin 7) (delta : ℝ) (t : Fin 8 → ℝ)
    (ht : t ∈ trim (sourceCell i) delta) : delta ≤ t j.castSucc - t j.succ := by
  have hp := (trim_exact delta (sourceCell i) t).mpr ht
  simp only [trimTests, passed_append, passed_indexed, Finset.mem_univ,
    true_implies, holds_LE, Program.eval, Affine.eval_const] at hp
  have h := hp.1.2 (orderRow j)
  simpa only [original_order_row] using h

/-- All seven worst closed corners are strictly ordered. -/
theorem all_order_worst_corners (i : Fin 14) (N d : ℕ) (tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 2 * tau ≤ delta)
    (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) delta) :
    ∀ j : Fin 7, 0 < slotLower N tau d j.castSucc - slotUpper N tau d j.succ := by
  intro j
  have hm := order_row_margin i j delta (firstEightCoordinates N d) htrim
  have h0 := (P2LowerFiniteCellRounding.primeLabel_halfopen N htau
    (canonicalPrefix 8 d j.castSucc)).2
  have h1 := (P2LowerFiniteCellRounding.primeLabel_halfopen N htau
    (canonicalPrefix 8 d j.succ)).1
  have he0 : firstEightCoordinates N d j.castSucc =
      Real.log (canonicalPrefix 8 d j.castSucc : ℝ) / Real.log (N : ℝ) := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank]
    rfl
  have he1 : firstEightCoordinates N d j.succ =
      Real.log (canonicalPrefix 8 d j.succ : ℝ) / Real.log (N : ℝ) := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank]
    rfl
  rw [← he0] at h0
  rw [← he1] at h1
  dsimp only [slotLower, slotUpper]
  linarith

/-- Every point of the closed label box satisfies all seven original
ordered rows, so every endpoint choice is included. -/
theorem all_order_closed_box (i : Fin 14) (N d : ℕ) (tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 2 * tau ≤ delta)
    (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) delta)
    (u : Fin 8 → ℝ)
    (hu : ∀ k : Fin 8, slotLower N tau d k ≤ u k ∧ u k ≤ slotUpper N tau d k) :
    ∀ j : Fin 7, 0 < (rowForm (sourceCell i) (orderRow j)).eval u := by
  have hc := all_order_worst_corners i N d tau delta htau hwidth hrank htrim
  intro j
  rw [original_order_row]
  have hl := (hu j.castSucc).1
  have hr := (hu j.succ).2
  have hcorner := hc j
  linarith

/-- The seven literal row occurrences remain strict on the same fibre. -/
theorem all_order_rows_on_fibre (i : Fin 14) (N : ℕ) (w tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 2 * tau ≤ delta) {x y : ℕ}
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) delta)
    (hy : y ∈ cell (fun _ => []) N N w (cutoff N) tau x) :
    ∀ j : Fin 7, 0 < (rowForm (sourceCell i) (orderRow j)).eval (firstEightCoordinates N y) := by
  have hyrank : 8 ≤ y.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hy]
    exact hrank
  intro j
  have h0 : |firstEightCoordinates N x j.castSucc - firstEightCoordinates N y j.castSucc| < tau := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank, coord_ancestor hyrank]
    exact same_primeLabel_coordinate_distance_lt N htau
      (cell_canonicalPrefix_label_eq _ _ _ _ _ _ hy hrank j.castSucc)
  have h1 : |firstEightCoordinates N x j.succ - firstEightCoordinates N y j.succ| < tau := by
    dsimp only [firstEightCoordinates]
    rw [coord_ancestor hrank, coord_ancestor hyrank]
    exact same_primeLabel_coordinate_distance_lt N htau
      (cell_canonicalPrefix_label_eq _ _ _ _ _ _ hy hrank j.succ)
  have hm := order_row_margin i j delta (firstEightCoordinates N x) htrim
  have h0' := (abs_lt.mp h0).2
  have h1' := (abs_lt.mp h1).1
  rw [original_order_row]
  linarith

/-- The actual product lies on the very compiler Q and has exactly one
small/rough decomposition there. This is not corner multiplicity. -/
theorem actual_product_mem_Q_unique (N : ℕ) (w : ℝ) {b y : ℕ}
    (hb : b ∈ actualSmallRosserSupport N N w)
    (hy : y ∈ universe N N w (cutoff N)) :
    b * y ∈ P4AOriginalFull87CompiledCounting.moduli N w ∧
    ∀ s d : ℕ, s ∈ actualSmallRosserSupport N N w → d ∈ universe N N w (cutoff N) →
      s * d = b * y → s = b ∧ d = y := by
  constructor
  · change b * y ∈ smallRoughModuli (actualSmallRosserSupport N N w) (universe N N w (cutoff N))
    exact Finset.mem_image.mpr ⟨(b, y), Finset.mem_product.mpr ⟨hb, hy⟩, rfl⟩
  · intro s d hs hd he
    have h : (s, d) = (b, y) := smallRough_factorization_unique
      (actualSmallRosserSupport_smallPrimeSupportedAt N N w hs)
      (P2LowerFiniteCellRounding.universe_rough N N w (cutoff N) hd)
      (actualSmallRosserSupport_smallPrimeSupportedAt N N w hb)
      (P2LowerFiniteCellRounding.universe_rough N N w (cutoff N) hy) he
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Same source witness, all seven original rows, literal Q, unique
small/rough factorization, and the existing same-beta signed term. -/
theorem seven_rows_same_Q_signed_product
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
    (∀ j : Fin 7, 0 < slotLower N tau x j.castSucc - slotUpper N tau x j.succ) ∧
    (∀ u : Fin 8 → ℝ, (∀ k : Fin 8, slotLower N tau x k ≤ u k ∧ u k ≤ slotUpper N tau x k) →
      ∀ j : Fin 7, 0 < (rowForm (sourceCell i) (orderRow j)).eval u) ∧
    (∀ j : Fin 7, 0 < (rowForm (sourceCell i) (orderRow j)).eval (firstEightCoordinates N y)) ∧
    b * y ∈ P4AOriginalFull87CompiledCounting.moduli N w ∧
    (∀ s d : ℕ, s ∈ actualSmallRosserSupport N N w → d ∈ universe N N w z →
      s * d = b * y → s = b ∧ d = y) ∧
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
  have hq := actual_product_mem_Q_unique N ((N : ℝ) ^ (nu * beta ^ 2)) hb hyu
  have hs := fourth_row_same_beta_signed_product r n e q a nu beta tau he hcut hh
    N hN htau hwidth i hx hrank htrim hy hb G
  exact ⟨all_order_worst_corners i N x tau (width r) htau hwidth hrank htrim,
    fun u hu => all_order_closed_box i N x tau (width r) htau hwidth hrank htrim u hu,
    all_order_rows_on_fibre i N ((N : ℝ) ^ (nu * beta ^ 2)) tau (width r) htau hwidth hrank htrim hy,
    hq.1, hq.2, hs.2.2.1, hs.2.2.2⟩

end
end ImbalancedChen.P2Saving16SevenOrderRowsCarrier
