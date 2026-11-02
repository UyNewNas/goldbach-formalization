import ImbalancedChen.P4AOriginalRemainingEighthSources
import ImbalancedChen.OriginalDescendingFifteenExportOwnershipJoin
import ImbalancedChen.OriginalAscendingThirteenExportOwnershipJoin
import ImbalancedChen.P4AOriginalFirstFailureH3SourceSemantics

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The index type below names the actual source families. The map to the
published 87 slots is a consequence, never a source witness or input.
The forty already supplied source dictionaries are reused exactly.
The new facts derive from original affine source membership. This file
does not construct the missing full actual lambda6 or the final rho.
-/
namespace ImbalancedChen.P4AOriginalFull87SourceDictionary
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope

abbrev Point := Fin 8 → ℝ
inductive Cell where
  | remaining (c : P4AOriginalRemainingEighthSources.Cell)
  | descending (i : Fin 15)
  | ascendingPair (i : Fin 13)
  | h3 (i : Fin 12)
  deriving DecidableEq, Fintype

def Source : Cell → Point → Prop
  | .remaining c, t => P4AOriginalRemainingEighthSources.Source c t
  | .descending i, t => OriginalDescendingFifteenLiteralAffineRows.StrictExportedRows i t
  | .ascendingPair i, t => OriginalAscendingThirteenLiteralAffineRows.StrictExportedRows i t
  | .h3 i, t => P4AOriginalFirstFailureH3Literal.sourceAffineGuard i t

def selected : Cell → Finset (Fin 8)
  | .remaining c => P4AOriginalRemainingEighthSources.selected c
  | .descending _ => {0,7}
  | _ => {1,3,7}
def newCap : Cell → Point → ℝ
  | .remaining c, t => P4AOriginalRemainingEighthSources.newCap c t
  | .descending _, t => P2OriginalDescendingEighthLogSemantics.newCap t
  | .ascendingPair _, t => P2OriginalThirdMinorantLogDictionarySourceOnly.newCap t
  | .h3 _, t => P4AOriginalFirstFailureH3Literal.M8 t
def comparison : Cell → Point → ℝ
  | .remaining c, t => P4AOriginalRemainingEighthSources.comparison c t
  | .descending _, t => P2OriginalDescendingEighthLogSemantics.oldRaw t
  | .ascendingPair _, t => P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap t
  | .h3 _, t => P4AOriginalFirstFailureH3Literal.R6 t

/-- Each family's own original six-coordinate subset convention. -/
def oldSubsetSum : Cell → ℕ → Point → ℝ
  | .remaining _, m, t => P4AOriginalRemainingEighthSources.subsetSum m t
  | .descending _, m, t => OriginalDescendingFifteenCellOwnership.subsetSum m t
  | .ascendingPair _, m, t => OriginalAscendingThirteenCellOwnership.subsetSum m t
  | .h3 _, m, t => P4AOriginalFirstFailureH3Literal.oldSubsetSum m t

def globalIndex : Cell → Fin 87
  | .remaining (.ascending i) =>
      ⟨P4AOriginalAscendingFourteenAffineSource.originalId i, by
        fin_cases i <;> decide⟩
  | .remaining .seed => 7
  | .remaining (.nine i) => ⟨30+i.val, by omega⟩
  | .remaining .fiftyA => 43
  | .remaining .fiftyD => 44
  | .remaining (.h5 i) => ⟨70+i.val, by omega⟩
  | .remaining (.h7 i) => ⟨77+i.val, by omega⟩
  | .descending i => ⟨15+i.val, by omega⟩
  | .ascendingPair i => ⟨45+i.val, by omega⟩
  | .h3 i => ⟨58+i.val, by omega⟩

/-- Closed source-index arithmetic, UNEVALUATED. No generic Fin87 guard
is used to define the source domains. -/
theorem globalIndex_bijective : Function.Bijective globalIndex := by decide
theorem source_cell_count : Fintype.card Cell = 87 := by decide

theorem source_basic {c : Cell} {t : Point} (h : Source c t) :
    t 0 < mu ∧ (1/100 : ℝ) < t 2 ∧ (53/13824 : ℝ) < t 7 ∧
    (∀ j : Fin 7, t j.succ < t j.castSucc) := by
  cases c with
  | remaining c =>
      obtain ⟨hx,hz,hr,ho,_⟩ := P4AOriginalRemainingEighthSources.source_basic h
      exact ⟨hx,hz,hr,ho⟩
  | descending i =>
      have hs := (OriginalDescendingFifteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      exact ⟨hs.largest,hs.thirdFloor,hs.lastFloor,hs.order⟩
  | ascendingPair i =>
      have hs := (OriginalAscendingThirteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      exact ⟨hs.largest,hs.thirdFloor,hs.lastFloor,hs.order⟩
  | h3 i =>
      have hs := (P4AOriginalFirstFailureH3SourceSemantics.sourceAffineGuard_iff_StrictH3 i t).mp h
      exact ⟨hs.largest,hs.third_cutoff,hs.eighth_cutoff,hs.ordered⟩

theorem source_selected_license {c : Cell} {t : Point} (h : Source c t) :
    newCap c t < v (∑ j ∈ selected c, t j) := by
  cases c with
  | remaining c => exact P4AOriginalRemainingEighthSources.source_selected_license h
  | descending i =>
      have hs := (OriginalDescendingFifteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      simpa [selected,newCap,P2OriginalDescendingEighthLogSemantics.selectedMask129] using
        (P2OriginalDescendingEighthLogSemantics.selected129_license hs.descending).2
  | ascendingPair i =>
      have hs := (OriginalAscendingThirteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      have hv := v_eq_A hs.ascendingNew.le
      simp only [newCap,selected]
      have heq : (∑ j ∈ ({1,3,7} : Finset (Fin 8)), t j) =
          P2OriginalThirdMinorantLogDictionarySourceOnly.selectedSum t := by
        norm_num [P2OriginalThirdMinorantLogDictionarySourceOnly.selectedSum]
      rw [heq,hv]
      dsimp [P2OriginalThirdMinorantLogDictionarySourceOnly.newCap,
        P2OriginalThirdMinorantLogDictionarySourceOnly.eta]
      linarith
  | h3 i =>
      simpa [newCap,selected,P4AOriginalFirstFailureH3Literal.selected138] using
        P4AOriginalFirstFailureH3SourceSemantics.source_selected_license h

theorem source_full_selected {c : Cell} {t : Point} (h : Source c t) :
    (∀ j, prefixSquareExpr t j < newCap c t) ∧
    (∀ j ∉ selected c, selectedSquareExpr (selected c) t j < newCap c t) := by
  cases c with
  | remaining c => exact P4AOriginalRemainingEighthSources.source_full_selected h
  | descending i =>
      have hs := (OriginalDescendingFifteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      refine ⟨hs.fullSquares,?_⟩
      intro j hj
      have hn : j ≠ 0 ∧ j ≠ 7 := by simpa [selected] using hj
      have hg := hs.complementSquares j hn.1 hn.2
      change selectedSquareExpr {0,7} t j < P2OriginalDescendingEighthLogSemantics.newCap t
      have heq : selectedSquareExpr ({0,7} : Finset (Fin 8)) t j =
          P2OriginalDescendingEighthLogSemantics.selectedSum t +
          (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => 0 < k ∧ k < j), t k)+2*t j := by
        fin_cases j <;> norm_num at hn
        all_goals norm_num [selectedSquareExpr,P2OriginalDescendingEighthLogSemantics.selectedSum,
          Finset.sum_filter,Fin.sum_univ_succ] <;> ring
      rw [heq]
      exact hg
  | ascendingPair i =>
      have hs := (OriginalAscendingThirteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      refine ⟨hs.fullSquares,?_⟩
      intro j hj
      have hn : j ≠ 1 ∧ j ≠ 3 ∧ j ≠ 7 := by simpa [selected] using hj
      have hg := hs.complementSquares j hn.1 hn.2.1 hn.2.2
      simpa [selected,newCap,selectedSquareExpr,
        P2OriginalThirdMinorantLogDictionarySourceOnly.selectedSum,
        Finset.sum_filter,add_assoc,and_assoc] using hg
  | h3 i =>
      simpa [newCap,selected,P4AOriginalFirstFailureH3SourceSemantics.selectedSlots] using
        P4AOriginalFirstFailureH3SourceSemantics.source_full_and_selected_squares h

theorem source_physical_ceiling {c : Cell} {t : Point} (h : Source c t) :
    newCap c t < (153/256 : ℝ) :=
  (source_selected_license h).trans_le (v_le_cap _)

-- SOURCE_IDEAL_HISTORY

theorem source_ordered {c : Cell} {t : Point} (h : Source c t) :
    Ordered (t 0) (t 1) (t 2) := by
  obtain ⟨hx,hz,_hr,ho⟩ := source_basic h
  exact ⟨by linarith, (ho 1).le, (ho 0).le, hx.le⟩

/-- Every old nonempty first-six tent is bounded using the original
chosen-plane row, with the omitted winner supplied by its literal identity. -/
theorem source_all_old_tents {c : Cell} {t : Point} (h : Source c t)
    (m : ℕ) (hm : m ∈ Finset.Icc 1 63) :
    v (oldSubsetSum c m t) ≤ comparison c t := by
  cases c with
  | remaining c => exact P4AOriginalRemainingEighthSources.source_all_old_tents h m hm
  | descending i =>
      have hs := (OriginalDescendingFifteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      change v (OriginalDescendingFifteenCellOwnership.subsetSum m t) ≤
        P2OriginalDescendingEighthLogSemantics.oldRaw t
      by_cases hw : m = 6
      · subst m
        have heq : OriginalDescendingFifteenCellOwnership.subsetSum 6 t = t 1+t 2 := by
          norm_num [OriginalDescendingFifteenCellOwnership.subsetSum,
            OriginalDescendingFifteenCellOwnership.maskSlots,Finset.sum_filter,Fin.sum_univ_succ]
        rw [heq,v_eq_min]
        exact min_le_right _ _
      · have hg := hs.branches m hm hw
        rw [OriginalDescendingFifteenCellOwnership.branchPlane] at hg
        rw [v_eq_min]
        split_ifs at hg
        · exact (min_le_left _ _).trans hg.le
        · exact (min_le_right _ _).trans hg.le
  | ascendingPair i =>
      have hs := (OriginalAscendingThirteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      change v (OriginalAscendingThirteenCellOwnership.subsetSum m t) ≤
        P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap t
      by_cases hw : m = 9
      · subst m
        have heq : OriginalAscendingThirteenCellOwnership.subsetSum 9 t = t 0+t 3 := by
          norm_num [OriginalAscendingThirteenCellOwnership.subsetSum,
            OriginalAscendingThirteenCellOwnership.maskSlots,Finset.sum_filter,Fin.sum_univ_succ]
        rw [heq,v_eq_min]
        exact min_le_left _ _
      · have hg := hs.branches m hm hw
        rw [OriginalAscendingThirteenCellOwnership.branchPlane] at hg
        rw [v_eq_min]
        split_ifs at hg
        · exact (min_le_left _ _).trans hg.le
        · exact (min_le_right _ _).trans hg.le
  | h3 i =>
      have hs := (P4AOriginalFirstFailureH3SourceSemantics.sourceAffineGuard_iff_StrictH3 i t).mp h
      change v (P4AOriginalFirstFailureH3Literal.oldSubsetSum m t) ≤
        P4AOriginalFirstFailureH3Literal.R6 t
      by_cases hw : m = 9
      · subst m
        have heq : P4AOriginalFirstFailureH3Literal.oldSubsetSum 9 t = t 0+t 3 := by
          norm_num [P4AOriginalFirstFailureH3Literal.oldSubsetSum,Fin.sum_univ_succ]
        rw [heq,v_eq_min]
        exact min_le_left _ _
      · have hg := hs.old_planes m hm hw
        have htent : v (P4AOriginalFirstFailureH3Literal.oldSubsetSum m t) ≤
            P4AOriginalFirstFailureH3Literal.oldPlane i m t := by
          rw [v_eq_min,P4AOriginalFirstFailureH3Literal.oldPlane]
          split_ifs
          · exact min_le_left _ _
          · apply (min_le_right _ _).trans
            have heq : C (P4AOriginalFirstFailureH3Literal.oldSubsetSum m t) =
                P4AOriginalFirstFailureH3Literal.D
                  (P4AOriginalFirstFailureH3Literal.oldSubsetSum m t) := by
              dsimp [C,P4AOriginalFirstFailureH3Literal.D]
              ring
            exact heq.le
        exact htent.trans hg.le

theorem oldSubsetSum_third_masks (c : Cell) (t : Point) :
    oldSubsetSum c 1 t = t 0 ∧ oldSubsetSum c 3 t = t 0+t 1 ∧
    oldSubsetSum c 7 t = t 0+t 1+t 2 ∧ oldSubsetSum c 5 t = t 0+t 2 ∧
    oldSubsetSum c 6 t = t 1+t 2 := by
  cases c <;>
    norm_num [oldSubsetSum,P4AOriginalRemainingEighthSources.subsetSum,
      OriginalDescendingFifteenCellOwnership.subsetSum,
      OriginalDescendingFifteenCellOwnership.maskSlots,
      OriginalAscendingThirteenCellOwnership.subsetSum,
      OriginalAscendingThirteenCellOwnership.maskSlots,
      P4AOriginalFirstFailureH3Literal.oldSubsetSum,
      Finset.sum_filter,Fin.sum_univ_succ,add_assoc]

theorem source_old_w {c : Cell} {t : Point} (h : Source c t) :
    B (t 2) < comparison c t := by
  cases c with
  | remaining c => exact (P4AOriginalRemainingEighthSources.source_basic h).2.2.2.2.2.1
  | descending i =>
      have hs := (OriginalDescendingFifteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      have hw := hs.oldW
      change B (t 2) < P2OriginalDescendingEighthLogSemantics.oldRaw t
      dsimp [B]
      linarith
  | ascendingPair i =>
      have hs := (OriginalAscendingThirteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      have hw := hs.oldW
      change B (t 2) < P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap t
      dsimp [B]
      linarith
  | h3 i =>
      have hs := (P4AOriginalFirstFailureH3SourceSemantics.sourceAffineGuard_iff_StrictH3 i t).mp h
      have hw := hs.W_below_R6
      change B (t 2) < P4AOriginalFirstFailureH3Literal.R6 t
      dsimp [P4AOriginalFirstFailureH3Literal.W] at hw
      dsimp [B,cap]
      linarith

/-- The original gated and Theta-clipped ideal third is bounded on all87
source domains. This upper comparison is not an actual sixth-parent bound. -/
theorem source_original_ideal_le_comparison {c : Cell} {t : Point} (h : Source c t) :
    actualExtendedThirdIdealCap (t 0) (t 1) (t 2) ≤ comparison c t := by
  have ho := source_ordered h
  obtain ⟨he1,he3,he7,he5,he6⟩ := oldSubsetSum_third_masks c t
  have h1 := source_all_old_tents h 1 (by decide)
  have h3 := source_all_old_tents h 3 (by decide)
  have h7 := source_all_old_tents h 7 (by decide)
  have h5 := source_all_old_tents h 5 (by decide)
  have h6 := source_all_old_tents h 6 (by decide)
  rw [he1] at h1
  rw [he3] at h3
  rw [he7] at h7
  rw [he5] at h5
  rw [he6] at h6
  rw [actualExtendedThirdIdealCap_eq,if_pos ho.2.2.2,original_eq_six ho]
  exact (min_le_right _ _).trans
    (max_le h1 (max_le h3 (max_le h7 (max_le (source_old_w h).le (max_le h5 h6)))))

private theorem first_and_pair_le_original_ideal (t : Point)
    (ho : Ordered (t 0) (t 1) (t 2)) :
    v (t 0) ≤ actualExtendedThirdIdealCap (t 0) (t 1) (t 2) ∧
    v (t 1+t 2) ≤ actualExtendedThirdIdealCap (t 0) (t 1) (t 2) := by
  have hc : cap < thirdPrefixTheta := by norm_num [cap,thirdPrefixTheta]
  rw [actualExtendedThirdIdealCap_eq,if_pos ho.2.2.2,original_eq_six ho]
  constructor
  · exact le_min ((v_le_cap _).trans hc.le) (le_max_left _ _)
  · apply le_min ((v_le_cap _).trans hc.le)
    unfold six
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _))))

/-- The actual gated ideal third admits each named old odd history.
Failure of D23 in H3/H5/H7 is not failure of this true third policy. -/
theorem source_histories_original_ideal {c : Cell} {t : Point} (h : Source c t) :
    ∀ j : Fin 4, P4AOriginalRemainingEighthSources.history t j <
      actualExtendedThirdIdealCap (t 0) (t 1) (t 2) := by
  have hv := first_and_pair_le_original_ideal t (source_ordered h)
  cases c with
  | remaining c => exact P4AOriginalRemainingEighthSources.source_histories_original_ideal h
  | descending i =>
      have hs := (OriginalDescendingFifteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      have hb : P2OriginalDescendingEighthLogSemantics.oldRaw t ≤
          actualExtendedThirdIdealCap (t 0) (t 1) (t 2) := by
        have heq : P2OriginalDescendingEighthLogSemantics.oldRaw t = v (t 1+t 2) :=
          (v_eq_C hs.oldWinner.le).symm
        rw [heq]
        exact hv.2
      intro j
      fin_cases j
      · exact hs.firstHistory.trans_le hb
      · exact hs.thirdHistory.trans_le hb
      · exact hs.fifthHistory.trans_le hb
      · exact hs.seventhHistory.trans_le hb
  | ascendingPair i =>
      have hs := (OriginalAscendingThirteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      have hb := P2OriginalThirdMinorantLogDictionarySourceOnly.thirdMinorant_le_actual_cap
        (OriginalAscendingThirteenCellOwnership.rows_physical hs)
      intro j
      fin_cases j
      · exact hs.firstHistory.trans_le hb
      · exact hs.thirdHistory.trans_le hb
      · exact hs.fifthHistory.trans_le hb
      · exact hs.seventhHistory.trans_le hb
  | h3 i =>
      have hs := (P4AOriginalFirstFailureH3SourceSemantics.sourceAffineGuard_iff_StrictH3 i t).mp h
      have hb : P4AOriginalFirstFailureH3Literal.B3 t ≤
          actualExtendedThirdIdealCap (t 0) (t 1) (t 2) := by
        have heq : P4AOriginalFirstFailureH3Literal.B3 t = v (t 0) :=
          (v_eq_A hs.largest.le).symm
        rw [heq]
        exact hv.1
      intro j
      fin_cases j
      · exact hs.first_below_B3.trans_le hb
      · exact hs.H3_below_B3.trans_le hb
      · exact hs.H5_below_B3.trans_le hb
      · exact hs.H7_below_B3.trans_le hb

theorem source_improvement_terminal {c : Cell} {t : Point} (h : Source c t) :
    comparison c t < newCap c t ∧ newCap c t < (∑ j, t j)+3*t 7 := by
  cases c with
  | remaining c => exact (P4AOriginalRemainingEighthSources.source_basic h).2.2.2.2.2.2
  | descending i =>
      have hs := (OriginalDescendingFifteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      exact ⟨hs.improvement,hs.terminal⟩
  | ascendingPair i =>
      have hs := (OriginalAscendingThirteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      exact ⟨hs.improvement,hs.terminal⟩
  | h3 i =>
      have hs := (P4AOriginalFirstFailureH3SourceSemantics.sourceAffineGuard_iff_StrictH3 i t).mp h
      exact ⟨hs.improved,hs.new_residual⟩

/-- This is the ideal third's residual, not a substituted sixth parent. -/
theorem source_original_ideal_residual {c : Cell} {t : Point} (h : Source c t) :
    t 7 < actualExtendedThirdIdealCap (t 0) (t 1) (t 2)-(∑ j, t j) := by
  have hh := source_histories_original_ideal h 3
  have ho := (source_basic h).2.2.2 6
  dsimp [P4AOriginalRemainingEighthSources.history] at hh
  norm_num at ho
  simp [Fin.sum_univ_succ]
  linarith

/-- Every source square is at the literal same physical cap and same N. -/
theorem source_integer_squares {c : Cell} {t : Point} (h : Source c t)
    (N : ℝ) (hN : 1 < N) (p : Fin 8 → ℕ)
    (hp : ∀ j, (p j : ℝ) ≤ N^t j) :
    (∀ j, ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j), p k : ℕ) : ℝ) *
      (p j : ℝ)^2 < N^newCap c t) ∧
    (∀ j ∉ selected c, ((∏ k ∈ selected c, p k : ℕ) : ℝ) *
      ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ∉ selected c), p k : ℕ) : ℝ) *
      (p j : ℝ)^2 < N^newCap c t) := by
  obtain ⟨hf,hs⟩ := source_full_selected h
  exact ⟨fun j => prefixSquareExpr_actual_gate N hN p t hp j (hf j),
    fun j hj => selectedSquareExpr_actual_gate (selected c) N hN p t hp j (hs j hj)⟩

end
end ImbalancedChen.P4AOriginalFull87SourceDictionary
