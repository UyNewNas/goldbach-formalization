import ImbalancedChen.P4AOriginalFull87SourceDictionary
import ImbalancedChen.P4AOriginalH5H7SourceDispatch

/-!
SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.
Original full87 ownership.  Every premise called Source is the entire
original strict affine source, not PhysicalRows or an assumed owner.
This file does not identify an ideal-third cap with an actual sixth cap.
The finite label/separator bodies below are UNEVALUATED.
-/
namespace ImbalancedChen.P4AOriginalFull87Ownership
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P4AOriginalFull87SourceDictionary

abbrev subsetSum := P4AOriginalRemainingEighthSources.subsetSum
abbrev history := P4AOriginalRemainingEighthSources.history

def winner : Cell → ℕ
  | .remaining c => P4AOriginalRemainingEighthSources.winner c
  | .descending _ => 6
  | _ => 9

def leftMasks : Cell → Finset ℕ
  | .remaining c => P4AOriginalRemainingEighthSources.leftMasks c
  | .descending i => OriginalDescendingFifteenCellOwnership.leftMasks i
  | .ascendingPair i => OriginalAscendingThirteenCellOwnership.leftMasks i
  | .h3 i => P4AOriginalFirstFailureH3Literal.leftMasks i

def plane (c : Cell) (m : ℕ) (t : Point) : ℝ :=
  if m ∈ leftMasks c then A (subsetSum m t) else C (subsetSum m t)

/-- This is the source chronology/branch kind, not a new permission. -/
def kind : Cell → Fin 9
  | .remaining (.ascending _) | .remaining .seed => 0
  | .descending _ => 1
  | .remaining (.nine _) => 2
  | .remaining .fiftyA => 3
  | .remaining .fiftyD => 4
  | .ascendingPair _ => 5
  | .h3 _ => 6
  | .remaining (.h5 _) => 7
  | .remaining (.h7 _) => 8

theorem winner_mem (c : Cell) : winner c ∈ Finset.Icc 1 63 := by
  cases c with
  | remaining c => cases c <;> norm_num [winner, P4AOriginalRemainingEighthSources.winner]
  | descending i => norm_num [winner]
  | ascendingPair i => norm_num [winner]
  | h3 i => norm_num [winner]

/-- Only the integer subset convention is converted; t remains arbitrary. -/
set_option maxHeartbeats 0 in
theorem source_subset_dictionary (c : Cell) (m : Fin 64) (t : Point) :
    oldSubsetSum c m.val t = subsetSum m.val t := by
  cases c with
  | remaining c => rfl
  | descending i =>
      fin_cases m <;>
        norm_num [oldSubsetSum, subsetSum, P4AOriginalRemainingEighthSources.subsetSum,
          OriginalDescendingFifteenCellOwnership.subsetSum,
          OriginalDescendingFifteenCellOwnership.maskSlots,
          Finset.sum_filter, Fin.sum_univ_succ] <;> ring
  | ascendingPair i =>
      fin_cases m <;>
        norm_num [oldSubsetSum, subsetSum, P4AOriginalRemainingEighthSources.subsetSum,
          OriginalAscendingThirteenCellOwnership.subsetSum,
          OriginalAscendingThirteenCellOwnership.maskSlots,
          Finset.sum_filter, Fin.sum_univ_succ] <;> ring
  | h3 i => rfl

theorem source_old_planes {c : Cell} {t : Point} (h : Source c t)
    (m : ℕ) (hm : m ∈ Finset.Icc 1 63) (hw : m ≠ winner c) :
    plane c m t < comparison c t := by
  have hm64 : m < 64 := by have hh := (Finset.mem_Icc.mp hm).2; omega
  have he := source_subset_dictionary c ⟨m,hm64⟩ t
  cases c with
  | remaining c =>
      obtain ⟨k,hk⟩ := P4AOriginalRemainingEighthSources.branchMask_covers c m hm hw
      have hb := h (P4AOriginalRemainingEighthSources.branchRow c k)
      rw [P4AOriginalRemainingEighthSources.source_branch_row,hk] at hb
      exact sub_pos.mp hb
  | descending i =>
      have hs := (OriginalDescendingFifteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      have hb := hs.branches m hm hw
      change OriginalDescendingFifteenCellOwnership.subsetSum m t = subsetSum m t at he
      simpa only [plane,leftMasks,comparison,
        OriginalDescendingFifteenCellOwnership.branchPlane,he] using hb
  | ascendingPair i =>
      have hs := (OriginalAscendingThirteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      have hb := hs.branches m hm hw
      change OriginalAscendingThirteenCellOwnership.subsetSum m t = subsetSum m t at he
      simpa only [plane,leftMasks,comparison,
        OriginalAscendingThirteenCellOwnership.branchPlane,he] using hb
  | h3 i =>
      have hs := (P4AOriginalFirstFailureH3SourceSemantics.sourceAffineGuard_iff_StrictH3 i t).mp h
      simpa [plane,leftMasks,comparison,
        P4AOriginalFirstFailureH3Literal.oldPlane,
        P4AOriginalFirstFailureH3Literal.oldSubsetSum,subsetSum,
        P4AOriginalRemainingEighthSources.subsetSum,
        A,C,P4AOriginalFirstFailureH3Literal.A,P4AOriginalFirstFailureH3Literal.D,
        div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using
          hs.old_planes m hm hw

theorem source_nonwinner_tent {c : Cell} {t : Point} (h : Source c t)
    (m : ℕ) (hm : m ∈ Finset.Icc 1 63) (hw : m ≠ winner c) :
    v (subsetSum m t) < comparison c t := by
  have hp := source_old_planes h m hm hw
  rw [v_eq_min]
  unfold plane at hp
  split_ifs at hp
  · exact (min_le_left _ _).trans_lt hp
  · exact (min_le_right _ _).trans_lt hp

/-- Original named winner-side rows for the newly materialized families.
The row is checked symbolically, never at a sample or a barycentre. -/
set_option maxHeartbeats 0 in
theorem remaining_winner_side {c : P4AOriginalRemainingEighthSources.Cell} {t : Point}
    (h : P4AOriginalRemainingEighthSources.Source c t) :
    match c with
    | .ascending _ | .seed => mu < t 1+t 2
    | .fiftyA => t 1+t 4+t 5 < mu
    | .fiftyD => mu < t 1+t 4+t 5
    | _ => t 0+t 3 < mu := by
  cases c with
  | ascending i =>
      have hh := P4AOriginalRemainingEighthSources.source_common_pos h 34
      dsimp [P4AOriginalRemainingEighthSources.commonSlack,
        P4AOriginalRemainingEighthSources.sideSlack] at hh
      linarith
  | seed =>
      have hh := P4AOriginalRemainingEighthSources.source_common_pos h 34
      dsimp [P4AOriginalRemainingEighthSources.commonSlack,
        P4AOriginalRemainingEighthSources.sideSlack] at hh
      linarith
  | nine i =>
      have hh := h 15
      fin_cases i <;>
        norm_num [P4AOriginalRemainingEighthSources.row,
          P4AOriginalRemainingEighthSources.evalRow,
          P4AOriginalSeed7Unequal15Literal.nineRows,Fin.sum_univ_succ,mu] at hh ⊢ <;>
        linarith
  | fiftyA =>
      have hh := h 15
      norm_num [P4AOriginalRemainingEighthSources.row,
        P4AOriginalRemainingEighthSources.evalRow,
        P4AOriginalSeed7Unequal15Literal.fiftyAscRows,Fin.sum_univ_succ,mu] at hh ⊢
      linarith
  | fiftyD =>
      have hh := h 15
      norm_num [P4AOriginalRemainingEighthSources.row,
        P4AOriginalRemainingEighthSources.evalRow,
        P4AOriginalSeed7Unequal15Literal.fiftyDescRows,Fin.sum_univ_succ,mu] at hh ⊢
      linarith
  | h5 i =>
      have hh := h 15
      fin_cases i <;>
        norm_num [P4AOriginalRemainingEighthSources.row,
          P4AOriginalRemainingEighthSources.evalRow,
          P4AOriginalFirstFailureH5H7Literal.h5AffineRows,Fin.sum_univ_succ,mu] at hh ⊢ <;>
        linarith
  | h7 i =>
      have hh := h 15
      fin_cases i <;>
        norm_num [P4AOriginalRemainingEighthSources.row,
          P4AOriginalRemainingEighthSources.evalRow,
          P4AOriginalFirstFailureH5H7Literal.h7AffineRows,Fin.sum_univ_succ,mu] at hh ⊢ <;>
        linarith

theorem source_winner_tent {c : Cell} {t : Point} (h : Source c t) :
    v (subsetSum (winner c) t) = comparison c t := by
  cases c with
  | remaining c =>
      have hw := remaining_winner_side h
      cases c <;>
        norm_num [winner,P4AOriginalRemainingEighthSources.winner,
          subsetSum,P4AOriginalRemainingEighthSources.subsetSum,
          comparison,P4AOriginalRemainingEighthSources.comparison,Fin.sum_univ_succ]
      all_goals first | exact v_eq_C hw.le | exact v_eq_A hw.le
  | descending i =>
      have hs := (OriginalDescendingFifteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      simpa [winner,subsetSum,P4AOriginalRemainingEighthSources.subsetSum,
        comparison,P2OriginalDescendingEighthLogSemantics.oldRaw,
        P2OriginalDescendingEighthLogSemantics.d,Fin.sum_univ_succ] using v_eq_C hs.oldWinner.le
  | ascendingPair i =>
      have hs := (OriginalAscendingThirteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      simpa [winner,subsetSum,P4AOriginalRemainingEighthSources.subsetSum,
        comparison,P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap,
        Fin.sum_univ_succ] using v_eq_A hs.oldWinner.le
  | h3 i =>
      have hs := (P4AOriginalFirstFailureH3SourceSemantics.sourceAffineGuard_iff_StrictH3 i t).mp h
      have hw := hs.winner9_ascending
      have hm : t 0+t 3 < mu := by
        dsimp [P4AOriginalFirstFailureH3Literal.R6,P4AOriginalFirstFailureH3Literal.A,
          P4AOriginalFirstFailureH3Literal.D,mu] at *
        linarith
      simpa [winner,subsetSum,P4AOriginalRemainingEighthSources.subsetSum,
        comparison,P4AOriginalFirstFailureH3Literal.R6,
        A,P4AOriginalFirstFailureH3Literal.A,Fin.sum_univ_succ] using v_eq_A hm.le

theorem source_comparison_le_cap {c : Cell} {t : Point} (h : Source c t) :
    comparison c t ≤ cap := by
  rw [← source_winner_tent h]
  exact v_le_cap _

theorem common_source_winner {c d : Cell} {t : Point}
    (hc : Source c t) (hd : Source d t) : winner c = winner d := by
  by_contra hne
  have hcd := source_nonwinner_tent hc (winner d) (winner_mem d) (Ne.symm hne)
  have hdc := source_nonwinner_tent hd (winner c) (winner_mem c) hne
  rw [source_winner_tent hd] at hcd
  rw [source_winner_tent hc] at hdc
  exact lt_asymm hcd hdc

def KindRows (k : Fin 9) (t : Point) : Prop :=
  match k.val with
  | 0 => t 0+t 7 < mu
  | 1 => mu < t 0+t 7
  | 2 => mu < t 1+t 2 ∧ ∀ j : Fin 4, history t j < C (t 1+t 2)
  | 3 => t 1+t 4+t 5 < mu
  | 4 => mu < t 1+t 4+t 5
  | 5 => t 1+t 2 < mu
  | 6 => mu < t 1+t 2 ∧ C (t 1+t 2) < history t 1
  | 7 => mu < t 1+t 2 ∧ history t 1 < C (t 1+t 2) ∧ C (t 1+t 2) < history t 2
  | _ => mu < t 1+t 2 ∧ history t 1 < C (t 1+t 2) ∧
      history t 2 < C (t 1+t 2) ∧ C (t 1+t 2) < history t 3

set_option maxHeartbeats 0 in
theorem source_kind_rows {c : Cell} {t : Point} (h : Source c t) : KindRows (kind c) t := by
  cases c with
  | remaining c =>
      cases c with
      | ascending i =>
          have hh := P4AOriginalRemainingEighthSources.source_common_pos h 17
          norm_num [P4AOriginalRemainingEighthSources.commonSlack,
            P4AOriginalRemainingEighthSources.otherPlane,
            P4AOriginalRemainingEighthSources.newCap,
            P4AOriginalRemainingEighthSources.descendingNew,
            P4AOriginalRemainingEighthSources.selectedSum,
            P4AOriginalRemainingEighthSources.selected,A,C,KindRows,kind,mu] at hh ⊢
          linarith
      | seed =>
          have hh := P4AOriginalRemainingEighthSources.source_common_pos h 17
          norm_num [P4AOriginalRemainingEighthSources.commonSlack,
            P4AOriginalRemainingEighthSources.otherPlane,
            P4AOriginalRemainingEighthSources.newCap,
            P4AOriginalRemainingEighthSources.descendingNew,
            P4AOriginalRemainingEighthSources.selectedSum,
            P4AOriginalRemainingEighthSources.selected,A,C,KindRows,kind,mu] at hh ⊢
          linarith
      | nine i =>
          have hh := P4AOriginalRemainingEighthSources.source_common_pos h 34
          have hh' := (P4AOriginalRemainingEighthSources.source_basic h).2.2.2.2.1
          change mu < t 1+t 2 ∧ ∀ j : Fin 4, history t j < C (t 1+t 2)
          refine ⟨?_,hh'⟩
          dsimp [P4AOriginalRemainingEighthSources.commonSlack,
            P4AOriginalRemainingEighthSources.sideSlack] at hh
          linarith
      | fiftyA => exact remaining_winner_side h
      | fiftyD => exact remaining_winner_side h
      | h5 i =>
          have hh := h 17
          have hp := P4AOriginalH5H7SourceDispatch.source_h5_priority h
          change mu < t 1+t 2 ∧ history t 1 < C (t 1+t 2) ∧ C (t 1+t 2) < history t 2
          refine ⟨?_,?_,?_⟩
          · fin_cases i <;>
              norm_num [P4AOriginalRemainingEighthSources.row,
                P4AOriginalRemainingEighthSources.evalRow,
                P4AOriginalFirstFailureH5H7Literal.h5AffineRows,Fin.sum_univ_succ,mu] at hh ⊢ <;>
              linarith
          · simpa [history,P4AOriginalRemainingEighthSources.history,C,
              P4AOriginalFirstFailureH5H7Literal.H3,P4AOriginalFirstFailureH5H7Literal.D23,
              P4AOriginalFirstFailureH5H7Literal.D,
              div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hp.2.1
          · simpa [history,P4AOriginalRemainingEighthSources.history,C,
              P4AOriginalFirstFailureH5H7Literal.H5,P4AOriginalFirstFailureH5H7Literal.D23,
              P4AOriginalFirstFailureH5H7Literal.D,
              div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hp.2.2
      | h7 i =>
          have hh := h 17
          have hp := P4AOriginalH5H7SourceDispatch.source_h7_priority h
          change mu < t 1+t 2 ∧ history t 1 < C (t 1+t 2) ∧
            history t 2 < C (t 1+t 2) ∧ C (t 1+t 2) < history t 3
          refine ⟨?_,?_,?_,?_⟩
          · fin_cases i <;>
              norm_num [P4AOriginalRemainingEighthSources.row,
                P4AOriginalRemainingEighthSources.evalRow,
                P4AOriginalFirstFailureH5H7Literal.h7AffineRows,Fin.sum_univ_succ,mu] at hh ⊢ <;>
              linarith
          · simpa [history,P4AOriginalRemainingEighthSources.history,C,
              P4AOriginalFirstFailureH5H7Literal.H3,P4AOriginalFirstFailureH5H7Literal.D23,
              P4AOriginalFirstFailureH5H7Literal.D,
              div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hp.2.1
          · simpa [history,P4AOriginalRemainingEighthSources.history,C,
              P4AOriginalFirstFailureH5H7Literal.H5,P4AOriginalFirstFailureH5H7Literal.D23,
              P4AOriginalFirstFailureH5H7Literal.D,
              div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hp.2.2.1
          · simpa [history,P4AOriginalRemainingEighthSources.history,C,
              P4AOriginalFirstFailureH5H7Literal.H7,P4AOriginalFirstFailureH5H7Literal.D23,
              P4AOriginalFirstFailureH5H7Literal.D,
              div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hp.2.2.2
  | descending i =>
      have hs := (OriginalDescendingFifteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      exact hs.descending
  | ascendingPair i =>
      have hs := (OriginalAscendingThirteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t).mp h
      exact hs.ascendingThird
  | h3 i =>
      have hs := (P4AOriginalFirstFailureH3SourceSemantics.sourceAffineGuard_iff_StrictH3 i t).mp h
      refine ⟨hs.d23_high,?_⟩
      simpa [history,P4AOriginalRemainingEighthSources.history,C,
        P4AOriginalFirstFailureH3Literal.H3,P4AOriginalFirstFailureH3Literal.D23,
        P4AOriginalFirstFailureH3Literal.D,
        div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hs.first_H3_failure

def kindWinner (k : Fin 9) : ℕ := if k.val ≤ 1 then 6 else if k.val = 3 ∨ k.val = 4 then 50 else 9

theorem kindWinner_eq (c : Cell) : kindWinner (kind c) = winner c := by
  cases c with
  | remaining c => cases c <;> norm_num [kindWinner,kind,winner,P4AOriginalRemainingEighthSources.winner]
  | descending i => norm_num [kindWinner,kind,winner]
  | ascendingPair i => norm_num [kindWinner,kind,winner]
  | h3 i => norm_num [kindWinner,kind,winner]

theorem common_source_kind {c d : Cell} {t : Point}
    (hc : Source c t) (hd : Source d t) : kind c = kind d := by
  have hw : kindWinner (kind c) = kindWinner (kind d) := by
    rw [kindWinner_eq,kindWinner_eq,common_source_winner hc hd]
  have hkc := source_kind_rows hc
  have hkd := source_kind_rows hd
  generalize kind c = i at hw hkc ⊢
  generalize kind d = j at hw hkd ⊢
  fin_cases i <;> fin_cases j <;> norm_num [kindWinner,KindRows] at hw hkc hkd ⊢
  all_goals first
    | linarith
    | linarith [hkc.1]
    | linarith [hkd.1]
    | linarith [hkc.2 (1 : Fin 4),hkd.2]
    | linarith [hkd.2 (1 : Fin 4),hkc.2]
    | linarith [hkc.2 (2 : Fin 4),hkd.2.2]
    | linarith [hkd.2 (2 : Fin 4),hkc.2.2]
    | linarith [hkc.2 (3 : Fin 4),hkd.2.2.2]
    | linarith [hkd.2 (3 : Fin 4),hkc.2.2.2]
    | linarith [hkc.2,hkd.2.1]
    | linarith [hkd.2,hkc.2.1]
    | linarith [hkc.2.2,hkd.2.2.1]
    | linarith [hkd.2.2,hkc.2.2.1]

/-- The original finite left-pattern lists separate labels of the same
chronological kind.  Seed7 is included once and differs from all fourteen
remaining ascending navigation entries.  UNEVALUATED source-label fact. -/
theorem same_kind_separator (c d : Cell) (hcd : c ≠ d) (hk : kind c = kind d) :
    ∃ m ∈ Finset.Icc 1 63, m ≠ winner c ∧ m ≠ winner d ∧
      ((m ∈ leftMasks c ∧ m ∉ leftMasks d) ∨
        (m ∈ leftMasks d ∧ m ∉ leftMasks c)) := by
  have hall : ∀ c d : Cell, c ≠ d → kind c = kind d →
      ∃ m ∈ Finset.Icc 1 63, m ≠ winner c ∧ m ≠ winner d ∧
        ((m ∈ leftMasks c ∧ m ∉ leftMasks d) ∨
          (m ∈ leftMasks d ∧ m ∉ leftMasks c)) := by decide
  exact hall c d hcd hk

private theorem planes_incompatible (s R : ℝ) (hR : R ≤ cap)
    (ha : A s < R) (hc : C s < R) : False := by
  dsimp [A,C,cap] at *
  linarith

/-- Full original87 semantic ownership, derived from all original rows. -/
theorem source_owner_unique {c d : Cell} {t : Point}
    (hc : Source c t) (hd : Source d t) : c = d := by
  by_contra hne
  have hw := common_source_winner hc hd
  have hcmp : comparison c t = comparison d t := by
    rw [← source_winner_tent hc,← source_winner_tent hd,hw]
  obtain ⟨m,hm,hmc,hmd,hsep⟩ := same_kind_separator c d hne (common_source_kind hc hd)
  have hpc := source_old_planes hc m hm hmc
  have hpd := source_old_planes hd m hm hmd
  rw [← hcmp] at hpd
  rcases hsep with ⟨hmc',hmd'⟩ | ⟨hmd',hmc'⟩
  · rw [plane,if_pos hmc'] at hpc
    rw [plane,if_neg hmd'] at hpd
    exact planes_incompatible _ _ (source_comparison_le_cap hc) hpc hpd
  · rw [plane,if_neg hmc'] at hpc
    rw [plane,if_pos hmd'] at hpd
    exact planes_incompatible _ _ (source_comparison_le_cap hc) hpd hpc

theorem source_cells_pairwise_disjoint {c d : Cell} (hcd : c ≠ d) :
    Disjoint {t : Point | Source c t} {t : Point | Source d t} := by
  exact Set.disjoint_left.mpr (fun _ hc hd => hcd (source_owner_unique hc hd))

end
end ImbalancedChen.P4AOriginalFull87Ownership
