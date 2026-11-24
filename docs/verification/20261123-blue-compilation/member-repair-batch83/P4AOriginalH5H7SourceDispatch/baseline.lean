import ImbalancedChen.P4AOriginalRemainingEighthSources

/-!
SOURCE ONLY / UNCOMPILED. Exact redundant-source-conjunct elimination
in the old literal H5/H7 guards. Actual parent admission/upper tests remain.
No claimed full87 policy is introduced. Finite symbolic bodies UNEVALUATED.
-/
namespace ImbalancedChen.P4AOriginalH5H7SourceDispatch
noncomputable section
open scoped Classical BigOperators
open P4AOriginalRemainingEighthSources

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h5_priority_rows (i : Fin 7) (t : Point) :
    evalRow (row (.h5 i) 36) t =
      P4AOriginalFirstFailureH5H7Literal.D23 t-P4AOriginalFirstFailureH5H7Literal.H1 t ∧
    evalRow (row (.h5 i) 37) t =
      P4AOriginalFirstFailureH5H7Literal.D23 t-P4AOriginalFirstFailureH5H7Literal.H3 t ∧
    evalRow (row (.h5 i) 18) t =
      P4AOriginalFirstFailureH5H7Literal.H5 t-P4AOriginalFirstFailureH5H7Literal.D23 t := by
  fin_cases i
  all_goals repeat' constructor
  all_goals norm_num [row,evalRow,Fin.sum_univ_succ,
    P4AOriginalFirstFailureH5H7Literal.h5AffineRows,
    P4AOriginalFirstFailureH5H7Literal.D23,P4AOriginalFirstFailureH5H7Literal.D,
    P4AOriginalFirstFailureH5H7Literal.H1,P4AOriginalFirstFailureH5H7Literal.H3,
    P4AOriginalFirstFailureH5H7Literal.H5] <;> ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h7_priority_rows (i : Fin 10) (t : Point) :
    evalRow (row (.h7 i) 36) t =
      P4AOriginalFirstFailureH5H7Literal.D23 t-P4AOriginalFirstFailureH5H7Literal.H1 t ∧
    evalRow (row (.h7 i) 37) t =
      P4AOriginalFirstFailureH5H7Literal.D23 t-P4AOriginalFirstFailureH5H7Literal.H3 t ∧
    evalRow (row (.h7 i) 38) t =
      P4AOriginalFirstFailureH5H7Literal.D23 t-P4AOriginalFirstFailureH5H7Literal.H5 t ∧
    evalRow (row (.h7 i) 18) t =
      P4AOriginalFirstFailureH5H7Literal.H7 t-P4AOriginalFirstFailureH5H7Literal.D23 t := by
  fin_cases i
  all_goals repeat' constructor
  all_goals norm_num [row,evalRow,Fin.sum_univ_succ,
    P4AOriginalFirstFailureH5H7Literal.h7AffineRows,
    P4AOriginalFirstFailureH5H7Literal.D23,P4AOriginalFirstFailureH5H7Literal.D,
    P4AOriginalFirstFailureH5H7Literal.H1,P4AOriginalFirstFailureH5H7Literal.H3,
    P4AOriginalFirstFailureH5H7Literal.H5,P4AOriginalFirstFailureH5H7Literal.H7] <;> ring

theorem source_h5_priority {i : Fin 7} {t : Point} (h : Source (.h5 i) t) :
    P4AOriginalFirstFailureH5H7Literal.H5Priority t := by
  have hh := h5_priority_rows i t
  have h1 := h 36
  have h3 := h 37
  have h5 := h 18
  rw [hh.1] at h1
  rw [hh.2.1] at h3
  rw [hh.2.2] at h5
  exact ⟨sub_pos.mp h1,sub_pos.mp h3,sub_pos.mp h5⟩

theorem source_h7_priority {i : Fin 10} {t : Point} (h : Source (.h7 i) t) :
    P4AOriginalFirstFailureH5H7Literal.H7Priority t := by
  have hh := h7_priority_rows i t
  have h1 := h 36
  have h3 := h 37
  have h5 := h 38
  have h7 := h 18
  rw [hh.1] at h1
  rw [hh.2.1] at h3
  rw [hh.2.2.1] at h5
  rw [hh.2.2.2] at h7
  exact ⟨sub_pos.mp h1,sub_pos.mp h3,sub_pos.mp h5,sub_pos.mp h7⟩

theorem h5ActualGuard_iff_source (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) :
    P4AOriginalFirstFailureH5H7Literal.H5ActualGuard N lambda6 pre ↔
    pre.length = 8 ∧ ∃ i : Fin 7,
      let t := primeHistoryLogCoordinates N 8 pre
      Source (.h5 i) t ∧
      P4AOriginalFirstFailureH5H7Literal.H7 t < lambda6 (rosserAncestor 6 pre) ∧
      lambda6 (rosserAncestor 6 pre) ≤ P4AOriginalFirstFailureH5H7Literal.R6 t := by
  constructor
  · rintro ⟨hl,i,ha,_hp,_hb,hh,hu,_hg⟩
    exact ⟨hl,i,ha,hh,hu⟩
  · rintro ⟨hl,i,ha,hh,hu⟩
    have hb := (source_basic ha).2.2.2.2.1 3
    have hg := (source_basic ha).2.2.2.2.2.2.1
    refine ⟨hl,i,ha,source_h5_priority ha,?_,hh,hu,?_⟩
    · exact hb
    · simpa [comparison,newCap,selectedSum,selected,descendingNew,eta,
        P4AOriginalFirstFailureH5H7Literal.R6,P4AOriginalFirstFailureH5H7Literal.M8,
        VariableEnvelope.A,P4AOriginalFirstFailureH5H7Literal.A,add_assoc] using hg

theorem h7ActualGuard_iff_source (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) :
    P4AOriginalFirstFailureH5H7Literal.H7ActualGuard N lambda6 pre ↔
    pre.length = 8 ∧ ∃ i : Fin 10,
      let t := primeHistoryLogCoordinates N 8 pre
      Source (.h7 i) t ∧
      P4AOriginalFirstFailureH5H7Literal.H7 t < lambda6 (rosserAncestor 6 pre) ∧
      lambda6 (rosserAncestor 6 pre) ≤ P4AOriginalFirstFailureH5H7Literal.R6 t := by
  constructor
  · rintro ⟨hl,i,ha,_hp,_hb,hh,hu,_hg⟩
    exact ⟨hl,i,ha,hh,hu⟩
  · rintro ⟨hl,i,ha,hh,hu⟩
    have hb := (source_basic ha).2.2.2.2.1 3
    have hg := (source_basic ha).2.2.2.2.2.2.1
    refine ⟨hl,i,ha,source_h7_priority ha,?_,hh,hu,?_⟩
    · exact hb
    · simpa [comparison,newCap,selectedSum,selected,descendingNew,eta,
        P4AOriginalFirstFailureH5H7Literal.R6,P4AOriginalFirstFailureH5H7Literal.M8,
        VariableEnvelope.A,P4AOriginalFirstFailureH5H7Literal.A,add_assoc] using hg

end
end ImbalancedChen.P4AOriginalH5H7SourceDispatch
