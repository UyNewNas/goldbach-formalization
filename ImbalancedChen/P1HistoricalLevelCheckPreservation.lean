import ImbalancedChen.HistoricalPrefixCertificate

/-!
# Restricting actual historical selected-cell tables

These constructions change the selected finsets of the existing
`HistoricalPrefixCapData`. The original `levelCheck` is used unchanged.
Removing earlier selections changes later inherited values, so the
comparison proofs follow `cell3 -> old4 -> cell4 -> old5` explicitly.

This source-only draft supplies finite table operations and exact inherited
fallback. It supplies neither concrete manuscript tables nor an integral
or distribution estimate. No compilation is claimed.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

namespace HistoricalPrefixCapData

/-- Keep arbitrary subfamilies of all three selected-cell families.
The cap tables, mesh and global fallback remain the original data. -/
def p1RestrictSelections (D : HistoricalPrefixCapData)
    (J3 : Finset (Fin 3 → Fin (D.m + 1)))
    (J4 : Finset (Fin 4 → Fin (D.m + 1)))
    (J5 : Finset (Fin 5 → Fin (D.m + 1))) : HistoricalPrefixCapData :=
  { D with
    cells3 := D.cells3 ∩ J3
    cells4 := D.cells4 ∩ J4
    cells5 := D.cells5 ∩ J5 }

theorem p1RestrictSelections_old4_exact (D : HistoricalPrefixCapData)
    (J3 : Finset (Fin 3 → Fin (D.m + 1)))
    (J4 : Finset (Fin 4 → Fin (D.m + 1)))
    (J5 : Finset (Fin 5 → Fin (D.m + 1))) (j : Fin 4 → Fin (D.m + 1)) :
    (D.p1RestrictSelections J3 J4 J5).old4 j =
      if historicalPrefixProject (by omega : 3 ≤ 4) j ∈ D.cells3 ∩ J3 then
        D.cap3 (historicalPrefixProject (by omega : 3 ≤ 4) j) else D.old := by
  rfl

/-- The nested fallback records both actual ancestor selections. -/
theorem p1RestrictSelections_old5_exact (D : HistoricalPrefixCapData)
    (J3 : Finset (Fin 3 → Fin (D.m + 1)))
    (J4 : Finset (Fin 4 → Fin (D.m + 1)))
    (J5 : Finset (Fin 5 → Fin (D.m + 1))) (j : Fin 5 → Fin (D.m + 1)) :
    (D.p1RestrictSelections J3 J4 J5).old5 j =
      if historicalPrefixProject (by omega : 4 ≤ 5) j ∈ D.cells4 ∩ J4 then
        D.cap4 (historicalPrefixProject (by omega : 4 ≤ 5) j) else
        if historicalPrefixProject (by omega : 3 ≤ 4)
            (historicalPrefixProject (by omega : 4 ≤ 5) j) ∈ D.cells3 ∩ J3 then
          D.cap3 (historicalPrefixProject (by omega : 3 ≤ 4)
            (historicalPrefixProject (by omega : 4 ≤ 5) j)) else D.old := by
  rfl

theorem p1Old_le_cell3 (D : HistoricalPrefixCapData)
    (hcheck : D.levelCheck = true) (j : Fin 3 → Fin (D.m + 1)) :
    D.old ≤ D.cell3 j := by
  unfold cell3
  split_ifs with hj
  · exact (D.levelCheck_sound hcheck).1 j hj
  · exact le_rfl

theorem p1Old4_le_cell4 (D : HistoricalPrefixCapData)
    (hcheck : D.levelCheck = true) (j : Fin 4 → Fin (D.m + 1)) :
    D.old4 j ≤ D.cell4 j := by
  unfold cell4
  split_ifs with hj
  · exact (D.levelCheck_sound hcheck).2.1 j hj
  · exact le_rfl

theorem p1Old5_le_cell5 (D : HistoricalPrefixCapData)
    (hcheck : D.levelCheck = true) (j : Fin 5 → Fin (D.m + 1)) :
    D.old5 j ≤ D.cell5 j := by
  unfold cell5
  split_ifs with hj
  · exact (D.levelCheck_sound hcheck).2.2 j hj
  · exact le_rfl

theorem p1RestrictSelections_cell3_le (D : HistoricalPrefixCapData)
    (J3 : Finset (Fin 3 → Fin (D.m + 1)))
    (J4 : Finset (Fin 4 → Fin (D.m + 1)))
    (J5 : Finset (Fin 5 → Fin (D.m + 1)))
    (hcheck : D.levelCheck = true) (j : Fin 3 → Fin (D.m + 1)) :
    (D.p1RestrictSelections J3 J4 J5).cell3 j ≤ D.cell3 j := by
  by_cases hj : j ∈ D.cells3 ∩ J3
  · have hD : j ∈ D.cells3 := (Finset.mem_inter.mp hj).1
    apply le_of_eq
    simp only [cell3, p1RestrictSelections, if_pos hj, if_pos hD]
  · change (if j ∈ D.cells3 ∩ J3 then D.cap3 j else D.old) ≤ D.cell3 j
    rw [if_neg hj]
    exact D.p1Old_le_cell3 hcheck j

/-- The inherited fourth value is recomputed from the restricted third
selection; it is not treated as an unchanged table field. -/
theorem p1RestrictSelections_old4_le (D : HistoricalPrefixCapData)
    (J3 : Finset (Fin 3 → Fin (D.m + 1)))
    (J4 : Finset (Fin 4 → Fin (D.m + 1)))
    (J5 : Finset (Fin 5 → Fin (D.m + 1)))
    (hcheck : D.levelCheck = true) (j : Fin 4 → Fin (D.m + 1)) :
    (D.p1RestrictSelections J3 J4 J5).old4 j ≤ D.old4 j := by
  exact D.p1RestrictSelections_cell3_le J3 J4 J5 hcheck
    (historicalPrefixProject (by omega : 3 ≤ 4) j)

theorem p1RestrictSelections_cell4_le (D : HistoricalPrefixCapData)
    (J3 : Finset (Fin 3 → Fin (D.m + 1)))
    (J4 : Finset (Fin 4 → Fin (D.m + 1)))
    (J5 : Finset (Fin 5 → Fin (D.m + 1)))
    (hcheck : D.levelCheck = true) (j : Fin 4 → Fin (D.m + 1)) :
    (D.p1RestrictSelections J3 J4 J5).cell4 j ≤ D.cell4 j := by
  by_cases hj : j ∈ D.cells4 ∩ J4
  · have hD : j ∈ D.cells4 := (Finset.mem_inter.mp hj).1
    apply le_of_eq
    simp only [cell4, p1RestrictSelections, if_pos hj, if_pos hD]
  · change (if j ∈ D.cells4 ∩ J4 then D.cap4 j else
      (D.p1RestrictSelections J3 J4 J5).old4 j) ≤ D.cell4 j
    rw [if_neg hj]
    exact (D.p1RestrictSelections_old4_le J3 J4 J5 hcheck j).trans
      (D.p1Old4_le_cell4 hcheck j)

/-- The inherited fifth value includes both restricted earlier choices. -/
theorem p1RestrictSelections_old5_le (D : HistoricalPrefixCapData)
    (J3 : Finset (Fin 3 → Fin (D.m + 1)))
    (J4 : Finset (Fin 4 → Fin (D.m + 1)))
    (J5 : Finset (Fin 5 → Fin (D.m + 1)))
    (hcheck : D.levelCheck = true) (j : Fin 5 → Fin (D.m + 1)) :
    (D.p1RestrictSelections J3 J4 J5).old5 j ≤ D.old5 j := by
  exact D.p1RestrictSelections_cell4_le J3 J4 J5 hcheck
    (historicalPrefixProject (by omega : 4 ≤ 5) j)

theorem p1RestrictSelections_cell5_le (D : HistoricalPrefixCapData)
    (J3 : Finset (Fin 3 → Fin (D.m + 1)))
    (J4 : Finset (Fin 4 → Fin (D.m + 1)))
    (J5 : Finset (Fin 5 → Fin (D.m + 1)))
    (hcheck : D.levelCheck = true) (j : Fin 5 → Fin (D.m + 1)) :
    (D.p1RestrictSelections J3 J4 J5).cell5 j ≤ D.cell5 j := by
  by_cases hj : j ∈ D.cells5 ∩ J5
  · have hD : j ∈ D.cells5 := (Finset.mem_inter.mp hj).1
    apply le_of_eq
    simp only [cell5, p1RestrictSelections, if_pos hj, if_pos hD]
  · change (if j ∈ D.cells5 ∩ J5 then D.cap5 j else
      (D.p1RestrictSelections J3 J4 J5).old5 j) ≤ D.cell5 j
    rw [if_neg hj]
    exact (D.p1RestrictSelections_old5_le J3 J4 J5 hcheck j).trans
      (D.p1Old5_le_cell5 hcheck j)

/-- Every restricted table passes the literal original three-part check.
The later comparisons use the new inherited old4/old5 values. -/
theorem p1RestrictSelections_levelCheck (D : HistoricalPrefixCapData)
    (J3 : Finset (Fin 3 → Fin (D.m + 1)))
    (J4 : Finset (Fin 4 → Fin (D.m + 1)))
    (J5 : Finset (Fin 5 → Fin (D.m + 1)))
    (hcheck : D.levelCheck = true) :
    (D.p1RestrictSelections J3 J4 J5).levelCheck = true := by
  obtain ⟨h3, h4, h5⟩ := D.levelCheck_sound hcheck
  simp only [levelCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    change j ∈ D.cells3 ∩ J3 at hj
    exact h3 j (Finset.mem_inter.mp hj).1
  · intro j hj
    change j ∈ D.cells4 ∩ J4 at hj
    exact (D.p1RestrictSelections_old4_le J3 J4 J5 hcheck j).trans
      (h4 j (Finset.mem_inter.mp hj).1)
  · intro j hj
    change j ∈ D.cells5 ∩ J5 at hj
    exact (D.p1RestrictSelections_old5_le J3 J4 J5 hcheck j).trans
      (h5 j (Finset.mem_inter.mp hj).1)

/-- Deleted fifth cells return to the restricted fourth ancestor,
including any changed third/fourth selection. -/
theorem p1RestrictSelections_exponent5_deleted (D : HistoricalPrefixCapData)
    (J3 : Finset (Fin 3 → Fin (D.m + 1)))
    (J4 : Finset (Fin 4 → Fin (D.m + 1)))
    (J5 : Finset (Fin 5 → Fin (D.m + 1)))
    (hab : D.a ≤ D.b) (t : Fin 5 → ℝ)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∉ J5)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictSelections J3 J4 J5).exponent5 t =
      (D.p1RestrictSelections J3 J4 J5).old5 j := by
  rw [(D.p1RestrictSelections J3 J4 J5).exponent5_on_cell hab t j ht]
  simp only [cell5, p1RestrictSelections, Finset.mem_inter, hj, and_false, if_false]

/-- Fifth-only restriction retains the exact original lower-rank data. -/
def p1RestrictFifth (D : HistoricalPrefixCapData)
    (J5 : Finset (Fin 5 → Fin (D.m + 1))) : HistoricalPrefixCapData :=
  { D with cells5 := D.cells5 ∩ J5 }

theorem p1RestrictFifth_old5 (D : HistoricalPrefixCapData)
    (J5 : Finset (Fin 5 → Fin (D.m + 1))) (j : Fin 5 → Fin (D.m + 1)) :
    (D.p1RestrictFifth J5).old5 j = D.old5 j := by
  rfl

theorem p1RestrictFifth_levelCheck (D : HistoricalPrefixCapData)
    (J5 : Finset (Fin 5 → Fin (D.m + 1))) (hcheck : D.levelCheck = true) :
    (D.p1RestrictFifth J5).levelCheck = true := by
  have h := D.p1RestrictSelections_levelCheck D.cells3 D.cells4 J5 hcheck
  simpa only [p1RestrictSelections, p1RestrictFifth, Finset.inter_self] using h

/-- A retained fifth owner still reads the original fifth cap. -/
theorem p1RestrictFifth_exponent5_kept (D : HistoricalPrefixCapData)
    (J5 : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (j : Fin 5 → Fin (D.m + 1))
    (hj : j ∈ D.cells5 ∩ J5)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictFifth J5).exponent5 t = D.cap5 j := by
  rw [(D.p1RestrictFifth J5).exponent5_on_cell hab t j ht]
  simp only [cell5, p1RestrictFifth, if_pos hj]

/-- Removing the owner of a fifth cell restores the original complete
fourth ancestor, rather than the global cap or third ancestor. -/
theorem p1RestrictFifth_exponent5_deleted (D : HistoricalPrefixCapData)
    (J5 : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (j : Fin 5 → Fin (D.m + 1)) (hj : j ∉ J5)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictFifth J5).exponent5 t =
      D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t) := by
  have hmem : j ∉ (D.p1RestrictFifth J5).cells5 := by
    intro h
    exact hj (Finset.mem_inter.mp h).2
  rw [(D.p1RestrictFifth J5).exponent5_on_cell hab t j ht]
  rw [cell5, if_neg hmem, D.p1RestrictFifth_old5 J5 j]
  exact (D.exponent4_on_cell hab _ _
    (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 4 ≤ 5) ht)).symm

theorem p1RestrictFifth_level5_deleted (D : HistoricalPrefixCapData)
    (J5 : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ) (hlen : history.length = 5)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∉ J5)
    (ht : primeHistoryLogCoordinates N 5 history ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictFifth J5).level5 N history =
      D.level4 N (rosserAncestor 4 history) := by
  unfold level5 level4
  rw [D.p1RestrictFifth_exponent5_deleted J5 hab _ j hj ht,
    primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 4 ≤ 5) hlen]

/-- The outside fallback holds globally, including outside the mesh. -/
theorem p1RestrictFifth_level5_outside (D : HistoricalPrefixCapData)
    (J5 : Finset (Fin 5 → Fin (D.m + 1)))
    (N : ℝ) (history : List ℕ) (hlen : history.length = 5)
    (hout : ∀ j ∈ D.cells5 ∩ J5, primeHistoryLogCoordinates N 5 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictFifth J5).level5 N history =
      D.level4 N (rosserAncestor 4 history) := by
  exact (D.p1RestrictFifth J5).level5_outside N history hlen hout

/-- Any function of the restricted cap has the exact selected-cell
difference, with the original historical fourth old cap on each cell. -/
theorem p1RestrictFifth_apply_sub (D : HistoricalPrefixCapData)
    (J5 : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (f : ℚ → ℝ) :
    f ((D.p1RestrictFifth J5).exponent5 t) -
        f (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t)) =
      ∑ j ∈ D.cells5 ∩ J5,
        if t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap5 j) - f (D.old5 j) else 0 := by
  exact (D.p1RestrictFifth J5).exponent5_apply_sub hab t f

/-- Empty fifth selection deletes the entire fifth update while retaining
the historical fourth fallback at every actual history of length five. -/
theorem p1RestrictFifth_empty_level5 (D : HistoricalPrefixCapData)
    (N : ℝ) (history : List ℕ) (hlen : history.length = 5) :
    (D.p1RestrictFifth ∅).level5 N history =
      D.level4 N (rosserAncestor 4 history) := by
  apply D.p1RestrictFifth_level5_outside ∅ N history hlen
  intro j hj
  exact False.elim (by simpa using hj)

end HistoricalPrefixCapData

end

end ImbalancedChen
