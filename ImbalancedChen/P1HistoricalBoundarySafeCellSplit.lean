import ImbalancedChen.P1HistoricalLevelCheckPreservation
import ImbalancedChen.P1HistoricalFourthUniformCellMargin
import ImbalancedChen.ActualHistoricalFourthResidualDictionaryP1

/-!
# Finite safe/boundary split of the actual fourth correction

Safe means that the existing rational whole-cell margin check returns true.
Boundary means that the same check returns false; this name makes no claim
about the size or analytic negligibility of that remaining finite family.

Only fourth selections are restricted. Third selections and fifth cap data
are retained, but old5 and unselected fifth fallbacks are recomputed from
the restricted fourth selection. No fifth-saving invariance is asserted.
All identities below are finite; no integral or mean supplier is added.
Imports of sibling drafts describe later integration, not an actual edit.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

namespace HistoricalPrefixCapData

def p1FourthSafeCells (D : HistoricalPrefixCapData) (delta rho : ℚ) :
    Finset (Fin 4 → Fin (D.m + 1)) :=
  D.cells4.filter (fun j => D.p1_fourthCellMarginCheck delta rho j = true)

def p1FourthBoundaryCells (D : HistoricalPrefixCapData) (delta rho : ℚ) :
    Finset (Fin 4 → Fin (D.m + 1)) :=
  D.cells4.filter (fun j => D.p1_fourthCellMarginCheck delta rho j = false)

theorem p1FourthSafeCells_subset (D : HistoricalPrefixCapData) (delta rho : ℚ) :
    D.p1FourthSafeCells delta rho ⊆ D.cells4 := by
  intro j hj
  exact (Finset.mem_filter.mp hj).1

theorem p1FourthBoundaryCells_subset (D : HistoricalPrefixCapData) (delta rho : ℚ) :
    D.p1FourthBoundaryCells delta rho ⊆ D.cells4 := by
  intro j hj
  exact (Finset.mem_filter.mp hj).1

theorem p1FourthSafeCells_pass (D : HistoricalPrefixCapData) (delta rho : ℚ)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.p1FourthSafeCells delta rho) :
    D.p1_fourthCellMarginCheck delta rho j = true := by
  exact (Finset.mem_filter.mp hj).2

theorem p1FourthBoundaryCells_fail (D : HistoricalPrefixCapData) (delta rho : ℚ)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.p1FourthBoundaryCells delta rho) :
    D.p1_fourthCellMarginCheck delta rho j = false := by
  exact (Finset.mem_filter.mp hj).2

theorem p1FourthSafeBoundary_disjoint (D : HistoricalPrefixCapData) (delta rho : ℚ) :
    Disjoint (D.p1FourthSafeCells delta rho) (D.p1FourthBoundaryCells delta rho) := by
  apply Finset.disjoint_left.mpr
  intro j hs hb
  have htrue := D.p1FourthSafeCells_pass delta rho j hs
  have hfalse := D.p1FourthBoundaryCells_fail delta rho j hb
  rw [htrue] at hfalse
  cases hfalse

theorem p1FourthSafeBoundary_union (D : HistoricalPrefixCapData) (delta rho : ℚ) :
    D.p1FourthSafeCells delta rho ∪ D.p1FourthBoundaryCells delta rho = D.cells4 := by
  ext j
  cases hc : D.p1_fourthCellMarginCheck delta rho j <;>
    simp [p1FourthSafeCells, p1FourthBoundaryCells, hc]

/-- Restrict only fourth selection, preserving the actual third and fifth
table fields. Fifth inherited values are not table fields. -/
def p1RestrictFourth (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) : HistoricalPrefixCapData :=
  { D with cells4 := D.cells4 ∩ J }

theorem p1RestrictFourth_eq_restrictSelections (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) :
    D.p1RestrictFourth J = D.p1RestrictSelections D.cells3 J D.cells5 := by
  simp only [p1RestrictFourth, p1RestrictSelections, Finset.inter_self]

theorem p1RestrictFourth_thirdData (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) :
    (D.p1RestrictFourth J).cells3 = D.cells3 ∧
      (D.p1RestrictFourth J).cap3 = D.cap3 := by
  exact ⟨rfl, rfl⟩

theorem p1RestrictFourth_fifthData (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) :
    (D.p1RestrictFourth J).cells5 = D.cells5 ∧
      (D.p1RestrictFourth J).cap5 = D.cap5 := by
  exact ⟨rfl, rfl⟩

theorem p1RestrictFourth_old4 (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) (j : Fin 4 → Fin (D.m + 1)) :
    (D.p1RestrictFourth J).old4 j = D.old4 j := by
  rfl

/-- Exact dependence of the fifth old value on the retained fourth owner. -/
theorem p1RestrictFourth_old5_exact (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) (j : Fin 5 → Fin (D.m + 1)) :
    (D.p1RestrictFourth J).old5 j =
      if historicalPrefixProject (by omega : 4 ≤ 5) j ∈ D.cells4 ∩ J then
        D.cap4 (historicalPrefixProject (by omega : 4 ≤ 5) j) else
        D.old4 (historicalPrefixProject (by omega : 4 ≤ 5) j) := by
  rfl

/-- Fifth cap data remain, whereas fifth fallback now reads the restricted
fourth owner and its unchanged third ancestor. -/
theorem p1RestrictFourth_cell5_exact (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) (j : Fin 5 → Fin (D.m + 1)) :
    (D.p1RestrictFourth J).cell5 j =
      if j ∈ D.cells5 then D.cap5 j else
        if historicalPrefixProject (by omega : 4 ≤ 5) j ∈ D.cells4 ∩ J then
          D.cap4 (historicalPrefixProject (by omega : 4 ≤ 5) j) else
          D.old4 (historicalPrefixProject (by omega : 4 ≤ 5) j) := by
  rfl

/-- On an unselected fifth owner, the actual fifth exponent now reads
the fourth-restricted value; removing that fourth owner exposes old4. -/
theorem p1RestrictFourth_exponent5_unselected_on_cell (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (j : Fin 5 → Fin (D.m + 1)) (hj : j ∉ D.cells5)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictFourth J).exponent5 t =
      if historicalPrefixProject (by omega : 4 ≤ 5) j ∈ D.cells4 ∩ J then
        D.cap4 (historicalPrefixProject (by omega : 4 ≤ 5) j) else
        D.old4 (historicalPrefixProject (by omega : 4 ≤ 5) j) := by
  rw [(D.p1RestrictFourth J).exponent5_on_cell hab t j ht,
    D.p1RestrictFourth_cell5_exact J j, if_neg hj]

theorem p1RestrictFourth_old5_le (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) (hcheck : D.levelCheck = true)
    (j : Fin 5 → Fin (D.m + 1)) :
    (D.p1RestrictFourth J).old5 j ≤ D.old5 j := by
  rw [D.p1RestrictFourth_eq_restrictSelections J]
  exact D.p1RestrictSelections_old5_le D.cells3 J D.cells5 hcheck j

/-- Retaining every original fifth cap is legal after fourth deletion:
the recomputed old5 can only decrease. -/
theorem p1RestrictFourth_old5_le_cap5 (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) (hcheck : D.levelCheck = true)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5) :
    (D.p1RestrictFourth J).old5 j ≤ D.cap5 j := by
  exact (D.p1RestrictFourth_old5_le J hcheck j).trans
    ((D.levelCheck_sound hcheck).2.2 j hj)

theorem p1RestrictFourth_levelCheck (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) (hcheck : D.levelCheck = true) :
    (D.p1RestrictFourth J).levelCheck = true := by
  rw [D.p1RestrictFourth_eq_restrictSelections J]
  exact D.p1RestrictSelections_levelCheck D.cells3 J D.cells5 hcheck

/-- Outside fifth selection, the restricted fourth level is inherited.
The right side intentionally uses the restricted data. -/
theorem p1RestrictFourth_level5_outside (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) (N : ℝ) (history : List ℕ)
    (hlen : history.length = 5)
    (hout : ∀ j ∈ D.cells5, primeHistoryLogCoordinates N 5 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictFourth J).level5 N history =
      (D.p1RestrictFourth J).level4 N (rosserAncestor 4 history) := by
  exact (D.p1RestrictFourth J).level5_outside N history hlen hout

theorem p1FourthSafeCells_marginCheck (D : HistoricalPrefixCapData) (delta rho : ℚ) :
    D.p1_fourthSelectedMarginCheck (D.p1FourthSafeCells delta rho) delta rho = true := by
  simp only [p1_fourthSelectedMarginCheck, decide_eq_true_eq]
  intro j hj
  exact D.p1FourthSafeCells_pass delta rho j hj

theorem p1FourthSafeRestricted_marginCheck (D : HistoricalPrefixCapData) (delta rho : ℚ) :
    (D.p1RestrictFourth (D.p1FourthSafeCells delta rho)).p1_fourthSelectedMarginCheck
      (D.p1RestrictFourth (D.p1FourthSafeCells delta rho)).cells4 delta rho = true := by
  simp only [p1_fourthSelectedMarginCheck, decide_eq_true_eq]
  intro j hj
  change D.p1_fourthCellMarginCheck delta rho j = true
  exact D.p1FourthSafeCells_pass delta rho j (Finset.mem_inter.mp hj).2

theorem p1FourthSafeBoundary_levelChecks (D : HistoricalPrefixCapData) (delta rho : ℚ)
    (hcheck : D.levelCheck = true) :
    (D.p1RestrictFourth (D.p1FourthSafeCells delta rho)).levelCheck = true ∧
      (D.p1RestrictFourth (D.p1FourthBoundaryCells delta rho)).levelCheck = true := by
  exact ⟨D.p1RestrictFourth_levelCheck (D.p1FourthSafeCells delta rho) hcheck,
    D.p1RestrictFourth_levelCheck (D.p1FourthBoundaryCells delta rho) hcheck⟩

/-- Restricting fourth selection preserves the original cell correction
on every retained cell; the admitted historical third frontier is identical. -/
theorem p1RestrictFourth_cellCorrection (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) (hab : D.a ≤ D.b) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4 ∩ J) :
    (D.p1RestrictFourth J).fourthCellPrimeCorrectionP1 N cap j =
      D.fourthCellPrimeCorrectionP1 N cap j := by
  unfold fourthCellPrimeCorrectionP1
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
  · have hdiff : (D.p1RestrictFourth J).fourthTupleResidualDifferenceP1 N cap p =
        D.fourthTupleResidualDifferenceP1 N cap p := by
      calc
        _ = fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p -
            fourthTuplePlusResidualP1 N cap (D.cap4 j : ℝ) p :=
          (D.p1RestrictFourth J).fourthTupleResidualDifference_on_cellP1 hab N cap j hj p ht
        _ = _ := (D.fourthTupleResidualDifference_on_cellP1 hab N cap j
          (Finset.mem_inter.mp hj).1 p ht).symm
    rw [if_pos ht, if_pos ht, hdiff]
  · rw [if_neg ht, if_neg ht]

theorem p1RestrictFourth_correction_eq_selected_cells (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) (hab : D.a ≤ D.b) (N cap : ℕ) :
    (D.p1RestrictFourth J).fourthPrimeCorrectionP1 N cap =
      ∑ j ∈ D.cells4 ∩ J, D.fourthCellPrimeCorrectionP1 N cap j := by
  rw [(D.p1RestrictFourth J).fourthPrimeCorrection_eq_cellsP1 hab N cap]
  apply Finset.sum_congr rfl
  intro j hj
  exact D.p1RestrictFourth_cellCorrection J hab N cap j hj

/-- Strict finite split of the original correction. Neither term is
claimed to have a sign or to be analytically negligible. -/
theorem p1FourthCorrection_safeBoundary_split (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (delta rho : ℚ) (N cap : ℕ) :
    D.fourthPrimeCorrectionP1 N cap =
      (∑ j ∈ D.p1FourthSafeCells delta rho, D.fourthCellPrimeCorrectionP1 N cap j) +
        ∑ j ∈ D.p1FourthBoundaryCells delta rho, D.fourthCellPrimeCorrectionP1 N cap j := by
  rw [D.fourthPrimeCorrection_eq_cellsP1 hab N cap,
    ← D.p1FourthSafeBoundary_union delta rho,
    Finset.sum_union (D.p1FourthSafeBoundary_disjoint delta rho)]

/-- Each piece is also the actual correction for its fourth-restricted
table, with the original third parent and all original fifth cap fields. -/
theorem p1FourthCorrection_eq_restricted_safe_add_boundary (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (delta rho : ℚ) (N cap : ℕ) :
    D.fourthPrimeCorrectionP1 N cap =
      (D.p1RestrictFourth (D.p1FourthSafeCells delta rho)).fourthPrimeCorrectionP1 N cap +
        (D.p1RestrictFourth (D.p1FourthBoundaryCells delta rho)).fourthPrimeCorrectionP1 N cap := by
  rw [D.p1RestrictFourth_correction_eq_selected_cells (D.p1FourthSafeCells delta rho) hab N cap,
    D.p1RestrictFourth_correction_eq_selected_cells (D.p1FourthBoundaryCells delta rho) hab N cap]
  have hs : D.cells4 ∩ D.p1FourthSafeCells delta rho = D.p1FourthSafeCells delta rho := by
    ext j
    simp only [p1FourthSafeCells, Finset.mem_inter, Finset.mem_filter]
    tauto
  have hb : D.cells4 ∩ D.p1FourthBoundaryCells delta rho = D.p1FourthBoundaryCells delta rho := by
    ext j
    simp only [p1FourthBoundaryCells, Finset.mem_inter, Finset.mem_filter]
    tauto
  rw [hs, hb]
  exact D.p1FourthCorrection_safeBoundary_split hab delta rho N cap

/-- The identical split for the normalized actual historical fourth
saving uses only the previously proved finite dictionary. -/
theorem p1ActualFourthSaving_safeBoundary_split (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (delta rho : ℚ) (N cap : ℕ) :
    actualHistoricalFourthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap ((N : ℝ) ^ (D.b : ℝ)) *
        Real.log (N : ℝ) / singularSeries N =
      (∑ j ∈ D.p1FourthSafeCells delta rho, D.fourthCellPrimeCorrectionP1 N cap j) +
        ∑ j ∈ D.p1FourthBoundaryCells delta rho, D.fourthCellPrimeCorrectionP1 N cap j := by
  rw [D.actualHistoricalFourthSaving_eq_fourthPrimeCorrectionP1 N cap]
  exact D.p1FourthCorrection_safeBoundary_split hab delta rho N cap

end HistoricalPrefixCapData

end

end ImbalancedChen
