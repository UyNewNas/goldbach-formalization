import ImbalancedChen.ActualHistoricalFifthCellIntegral

/-!
A rational witness distinguishes the original first cap, the effective
third parent cap, and the inherited fourth residual cap.  It passes the
historical parent but fails the ordinary old parent, and its fifth cube is
old-rejected and new-accepted.  This is a regression witness for the
historical dictionary, not an adopted manuscript certificate.
-/

open ImbalancedChen
open scoped Classical BigOperators

namespace P1HistoricalCellProbe

noncomputable section

def table : HistoricalPrefixCapData where
  a := 1 / 100
  b := 1 / 4
  m := 0
  old := 1 / 2
  cells3 := {fun _ : Fin 3 => (0 : Fin 1)}
  cap3 := fun _ => 3 / 5
  cells4 := {fun _ : Fin 4 => (0 : Fin 1)}
  cap4 := fun _ => 5 / 8
  cells5 := {fun _ : Fin 5 => (0 : Fin 1)}
  cap5 := fun _ => 2 / 3

def cell : Fin 5 → Fin (table.m + 1) := fun _ => 0

def witness : Fin 5 → ℝ := ![3 / 20, 3 / 25, 1 / 10, 9 / 100, 13 / 200]

theorem table_levelCheck : table.levelCheck = true := by
  decide +kernel

private theorem table_cell3_eq (j : Fin 3 → Fin (table.m + 1)) :
    table.cell3 j = (3 / 5 : ℚ) := by
  have hm : j ∈ table.cells3 := by
    change j ∈ {fun _ : Fin 3 => (0 : Fin 1)}
    apply Finset.mem_singleton.mpr
    funext i
    exact Fin.eq_zero (j i)
  rw [HistoricalPrefixCapData.cell3, if_pos hm]
  rfl

private theorem table_old5_eq (j : Fin 5 → Fin (table.m + 1)) :
    table.old5 j = (5 / 8 : ℚ) := by
  let j4 := historicalPrefixProject (by omega : 4 ≤ 5) j
  have hm : j4 ∈ table.cells4 := by
    change j4 ∈ {fun _ : Fin 4 => (0 : Fin 1)}
    apply Finset.mem_singleton.mpr
    funext i
    exact Fin.eq_zero (j4 i)
  change (if j4 ∈ table.cells4 then table.cap4 j4 else table.old4 j4) = (5 / 8 : ℚ)
  rw [if_pos hm]
  rfl

theorem distinct_history_levels :
    table.fifthParentGateBounds cell 4 = (1 / 2 : ℝ) ∧
      table.fifthParentGateBounds cell 5 = (3 / 5 : ℝ) ∧
      table.old5 cell = (5 / 8 : ℚ) ∧ table.cap5 cell = (2 / 3 : ℚ) := by
  refine ⟨?_, ?_, table_old5_eq cell, rfl⟩
  · change ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ)
    norm_num
  · change (table.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) cell) : ℝ) =
      (3 / 5 : ℝ)
    rw [table_cell3_eq]
    norm_num

theorem witness_in_owned_cell :
    witness ∈ logPrimeMeshCell (table.a : ℝ) (table.b : ℝ) table.m cell := by
  norm_num [mem_logPrimeMeshCell, logPrimeMeshLo, logPrimeMeshHi,
    logPrimeMeshPoint, logPrimeMeshStep, table, cell, witness, Fin.forall_fin_succ]

theorem historical_parent_accepts :
    witness ∈ primeAffineGateRegion ordinaryUpperFiveGateForms
      (table.fifthParentGateBounds cell) := by
  rw [table.mem_fifthParentGateRegion]
  refine ⟨?_, ?_, ?_⟩
  · apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    fin_cases i
    · change (3 / 25 : ℝ) < 3 / 20
      norm_num
    · change (1 / 10 : ℝ) < 3 / 25
      norm_num
    · change (9 / 100 : ℝ) < 1 / 10
      norm_num
    · change (13 / 200 : ℝ) < 9 / 100
      norm_num
  · change (3 : ℝ) * (3 / 20) < ((1 / 2 : ℚ) : ℝ)
    norm_num
  · rw [table_cell3_eq]
    change (3 / 20 : ℝ) + 3 / 25 + 3 * (1 / 10) < ((3 / 5 : ℚ) : ℝ)
    norm_num

theorem ordinary_old_parent_rejects :
    witness ∉ primeAffineGateRegion ordinaryUpperFiveGateForms
      (ordinaryUpperFiveGateBounds (table.old : ℝ)) := by
  intro h
  have hthird := ((mem_ordinaryUpperFiveGateRegion (table.old : ℝ) witness).mp h).2.2
  change (3 / 20 : ℝ) + 3 / 25 + 3 * (1 / 10) < ((1 / 2 : ℚ) : ℝ) at hthird
  norm_num at hthird

theorem old_cube_rejects_new_cube_accepts :
    ¬primeTupleOwnCubeForm witness < (table.old5 cell : ℝ) ∧
      primeTupleOwnCubeForm witness < (table.cap5 cell : ℝ) := by
  have hlast : witness (Fin.last 4) = (13 / 200 : ℝ) := rfl
  have hform : primeTupleOwnCubeForm witness = (131 / 200 : ℝ) := by
    unfold primeTupleOwnCubeForm
    rw [hlast]
    norm_num [Fin.sum_univ_succ, witness]
  rw [hform, table_old5_eq]
  change ¬(131 / 200 : ℝ) < ((5 / 8 : ℚ) : ℝ) ∧
    (131 / 200 : ℝ) < ((2 / 3 : ℚ) : ℝ)
  norm_num

end

end P1HistoricalCellProbe
