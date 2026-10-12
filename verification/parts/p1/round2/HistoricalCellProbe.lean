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

theorem distinct_history_levels :
    table.fifthParentGateBounds cell 4 = (1 / 2 : ℝ) ∧
      table.fifthParentGateBounds cell 5 = (3 / 5 : ℝ) ∧
      table.old5 cell = (5 / 8 : ℚ) ∧ table.cap5 cell = (2 / 3 : ℚ) := by
  norm_num [HistoricalPrefixCapData.fifthParentGateBounds,
    HistoricalPrefixCapData.old5, HistoricalPrefixCapData.cell4,
    HistoricalPrefixCapData.cell3, historicalPrefixProject, table, cell]

theorem witness_in_owned_cell :
    witness ∈ logPrimeMeshCell (table.a : ℝ) (table.b : ℝ) table.m cell := by
  norm_num [mem_logPrimeMeshCell, logPrimeMeshLo, logPrimeMeshHi,
    logPrimeMeshPoint, logPrimeMeshStep, table, cell, witness, Fin.forall_fin_succ]

theorem historical_parent_accepts :
    witness ∈ primeAffineGateRegion ordinaryUpperFiveGateForms
      (table.fifthParentGateBounds cell) := by
  norm_num [primeAffineGateRegion, ordinaryUpperFiveGateForms,
    HistoricalPrefixCapData.fifthParentGateBounds,
    HistoricalPrefixCapData.cell3, historicalPrefixProject,
    table, cell, witness, Fin.forall_fin_succ]

theorem ordinary_old_parent_rejects :
    witness ∉ primeAffineGateRegion ordinaryUpperFiveGateForms
      (ordinaryUpperFiveGateBounds (table.old : ℝ)) := by
  norm_num [primeAffineGateRegion, ordinaryUpperFiveGateForms,
    ordinaryUpperFiveGateBounds, table, witness, Fin.forall_fin_succ]

theorem old_cube_rejects_new_cube_accepts :
    ¬primeTupleOwnCubeForm witness < (table.old5 cell : ℝ) ∧
      primeTupleOwnCubeForm witness < (table.cap5 cell : ℝ) := by
  norm_num [primeTupleOwnCubeForm, Fin.sum_univ_succ,
    HistoricalPrefixCapData.old5, HistoricalPrefixCapData.cell4,
    historicalPrefixProject, table, cell, witness]

end

end P1HistoricalCellProbe
