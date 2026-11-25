import ImbalancedChen.P2OriginalSaving19Geometry00BoundedAccess
import ImbalancedChen.P2OriginalSaving19Moment00Shape
import ImbalancedChen.P2OriginalSaving19RowNumericsPure
import ImbalancedChen.P2Winner9FastDetPure
import Mathlib.Tactic.FinCases

/-! Actual cell00 row arithmetic using the unchanged ten-clause pure
representation. The original decoded row and vertex IDs are bound by closed
equalities to their bounded accesses. No Q80/new Q96 or integral conclusion. -/
namespace ImbalancedChen.P2OriginalSaving19Cell00Row006
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19Archive
open P2OriginalSaving19Geometry00Decoding
open P2OriginalSaving19Geometry00BoundedAccess
open P2OriginalSaving19Moment00Decoding
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

noncomputable def row : GeometryRow := geometryRowsTyped006

noncomputable def vertices : Fin 9 → QPoint :=
  ![(fun j => geometryVerticesTyped027[j.val]!),
    (fun j => geometryVerticesTyped025[j.val]!),
    (fun j => geometryVerticesTyped023[j.val]!),
    (fun j => geometryVerticesTyped009[j.val]!),
    (fun j => geometryVerticesTyped007[j.val]!),
    (fun j => geometryVerticesTyped005[j.val]!),
    (fun j => geometryVerticesTyped003[j.val]!),
    (fun j => geometryVerticesTyped001[j.val]!),
    (fun j => geometryVerticesTyped000[j.val]!)]

noncomputable def momentRow : MomentRecord :=
  momentConcrete00.rows[(6 : Fin 56).val]'(P2OriginalSaving19Moment00Shape.row_bound 6)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 boundedRow_eq_before"
  err.flush

theorem boundedRow_eq :
    boundedRow (6 : Fin 56) = row := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 boundedRowVertex_eq_before"
  err.flush

theorem boundedRowVertex_eq :
    boundedRowVertex (6 : Fin 56) = vertices := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 raw_row_eq_before"
  err.flush

theorem raw_row_eq :
    concreteGeometry00.rows[6]! = row := (row_lookup_no_fallback (6 : Fin 56)).trans boundedRow_eq

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 raw_moment_row_eq_before"
  err.flush

theorem raw_moment_row_eq :
    momentConcrete00.rows[6]! = momentRow := P2OriginalSaving19Moment00Shape.row_lookup_no_fallback (6 : Fin 56)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 moment_row_eq_before"
  err.flush

theorem moment_row_eq :
    momentRow = momentTypedRecord006 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 physical_volume_positive_before"
  err.flush

theorem physical_volume_positive :
    0 < row.physicalVolume := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 volume_eq_before"
  err.flush

theorem volume_eq :
    row.physicalVolume = |(edgeOf vertices).det| / (Nat.factorial 8 : ℚ) := by
  rw [← P2Winner9FastDetPure.fastDet_eq (edgeOf vertices)]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 det_ne_before"
  err.flush

theorem det_ne :
    (edgeOf vertices).det ≠ 0 := by
  intro hzero
  have h := volume_eq
  rw [hzero, abs_zero, zero_div] at h
  exact (ne_of_gt physical_volume_positive) h

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 all_physical_before"
  err.flush

theorem all_physical :
    ∀ i : Fin 9, PhysicalQ (vertices i) := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 gap_sum_positive_before"
  err.flush

theorem gap_sum_positive :
    0 < gapSumOf vertices := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 mean_gap_eq_before"
  err.flush

theorem mean_gap_eq :
    row.meanGap = gapSumOf vertices / 9 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 weighted_means_eq_before"
  err.flush

theorem weighted_means_eq :
    ∀ j : Fin 10, meansOf row j = computedMeanOf vertices j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 factor_le_maxima_before"
  err.flush

theorem factor_le_maxima :
    ∀ i : Fin 9, ∀ j : Fin 10, factorsQ (vertices i) j ≤ topsOf row j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 factor_maxima_attained_before"
  err.flush

theorem factor_maxima_attained :
    ∀ j : Fin 10, ∃ i : Fin 9, factorsQ (vertices i) j = topsOf row j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 jensen_eq_before"
  err.flush

theorem jensen_eq :
    row.jensenBound = oldEvaluator (massOf row) (meansOf row) := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 old_floor_eq_before"
  err.flush

theorem old_floor_eq :
    row.jensenFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) := by
  unfold oldFloorQ96
  rw [← jensen_eq]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 row_data_checks_before"
  err.flush

theorem row_data_checks :
    RowDataChecksFor vertices row := by
  exact ⟨det_ne, all_physical, gap_sum_positive, volume_eq, mean_gap_eq,
    weighted_means_eq, factor_le_maxima, factor_maxima_attained, jensen_eq, old_floor_eq⟩

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 bounded_row_data_checks_before"
  err.flush

theorem bounded_row_data_checks :
    RowDataChecksFor (boundedRowVertex (6 : Fin 56)) (boundedRow (6 : Fin 56)) := by
  rw [boundedRowVertex_eq, boundedRow_eq]
  exact row_data_checks

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 moment_old_matches_geometry_before"
  err.flush

theorem moment_old_matches_geometry :
    momentRow.oldFloorQ96 = row.jensenFloorQ96 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 moment_old_eq_evaluator_before"
  err.flush

theorem moment_old_eq_evaluator :
    momentRow.oldFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) := moment_old_matches_geometry.trans old_floor_eq

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 actual_moment_old_eq_bounded_evaluator_before"
  err.flush

theorem actual_moment_old_eq_bounded_evaluator :
    (momentConcrete00.rows[6]!).oldFloorQ96 =
      oldFloorQ96 (massOf (boundedRow (6 : Fin 56))) (meansOf (boundedRow (6 : Fin 56))) := by
  rw [raw_moment_row_eq, boundedRow_eq]
  exact moment_old_eq_evaluator

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_ROW006 complete"
  err.flush

#print axioms boundedRow_eq
#print axioms boundedRowVertex_eq
#print axioms raw_row_eq
#print axioms raw_moment_row_eq
#print axioms moment_row_eq
#print axioms physical_volume_positive
#print axioms volume_eq
#print axioms det_ne
#print axioms all_physical
#print axioms gap_sum_positive
#print axioms mean_gap_eq
#print axioms weighted_means_eq
#print axioms factor_le_maxima
#print axioms factor_maxima_attained
#print axioms jensen_eq
#print axioms old_floor_eq
#print axioms row_data_checks
#print axioms bounded_row_data_checks
#print axioms moment_old_matches_geometry
#print axioms moment_old_eq_evaluator
#print axioms actual_moment_old_eq_bounded_evaluator

end ImbalancedChen.P2OriginalSaving19Cell00Row006
