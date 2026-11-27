import ImbalancedChen.P2OriginalSaving19Geometry01BoundedAccess
import ImbalancedChen.P2OriginalSaving19RowNumericsPure
import Mathlib.Tactic.FinCases
import ImbalancedChen.P2Winner9FastDetPure
import ImbalancedChen.P2OriginalSaving19Moment01Shape
import ImbalancedChen.P2OriginalSaving19PrefixMoments
import Mathlib.Algebra.BigOperators.Field

/-! SOURCE CANDIDATE: original Cell01 row 2 only.
Twenty-one accepted row000 source bodies are merged into one new owner.
Original ordinal, vertex order and decoded row/record identities are retained.
All host-produced literals remain closed Lean proof obligations. This owner
has not been compiled, independently replayed or audited. No integral or
OriginalFloorBridge claim is included. The shared bounded-access owner is
imported unchanged. -/

-- BEGIN DONOR Input
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! The actual original row 2 and its original nine ordered vertices. The small
selectors refer to the already decoded values, with closed equalities to
the original bounded accesses. No numeric field is recomputed or assumed. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2OriginalSaving19RowNumericsPure
open P2OriginalSaving19Geometry01Decoding
open P2OriginalSaving19Geometry01DirectDecoding
open P2OriginalSaving19Geometry01BoundedAccess

noncomputable def row : GeometryRow := geometryRowsTyped002

noncomputable def vertices : Fin 9 → QPoint :=
  ![(fun j => geometryVerticesTyped039[j.val]!),
    (fun j => geometryVerticesTyped035[j.val]!),
    (fun j => geometryVerticesTyped029[j.val]!),
    (fun j => geometryVerticesTyped028[j.val]!),
    (fun j => geometryVerticesTyped025[j.val]!),
    (fun j => geometryVerticesTyped013[j.val]!),
    (fun j => geometryVerticesTyped012[j.val]!),
    (fun j => geometryVerticesTyped002[j.val]!),
    (fun j => geometryVerticesTyped000[j.val]!)]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_INPUT before_row_binding"
  err.flush

theorem boundedRow_eq : boundedRow (2 : Fin 144) = row := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_INPUT before_vertex_binding"
  err.flush

theorem boundedRowVertex_eq : boundedRowVertex (2 : Fin 144) = vertices := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem raw_row_eq : concreteGeometry01.rows[2]! = row :=
  (row_lookup_no_fallback (2 : Fin 144)).trans boundedRow_eq

theorem raw_vertices_eq (i : Fin 9) (j : Fin 8) :
    ((concreteGeometry01.vertices[
      (concreteGeometry01.rows[2]!).vertexIds[i.val]!]!)[j.val]!) = vertices i j :=
  (raw_vertex_no_fallback (2 : Fin 144) i j).trans
    (congrFun (congrFun boundedRowVertex_eq i) j)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_INPUT bindings_complete"
  err.flush

#print axioms boundedRow_eq
#print axioms boundedRowVertex_eq
#print axioms raw_row_eq
#print axioms raw_vertices_eq

/-- The original factor and mean lookups retain the certified bounds. -/
theorem factor_maximum_no_fallback (j : Fin 10) :
    row.factorMaxima[j.val]! =
      (boundedRow (2 : Fin 144)).factorMaxima[j.val]'(factor_maximum_bound (2 : Fin 144) j) := by
  rw [← raw_row_eq]
  exact factor_maximum_lookup_no_fallback (2 : Fin 144) j

theorem weighted_mean_no_fallback (j : Fin 10) :
    row.gapWeightedMeans[j.val]! =
      (boundedRow (2 : Fin 144)).gapWeightedMeans[j.val]'(weighted_mean_bound (2 : Fin 144) j) := by
  rw [← raw_row_eq]
  exact weighted_mean_lookup_no_fallback (2 : Fin 144) j

#print axioms factor_maximum_no_fallback
#print axioms weighted_mean_no_fallback

end ImbalancedChen.P2OriginalSaving19Cell01Row002
-- END DONOR Input

-- BEGIN DONOR Determinant
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row2.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Determinant_physical_volume_positive_before"
  err.flush

theorem physical_volume_positive :
    0 < row.physicalVolume := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Determinant_volume_eq_before"
  err.flush

theorem volume_eq :
    row.physicalVolume = |(edgeOf vertices).det| / (Nat.factorial 8 : ℚ) := by
  rw [← P2Winner9FastDetPure.fastDet_eq (edgeOf vertices)]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Determinant_det_ne_before"
  err.flush

theorem det_ne :
    (edgeOf vertices).det ≠ 0 := by
  intro hzero
  have h := volume_eq
  rw [hzero, abs_zero, zero_div] at h
  exact (ne_of_gt physical_volume_positive) h

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Determinant_complete"
  err.flush

#print axioms physical_volume_positive
#print axioms volume_eq
#print axioms det_ne

end ImbalancedChen.P2OriginalSaving19Cell01Row002
-- END DONOR Determinant

-- BEGIN DONOR Physical
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row2.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Physical_all_physical_before"
  err.flush

theorem all_physical :
    ∀ i : Fin 9, PhysicalQ (vertices i) := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Physical_complete"
  err.flush

#print axioms all_physical

end ImbalancedChen.P2OriginalSaving19Cell01Row002
-- END DONOR Physical

-- BEGIN DONOR Gap
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row2.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Gap_gap_sum_positive_before"
  err.flush

theorem gap_sum_positive :
    0 < gapSumOf vertices := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Gap_mean_gap_eq_before"
  err.flush

theorem mean_gap_eq :
    row.meanGap = gapSumOf vertices / 9 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Gap_complete"
  err.flush

#print axioms gap_sum_positive
#print axioms mean_gap_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row002
-- END DONOR Gap

-- BEGIN DONOR Means
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row2.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Means_weighted_means_eq_before"
  err.flush

theorem weighted_means_eq :
    ∀ j : Fin 10, meansOf row j = computedMeanOf vertices j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Means_complete"
  err.flush

#print axioms weighted_means_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row002
-- END DONOR Means

-- BEGIN DONOR Maxima
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row2.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Maxima_factor_le_maxima_before"
  err.flush

theorem factor_le_maxima :
    ∀ i : Fin 9, ∀ j : Fin 10, factorsQ (vertices i) j ≤ topsOf row j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Maxima_factor_maxima_attained_before"
  err.flush

theorem factor_maxima_attained :
    ∀ j : Fin 10, ∃ i : Fin 9, factorsQ (vertices i) j = topsOf row j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Maxima_complete"
  err.flush

#print axioms factor_le_maxima
#print axioms factor_maxima_attained

end ImbalancedChen.P2OriginalSaving19Cell01Row002
-- END DONOR Maxima

-- BEGIN DONOR Jensen
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row2.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Jensen_jensen_eq_before"
  err.flush

theorem jensen_eq :
    row.jensenBound = oldEvaluator (massOf row) (meansOf row) := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Jensen_old_floor_eq_before"
  err.flush

theorem old_floor_eq :
    row.jensenFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) := by
  unfold oldFloorQ96
  rw [← jensen_eq]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Jensen_complete"
  err.flush

#print axioms jensen_eq
#print axioms old_floor_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row002
-- END DONOR Jensen

-- BEGIN DONOR Arithmetic
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row2.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Arithmetic_row_data_checks_before"
  err.flush

theorem row_data_checks :
    RowDataChecksFor vertices row := by
  exact ⟨det_ne, all_physical, gap_sum_positive, volume_eq, mean_gap_eq,
    weighted_means_eq, factor_le_maxima, factor_maxima_attained,
    jensen_eq, old_floor_eq⟩

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Arithmetic_bounded_row_data_checks_before"
  err.flush

theorem bounded_row_data_checks :
    RowDataChecksFor
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRowVertex (2 : Fin 144))
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (2 : Fin 144)) := by
  rw [boundedRowVertex_eq, boundedRow_eq]
  exact row_data_checks

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002 Arithmetic_complete"
  err.flush

#print axioms row_data_checks
#print axioms bounded_row_data_checks

end ImbalancedChen.P2OriginalSaving19Cell01Row002
-- END DONOR Arithmetic

-- BEGIN DONOR OldFloor
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! The actual moment row2 old floor is the actual geometry row2 Jensen
floor and the same original exact Q96 arithmetic. The ten Q80 fields and
the new Q96 field are not certified by these old-floor equalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open P2OriginalSaving19Archive
open P2OriginalSaving19Moment01Decoding
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

noncomputable def momentRow : MomentRecord :=
  momentConcrete01.rows[(2 : Fin 144).val]'(P2OriginalSaving19Moment01Shape.row_bound 2)

theorem raw_moment_row_eq : momentConcrete01.rows[2]! = momentRow :=
  P2OriginalSaving19Moment01Shape.row_lookup_no_fallback (2 : Fin 144)

theorem moment_row_eq : momentRow = momentTypedRecord002 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_OLD_FLOOR before_original_moment_geometry_binding"
  err.flush

theorem moment_old_matches_geometry : momentRow.oldFloorQ96 = row.jensenFloorQ96 := by
  decide +kernel

theorem moment_old_eq_evaluator :
    momentRow.oldFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) :=
  moment_old_matches_geometry.trans old_floor_eq

theorem actual_moment_old_eq_bounded_evaluator :
    (momentConcrete01.rows[2]!).oldFloorQ96 =
      oldFloorQ96
        (massOf (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (2 : Fin 144)))
        (meansOf (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (2 : Fin 144))) := by
  rw [raw_moment_row_eq, boundedRow_eq]
  exact moment_old_eq_evaluator

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_OLD_FLOOR complete"
  err.flush

#print axioms raw_moment_row_eq
#print axioms moment_row_eq
#print axioms moment_old_matches_geometry
#print axioms moment_old_eq_evaluator
#print axioms actual_moment_old_eq_bounded_evaluator

/-- The saved ten Q80 fields are accessed at their true bounded indices. -/
theorem moment_floor_bound (j : Fin 10) : j.val < momentRow.factorFloorsQ80.size := by
  have hs : momentRow.factorFloorsQ80.size = 10 :=
    (P2OriginalSaving19Moment01Shape.row_ids_and_floor_sizes_bounded (2 : Fin 144)).2
  rw [hs]
  exact j.isLt

theorem moment_floor_lookup_no_fallback (j : Fin 10) :
    momentRow.factorFloorsQ80[j.val]! =
      momentRow.factorFloorsQ80[j.val]'(moment_floor_bound j) :=
  getElem!_pos momentRow.factorFloorsQ80 j.val (moment_floor_bound j)

#print axioms moment_floor_bound
#print axioms moment_floor_lookup_no_fallback

end ImbalancedChen.P2OriginalSaving19Cell01Row002
-- END DONOR OldFloor

-- BEGIN DONOR MomentEncoding
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact nonnegative integer encodings of the actual nine ordered vertices.
The existing prefix evaluator is used unchanged. Host-generated literals
are connected to the decoded row by closed Lean equalities below. No
saved field, moment value or final floor is an assumption. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row002
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

def gapScale : Nat := 98000000

def gapNats : Fin 9 → Nat := ![0, 0, 0, 0, 0, 0, 0, 515533, 0]

def deviationDenominators : Fin 10 → Nat := ![34085021320, 34085021320, 11693988600, 44833808320, 11693988600, 31190382580, 13367095140, 11024736576, 38586578016, 38585919456]

def deviationNats : Fin 10 → Fin 9 → Nat :=
  ![![4868630200, 17361334648, 7796484325, 7796484325, 5824600840, 4868536120, 4868630200, 4041778720, 0],
    ![4868630200, 17361334648, 7796484325, 7796484325, 5824600840, 4868536120, 4868630200, 2309587840, 0],
    ![0, 669252024, 1254841665, 1254841665, 1434103800, 1673119980, 1673130060, 2162435460, 2368648660],
    ![0, 6246352224, 4879976395, 4879976395, 6373827520, 7807924600, 7807940280, 7479997840, 12676570480],
    ![3346260120, 669252024, 1254841665, 1254841665, 1434103800, 6720, 0, 2699589120, 2782074400],
    ![16580540620, 11895776452, 7796648965, 7796648965, 9410008180, 4868700760, 4868630200, 6640065040, 0],
    ![5019366660, 2342358564, 0, 2927948205, 3107210340, 5019339780, 5019366660, 3298388340, 3628329460],
    ![2677008096, 0, 3513537846, 585589641, 764851776, 2676981216, 2677008096, 956029776, 1285970896],
    ![9369528336, 0, 12298041021, 12298041021, 10326157536, 9370092816, 9369528336, 3346104216, 4500898136],
    ![9369528336, 0, 12297382461, 12297382461, 10325498976, 9369434256, 9369528336, 6810485976, 4500898136]]

def prefixMoment (j : Fin 10) (k : Nat) : ℚ :=
  normalizedMoment gapNats (deviationNats j) (deviationDenominators j) k

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT gap_encoding_before"
  err.flush

theorem gapScale_ne : gapScale ≠ 0 := by decide +kernel

theorem gap_encoding : ∀ i : Fin 9,
    gapQ (vertices i) = (gapNats i : ℚ) / (gapScale : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT deviation_encoding_before"
  err.flush

theorem deviationDenominators_ne : ∀ j : Fin 10, deviationDenominators j ≠ 0 := by
  decide +kernel

theorem deviation_encoding : ∀ (j : Fin 10) (i : Fin 9),
    1 - factorsQ (vertices i) j / topsOf row j =
      (deviationNats j i : ℚ) / (deviationDenominators j : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT encoding_complete"
  err.flush

#print axioms gapScale_ne
#print axioms gap_encoding
#print axioms deviationDenominators_ne
#print axioms deviation_encoding

end ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor
-- END DONOR MomentEncoding

-- BEGIN DONOR MomentFactor00
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row002
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor00_moment1_before"
  err.flush

theorem factor00_moment1 : prefixMoment (0 : Fin 10) 1 = (30734129049 : ℚ) / 170425106600 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor00_moment2_before"
  err.flush

theorem factor00_moment2 : prefixMoment (0 : Fin 10) 2 = (2169520359705398194779 : ℚ) / 63898377311166999832000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor00_moment3_before"
  err.flush

theorem factor00_moment3 : prefixMoment (0 : Fin 10) 3 = (1323319591109557893085276641393 : ℚ) / 197997959360411951214014219840000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor00_moment4_before"
  err.flush

theorem factor00_moment4 : prefixMoment (0 : Fin 10) 4 = (1329642611672516376528036486579811392568341 : ℚ) / 965073347254607293719083862942228079398400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor00_moment5_before"
  err.flush

theorem factor00_moment5 : prefixMoment (0 : Fin 10) 5 = (13715136166128246344116684381593595420978429650473859 : ℚ) / 46052363863151874304499465782955322820435963483443200000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor00_moment6_before"
  err.flush

theorem factor00_moment6 : prefixMoment (0 : Fin 10) 6 = (530127369303175017202534076057776819934383096513608865813542639 : ℚ) / 7848479020559645990334122315703213354710211735139514695045120000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor00_first_moment_before"
  err.flush

theorem factor00_first_moment :
    prefixMoment (0 : Fin 10) 1 = 1 - meansOf row (0 : Fin 10) / topsOf row (0 : Fin 10) := by
  rw [factor00_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor00_gap_before"
  err.flush

theorem factor00_gap_value :
    gapEvaluator (prefixMoment (0 : Fin 10)) = (26862769110484907950291479503988996096128602128258809191623238435099 : ℚ) / 24526496939248893719794132236572541733469411672310983422016000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor00_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor00_saved_Q80_before"
  err.flush

theorem factor00_saved_Q80 :
    momentRow.factorFloorsQ80[0]! = factorFloorQ80 (prefixMoment (0 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor00_gap_value]
  decide +kernel

theorem factor00_Q80_lower :
    ((momentRow.factorFloorsQ80[0]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (0 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor00_gap_value]
  decide +kernel

theorem factor00_Q80_upper :
    gapEvaluator (prefixMoment (0 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[0]! : ℤ) : ℚ) + 1 := by
  rw [factor00_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor00_complete"
  err.flush

#print axioms factor00_moment1
#print axioms factor00_moment2
#print axioms factor00_moment3
#print axioms factor00_moment4
#print axioms factor00_moment5
#print axioms factor00_moment6
#print axioms factor00_first_moment
#print axioms factor00_gap_value
#print axioms factor00_saved_Q80
#print axioms factor00_Q80_lower
#print axioms factor00_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor
-- END DONOR MomentFactor00

-- BEGIN DONOR MomentFactor01
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row002
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor01_moment1_before"
  err.flush

theorem factor01_moment1 : prefixMoment (1 : Fin 10) 1 = (29001938169 : ℚ) / 170425106600 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor01_moment2_before"
  err.flush

theorem factor01_moment2 : prefixMoment (1 : Fin 10) 2 = (1951570038790456078299 : ℚ) / 63898377311166999832000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor01_moment3_before"
  err.flush

theorem factor01_moment3 : prefixMoment (1 : Fin 10) 3 = (12599501080369629141277081843563 : ℚ) / 2177977552964531463354156418240000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor01_moment4_before"
  err.flush

theorem factor01_moment4 : prefixMoment (1 : Fin 10) 4 = (1116797304563650444587696519479692394246421 : ℚ) / 965073347254607293719083862942228079398400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor01_moment5_before"
  err.flush

theorem factor01_moment5 : prefixMoment (1 : Fin 10) 5 = (11261529764244383357924037960667062952223013119431779 : ℚ) / 46052363863151874304499465782955322820435963483443200000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor01_moment6_before"
  err.flush

theorem factor01_moment6 : prefixMoment (1 : Fin 10) 6 = (428194949176982863315316761648464757760160845566945808699566959 : ℚ) / 7848479020559645990334122315703213354710211735139514695045120000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor01_first_moment_before"
  err.flush

theorem factor01_first_moment :
    prefixMoment (1 : Fin 10) 1 = 1 - meansOf row (1 : Fin 10) / topsOf row (1 : Fin 10) := by
  rw [factor01_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor01_gap_before"
  err.flush

theorem factor01_gap_value :
    gapEvaluator (prefixMoment (1 : Fin 10)) = (2635365856784790833327356740063853395197165847239255672986746126929 : ℚ) / 2229681539931717610890375657870231066679037424755543947456000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor01_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor01_saved_Q80_before"
  err.flush

theorem factor01_saved_Q80 :
    momentRow.factorFloorsQ80[1]! = factorFloorQ80 (prefixMoment (1 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor01_gap_value]
  decide +kernel

theorem factor01_Q80_lower :
    ((momentRow.factorFloorsQ80[1]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (1 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor01_gap_value]
  decide +kernel

theorem factor01_Q80_upper :
    gapEvaluator (prefixMoment (1 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[1]! : ℤ) : ℚ) + 1 := by
  rw [factor01_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor01_complete"
  err.flush

#print axioms factor01_moment1
#print axioms factor01_moment2
#print axioms factor01_moment3
#print axioms factor01_moment4
#print axioms factor01_moment5
#print axioms factor01_moment6
#print axioms factor01_first_moment
#print axioms factor01_gap_value
#print axioms factor01_saved_Q80
#print axioms factor01_Q80_lower
#print axioms factor01_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor
-- END DONOR MomentFactor01

-- BEGIN DONOR MomentFactor02
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row002
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor02_moment1_before"
  err.flush

theorem factor02_moment1 : prefixMoment (2 : Fin 10) 1 = (7326404387 : ℚ) / 58469943000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor02_moment2_before"
  err.flush

theorem factor02_moment2 : prefixMoment (2 : Fin 10) 2 = (120460028766827643451 : ℚ) / 7521215315731147800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor02_moment3_before"
  err.flush

theorem factor02_moment3 : prefixMoment (2 : Fin 10) 3 = (45818461143618376025366399239 : ℚ) / 21988251540076360759528770000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor02_moment4_before"
  err.flush

theorem factor02_moment4 : prefixMoment (2 : Fin 10) 4 = (3683475001040980730624555551633947588901 : ℚ) / 13370778867866441104273672443105144000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor02_moment5_before"
  err.flush

theorem factor02_moment5 : prefixMoment (2 : Fin 10) 5 = (1155733835795169796972379880937105301131443240491 : ℚ) / 31271547130790213719189547365961140507471680000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor02_moment6_before"
  err.flush

theorem factor02_moment6 : prefixMoment (2 : Fin 10) 6 = (9188782131187342643390473324413124131812006646191240523193 : ℚ) / 1828445578259117341118830840683548025686860203714240000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor02_first_moment_before"
  err.flush

theorem factor02_first_moment :
    prefixMoment (2 : Fin 10) 1 = 1 - meansOf row (2 : Fin 10) / topsOf row (2 : Fin 10) := by
  rw [factor02_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor02_gap_before"
  err.flush

theorem factor02_gap_value :
    gapEvaluator (prefixMoment (2 : Fin 10)) = (1172383101797457702498136621560557165320457828040313569257256073 : ℚ) / 5713892432059741690996346377136087580271438136607000000000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor02_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor02_saved_Q80_before"
  err.flush

theorem factor02_saved_Q80 :
    momentRow.factorFloorsQ80[2]! = factorFloorQ80 (prefixMoment (2 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor02_gap_value]
  decide +kernel

theorem factor02_Q80_lower :
    ((momentRow.factorFloorsQ80[2]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (2 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor02_gap_value]
  decide +kernel

theorem factor02_Q80_upper :
    gapEvaluator (prefixMoment (2 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[2]! : ℤ) : ℚ) + 1 := by
  rw [factor02_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor02_complete"
  err.flush

#print axioms factor02_moment1
#print axioms factor02_moment2
#print axioms factor02_moment3
#print axioms factor02_moment4
#print axioms factor02_moment5
#print axioms factor02_moment6
#print axioms factor02_first_moment
#print axioms factor02_gap_value
#print axioms factor02_saved_Q80
#print axioms factor02_Q80_lower
#print axioms factor02_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor
-- END DONOR MomentFactor02

-- BEGIN DONOR MomentFactor03
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row002
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor03_moment1_before"
  err.flush

theorem factor03_moment1 : prefixMoment (3 : Fin 10) 1 = (32816281787 : ℚ) / 224169041600 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor03_moment2_before"
  err.flush

theorem factor03_moment2 : prefixMoment (3 : Fin 10) 2 = (2414714063185096771051 : ℚ) / 110553870266097567232000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor03_moment3_before"
  err.flush

theorem factor03_moment3 : prefixMoment (3 : Fin 10) 3 = (16440980523773596011166952476731 : ℚ) / 4956551028544365723697800970240000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor03_moment4_before"
  err.flush

theorem factor03_moment4 : prefixMoment (3 : Fin 10) 4 = (1479856247639837957159124683181306482962101 : ℚ) / 2888873763646740239139188773968252397158400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor03_moment5_before"
  err.flush

theorem factor03_moment5 : prefixMoment (3 : Fin 10) 5 = (14579000665247975054097385773169481447092687227071937 : ℚ) / 181326897612020910504156291809343807235412305589043200000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor03_moment6_before"
  err.flush

theorem factor03_moment6 : prefixMoment (3 : Fin 10) 6 = (521138369361646689661275443456309551820277806436700423668485151 : ℚ) / 40647876853988056146876088751510531192857522124742137604997120000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor03_first_moment_before"
  err.flush

theorem factor03_first_moment :
    prefixMoment (3 : Fin 10) 1 = 1 - meansOf row (3 : Fin 10) / topsOf row (3 : Fin 10) := by
  rw [factor03_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor03_gap_before"
  err.flush

theorem factor03_gap_value :
    gapEvaluator (prefixMoment (3 : Fin 10)) = (35843460616460509971078940356574242870393435000394252295389679008671 : ℚ) / 127024615168712675458987777348470409977679756639819180015616000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor03_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor03_saved_Q80_before"
  err.flush

theorem factor03_saved_Q80 :
    momentRow.factorFloorsQ80[3]! = factorFloorQ80 (prefixMoment (3 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor03_gap_value]
  decide +kernel

theorem factor03_Q80_lower :
    ((momentRow.factorFloorsQ80[3]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (3 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor03_gap_value]
  decide +kernel

theorem factor03_Q80_upper :
    gapEvaluator (prefixMoment (3 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[3]! : ℤ) : ℚ) + 1 := by
  rw [factor03_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor03_complete"
  err.flush

#print axioms factor03_moment1
#print axioms factor03_moment2
#print axioms factor03_moment3
#print axioms factor03_moment4
#print axioms factor03_moment5
#print axioms factor03_moment6
#print axioms factor03_first_moment
#print axioms factor03_gap_value
#print axioms factor03_saved_Q80
#print axioms factor03_Q80_lower
#print axioms factor03_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor
-- END DONOR MomentFactor03

-- BEGIN DONOR MomentFactor04
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row002
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor04_moment1_before"
  err.flush

theorem factor04_moment1 : prefixMoment (4 : Fin 10) 1 = (8070279317 : ℚ) / 58469943000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor04_moment2_before"
  err.flush

theorem factor04_moment2 : prefixMoment (4 : Fin 10) 2 = (149842198899181054291 : ℚ) / 7521215315731147800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor04_moment3_before"
  err.flush

theorem factor04_moment3 : prefixMoment (4 : Fin 10) 3 = (263021833852102652510379951871 : ℚ) / 87953006160305443038115080000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor04_moment4_before"
  err.flush

theorem factor04_moment4 : prefixMoment (4 : Fin 10) 4 = (6213669539575113712687304256608744680741 : ℚ) / 13370778867866441104273672443105144000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor04_moment5_before"
  err.flush

theorem factor04_moment5 : prefixMoment (4 : Fin 10) 5 = (16305720715671628836686146963422250708307368881767 : ℚ) / 218900829915531496034326831561727983552301760000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor04_moment6_before"
  err.flush

theorem factor04_moment6 : prefixMoment (4 : Fin 10) 6 = (157137197433427866672101120071737000121365285185765636627191 : ℚ) / 12799119047813821387831815884784836179808021425999680000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor04_first_moment_before"
  err.flush

theorem factor04_first_moment :
    prefixMoment (4 : Fin 10) 1 = 1 - meansOf row (4 : Fin 10) / topsOf row (4 : Fin 10) := by
  rw [factor04_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor04_gap_before"
  err.flush

theorem factor04_gap_value :
    gapEvaluator (prefixMoment (4 : Fin 10)) = (870298906159635019635099807364546822229751836711157963362384713 : ℚ) / 1481379519422895993962015727405652335625928405787000000000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor04_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor04_saved_Q80_before"
  err.flush

theorem factor04_saved_Q80 :
    momentRow.factorFloorsQ80[4]! = factorFloorQ80 (prefixMoment (4 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor04_gap_value]
  decide +kernel

theorem factor04_Q80_lower :
    ((momentRow.factorFloorsQ80[4]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (4 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor04_gap_value]
  decide +kernel

theorem factor04_Q80_upper :
    gapEvaluator (prefixMoment (4 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[4]! : ℤ) : ℚ) + 1 := by
  rw [factor04_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor04_complete"
  err.flush

#print axioms factor04_moment1
#print axioms factor04_moment2
#print axioms factor04_moment3
#print axioms factor04_moment4
#print axioms factor04_moment5
#print axioms factor04_moment6
#print axioms factor04_first_moment
#print axioms factor04_gap_value
#print axioms factor04_saved_Q80
#print axioms factor04_Q80_lower
#print axioms factor04_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor
-- END DONOR MomentFactor04

-- BEGIN DONOR MomentFactor05
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row002
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor05_moment1_before"
  err.flush

theorem factor05_moment1 : prefixMoment (5 : Fin 10) 1 = (38248542111 : ℚ) / 155951912900 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor05_moment2_before"
  err.flush

theorem factor05_moment2 : prefixMoment (5 : Fin 10) 2 = (3306970088907682056819 : ℚ) / 53506198101772210102000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor05_moment3_before"
  err.flush

theorem factor05_moment3 : prefixMoment (5 : Fin 10) 3 = (606276188047117881458487946413 : ℚ) / 37929063390807841115761836890000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor05_moment4_before"
  err.flush

theorem factor05_moment4 : prefixMoment (5 : Fin 10) 4 = (2868740214049495621065343055521437339448101 : ℚ) / 676688582890530850448074415156240019186400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor05_moment5_before"
  err.flush

theorem factor05_moment5 : prefixMoment (5 : Fin 10) 5 = (34052007869593393411403064736988857489845065844243201 : ℚ) / 29548646103023179278675487606246027341822498866076800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor05_moment6_before"
  err.flush

theorem factor05_moment6 : prefixMoment (5 : Fin 10) 6 = (1478979354962050036578684353624284639260753500627870509518665079 : ℚ) / 4608167883371595281549084470534309951982920870422757878310720000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor05_first_moment_before"
  err.flush

theorem factor05_first_moment :
    prefixMoment (5 : Fin 10) 1 = 1 - meansOf row (5 : Fin 10) / topsOf row (5 : Fin 10) := by
  rw [factor05_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor05_gap_before"
  err.flush

theorem factor05_gap_value :
    gapEvaluator (prefixMoment (5 : Fin 10)) = (1915119628117796442411122783137096269595938944187147379106671721549 : ℚ) / 1309138603230566841349171724583610781813329792733738033611000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor05_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor05_saved_Q80_before"
  err.flush

theorem factor05_saved_Q80 :
    momentRow.factorFloorsQ80[5]! = factorFloorQ80 (prefixMoment (5 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor05_gap_value]
  decide +kernel

theorem factor05_Q80_lower :
    ((momentRow.factorFloorsQ80[5]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (5 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor05_gap_value]
  decide +kernel

theorem factor05_Q80_upper :
    gapEvaluator (prefixMoment (5 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[5]! : ℤ) : ℚ) + 1 := by
  rw [factor05_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor05_complete"
  err.flush

#print axioms factor05_moment1
#print axioms factor05_moment2
#print axioms factor05_moment3
#print axioms factor05_moment4
#print axioms factor05_moment5
#print axioms factor05_moment6
#print axioms factor05_first_moment
#print axioms factor05_gap_value
#print axioms factor05_saved_Q80
#print axioms factor05_Q80_lower
#print axioms factor05_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor
-- END DONOR MomentFactor05

-- BEGIN DONOR MomentFactor06
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row002
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor06_moment1_before"
  err.flush

theorem factor06_moment1 : prefixMoment (6 : Fin 10) 1 = (4808670907 : ℚ) / 19095850200 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor06_moment2_before"
  err.flush

theorem factor06_moment2 : prefixMoment (6 : Fin 10) 2 = (633631060122710535961 : ℚ) / 9827357786499639078000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor06_moment3_before"
  err.flush

theorem factor06_moment3 : prefixMoment (6 : Fin 10) 3 = (8804416185860477223646111046629 : ℚ) / 525452906027841932525151523680000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor06_moment4_before"
  err.flush

theorem factor06_moment4 : prefixMoment (6 : Fin 10) 4 = (100750110118703909297243207677056251378881 : ℚ) / 22827281706006838453071772794826199474400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor06_moment5_before"
  err.flush

theorem factor06_moment5 : prefixMoment (6 : Fin 10) 5 = (1005658123736258170998602690805071464448708328902509 : ℚ) / 854376449784969773459898274151335422788983824364800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor06_moment6_before"
  err.flush

theorem factor06_moment6 : prefixMoment (6 : Fin 10) 6 = (9066467921257705083538957323461026842385675303249888932940201 : ℚ) / 28551328224127808759656768013256758386181177310513329167680000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor06_first_moment_before"
  err.flush

theorem factor06_first_moment :
    prefixMoment (6 : Fin 10) 1 = 1 - meansOf row (6 : Fin 10) / topsOf row (6 : Fin 10) := by
  rw [factor06_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor06_gap_before"
  err.flush

theorem factor06_gap_value :
    gapEvaluator (prefixMoment (6 : Fin 10)) = (10690119648918653289747651386069041846273915871998536447789395477093 : ℚ) / 11420531289651123503862707205302703354472470924205331667072000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor06_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor06_saved_Q80_before"
  err.flush

theorem factor06_saved_Q80 :
    momentRow.factorFloorsQ80[6]! = factorFloorQ80 (prefixMoment (6 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor06_gap_value]
  decide +kernel

theorem factor06_Q80_lower :
    ((momentRow.factorFloorsQ80[6]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (6 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor06_gap_value]
  decide +kernel

theorem factor06_Q80_upper :
    gapEvaluator (prefixMoment (6 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[6]! : ℤ) : ℚ) + 1 := by
  rw [factor06_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor06_complete"
  err.flush

#print axioms factor06_moment1
#print axioms factor06_moment2
#print axioms factor06_moment3
#print axioms factor06_moment4
#print axioms factor06_moment5
#print axioms factor06_moment6
#print axioms factor06_first_moment
#print axioms factor06_gap_value
#print axioms factor06_saved_Q80
#print axioms factor06_Q80_lower
#print axioms factor06_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor
-- END DONOR MomentFactor06

-- BEGIN DONOR MomentFactor07
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row002
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor07_moment1_before"
  err.flush

theorem factor07_moment1 : prefixMoment (7 : Fin 10) 1 = (2299001017 : ℚ) / 15749623680 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor07_moment2_before"
  err.flush

theorem factor07_moment2 : prefixMoment (7 : Fin 10) 2 = (29723841992782805519 : ℚ) / 1336992982272114241536 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor07_moment3_before"
  err.flush

theorem factor07_moment3 : prefixMoment (7 : Fin 10) 3 = (207519612687317369356131725183 : ℚ) / 58959981734042789854049750482944 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor07_moment4_before"
  err.flush

theorem factor07_moment4 : prefixMoment (7 : Fin 10) 4 = (1219580907007509991048706162324394187079 : ℚ) / 2112559368216678711372327954087205738119168 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor07_moment5_before"
  err.flush

theorem factor07_moment5 : prefixMoment (7 : Fin 10) 5 = (31892174682663467227171555231491700888306988023387 : ℚ) / 326065747500498175555098716095694521125512564548042752 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor07_moment6_before"
  err.flush

theorem factor07_moment6 : prefixMoment (7 : Fin 10) 6 = (153420926107770198759273609630369564270397330547346542759923 : ℚ) / 8986972431623807035658914796577108257938107642800919592965242880 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor07_first_moment_before"
  err.flush

theorem factor07_first_moment :
    prefixMoment (7 : Fin 10) 1 = 1 - meansOf row (7 : Fin 10) / topsOf row (7 : Fin 10) := by
  rw [factor07_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor07_gap_before"
  err.flush

theorem factor07_gap_value :
    gapEvaluator (prefixMoment (7 : Fin 10)) = (254371708717649627957823005809584094080082431593265099389313816853 : ℚ) / 399420996961058090473729546514538144797249228568929759687344128000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor07_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor07_saved_Q80_before"
  err.flush

theorem factor07_saved_Q80 :
    momentRow.factorFloorsQ80[7]! = factorFloorQ80 (prefixMoment (7 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor07_gap_value]
  decide +kernel

theorem factor07_Q80_lower :
    ((momentRow.factorFloorsQ80[7]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (7 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor07_gap_value]
  decide +kernel

theorem factor07_Q80_upper :
    gapEvaluator (prefixMoment (7 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[7]! : ℤ) : ℚ) + 1 := by
  rw [factor07_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor07_complete"
  err.flush

#print axioms factor07_moment1
#print axioms factor07_moment2
#print axioms factor07_moment3
#print axioms factor07_moment4
#print axioms factor07_moment5
#print axioms factor07_moment6
#print axioms factor07_first_moment
#print axioms factor07_gap_value
#print axioms factor07_saved_Q80
#print axioms factor07_Q80_lower
#print axioms factor07_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor
-- END DONOR MomentFactor07

-- BEGIN DONOR MomentFactor08
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row002
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor08_moment1_before"
  err.flush

theorem factor08_moment1 : prefixMoment (8 : Fin 10) 1 = (37112247817 : ℚ) / 192932890080 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor08_moment2_before"
  err.flush

theorem factor08_moment2 : prefixMoment (8 : Fin 10) 2 = (622441458022635498959 : ℚ) / 16378164032833399458816 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor08_moment3_before"
  err.flush

theorem factor08_moment3 : prefixMoment (8 : Fin 10) 3 = (4858961996000376099895583255227 : ℚ) / 631977304211771153748095762989056 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor08_moment4_before"
  err.flush

theorem factor08_moment4 : prefixMoment (8 : Fin 10) 4 = (503648830656836293098330800033830380745649 : ℚ) / 317015940193015349125309963610211311076507648 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor08_moment5_before"
  err.flush

theorem factor08_moment5 : prefixMoment (8 : Fin 10) 5 = (28651740187425485180808228067746013743701735985639331 : ℚ) / 85627922160013638071164751897192778383695151130608664576 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor08_moment6_before"
  err.flush

theorem factor08_moment6 : prefixMoment (8 : Fin 10) 6 = (1184563998089799210203363562163253275248982511628195552929837503 : ℚ) / 16520442493876707405284932295351565772471256657310709206136997806080 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor08_first_moment_before"
  err.flush

theorem factor08_first_moment :
    prefixMoment (8 : Fin 10) 1 = 1 - meansOf row (8 : Fin 10) / topsOf row (8 : Fin 10) := by
  rw [factor08_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor08_gap_before"
  err.flush

theorem factor08_gap_value :
    gapEvaluator (prefixMoment (8 : Fin 10)) = (39456533630777542897199037914127988075932537073657497117566487105139 : ℚ) / 51626382793364710641515413422973643038972677054095966269178118144000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor08_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor08_saved_Q80_before"
  err.flush

theorem factor08_saved_Q80 :
    momentRow.factorFloorsQ80[8]! = factorFloorQ80 (prefixMoment (8 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor08_gap_value]
  decide +kernel

theorem factor08_Q80_lower :
    ((momentRow.factorFloorsQ80[8]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (8 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor08_gap_value]
  decide +kernel

theorem factor08_Q80_upper :
    gapEvaluator (prefixMoment (8 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[8]! : ℤ) : ℚ) + 1 := by
  rw [factor08_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor08_complete"
  err.flush

#print axioms factor08_moment1
#print axioms factor08_moment2
#print axioms factor08_moment3
#print axioms factor08_moment4
#print axioms factor08_moment5
#print axioms factor08_moment6
#print axioms factor08_first_moment
#print axioms factor08_gap_value
#print axioms factor08_saved_Q80
#print axioms factor08_Q80_lower
#print axioms factor08_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor
-- END DONOR MomentFactor08

-- BEGIN DONOR MomentFactor09
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row002
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor09_moment1_before"
  err.flush

theorem factor09_moment1 : prefixMoment (9 : Fin 10) 1 = (40575312457 : ℚ) / 192929597280 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor09_moment2_before"
  err.flush

theorem factor09_moment2 : prefixMoment (9 : Fin 10) 2 = (737087702706526913999 : ℚ) / 16377604982914112695296 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor09_moment3_before"
  err.flush

theorem factor09_moment3 : prefixMoment (9 : Fin 10) 3 = (6180440007299750683359390773467 : ℚ) / 631944946752908208626398526078976 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor09_moment4_before"
  err.flush

theorem factor09_moment4 : prefixMoment (9 : Fin 10) 4 = (62094028930375156362560451433518808494259 : ℚ) / 28817663509858274848513904817666025872949248 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor09_moment5_before"
  err.flush

theorem factor09_moment5 : prefixMoment (9 : Fin 10) 5 = (41157576280585756200174764397798504354395721045212131 : ℚ) / 85620615318815627456549846209469396298574846482790219776 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor09_moment6_before"
  err.flush

theorem factor09_moment6 : prefixMoment (9 : Fin 10) 6 = (1791876603392625063908151132112420689338710090405564877578710463 : ℚ) / 16518750832324897811762672527438865150368767769862541552106371809280 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor09_first_moment_before"
  err.flush

theorem factor09_first_moment :
    prefixMoment (9 : Fin 10) 1 = 1 - meansOf row (9 : Fin 10) / topsOf row (9 : Fin 10) := by
  rw [factor09_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor09_gap_before"
  err.flush

theorem factor09_gap_value :
    gapEvaluator (prefixMoment (9 : Fin 10)) = (31684917211782691903337791839503743639488470244438346777373838723379 : ℚ) / 51621096351015305661758351648246453594902399280820442350332411904000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor09_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor09_saved_Q80_before"
  err.flush

theorem factor09_saved_Q80 :
    momentRow.factorFloorsQ80[9]! = factorFloorQ80 (prefixMoment (9 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor09_gap_value]
  decide +kernel

theorem factor09_Q80_lower :
    ((momentRow.factorFloorsQ80[9]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (9 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor09_gap_value]
  decide +kernel

theorem factor09_Q80_upper :
    gapEvaluator (prefixMoment (9 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[9]! : ℤ) : ℚ) + 1 := by
  rw [factor09_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_MOMENT factor09_complete"
  err.flush

#print axioms factor09_moment1
#print axioms factor09_moment2
#print axioms factor09_moment3
#print axioms factor09_moment4
#print axioms factor09_moment5
#print axioms factor09_moment6
#print axioms factor09_first_moment
#print axioms factor09_gap_value
#print axioms factor09_saved_Q80
#print axioms factor09_Q80_lower
#print axioms factor09_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor
-- END DONOR MomentFactor09

-- BEGIN DONOR PrefixFloorChecks
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! All five original floor obligations for the actual cell01 row2, expressed
through the existing finite prefix evaluator. The old two equalities are
reused. Both Q80 bounds remain explicit, and the saved new field is the
maximum of the exact old and new Q96 evaluations. The separate bridge to
the original rationalMoment still requires its own acceptance. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row002
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_FLOOR first_moments_before"
  err.flush

theorem all_first_moments (j : Fin 10) :
    prefixMoment j 1 = 1 - meansOf row j / topsOf row j := by
  fin_cases j
  · exact factor00_first_moment
  · exact factor01_first_moment
  · exact factor02_first_moment
  · exact factor03_first_moment
  · exact factor04_first_moment
  · exact factor05_first_moment
  · exact factor06_first_moment
  · exact factor07_first_moment
  · exact factor08_first_moment
  · exact factor09_first_moment

theorem all_saved_Q80 (j : Fin 10) :
    momentRow.factorFloorsQ80[j.val]! = factorFloorQ80 (prefixMoment j) := by
  fin_cases j
  · exact factor00_saved_Q80
  · exact factor01_saved_Q80
  · exact factor02_saved_Q80
  · exact factor03_saved_Q80
  · exact factor04_saved_Q80
  · exact factor05_saved_Q80
  · exact factor06_saved_Q80
  · exact factor07_saved_Q80
  · exact factor08_saved_Q80
  · exact factor09_saved_Q80

theorem all_Q80_bounds (j : Fin 10) :
    ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
        gapEvaluator (prefixMoment j) * (2 : ℚ)^80 ∧
      gapEvaluator (prefixMoment j) * (2 : ℚ)^80 <
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1 := by
  fin_cases j
  · exact ⟨factor00_Q80_lower, factor00_Q80_upper⟩
  · exact ⟨factor01_Q80_lower, factor01_Q80_upper⟩
  · exact ⟨factor02_Q80_lower, factor02_Q80_upper⟩
  · exact ⟨factor03_Q80_lower, factor03_Q80_upper⟩
  · exact ⟨factor04_Q80_lower, factor04_Q80_upper⟩
  · exact ⟨factor05_Q80_lower, factor05_Q80_upper⟩
  · exact ⟨factor06_Q80_lower, factor06_Q80_upper⟩
  · exact ⟨factor07_Q80_lower, factor07_Q80_upper⟩
  · exact ⟨factor08_Q80_lower, factor08_Q80_upper⟩
  · exact ⟨factor09_Q80_lower, factor09_Q80_upper⟩

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_FLOOR total_Q80_before"
  err.flush

theorem total_Q80_eq_saved :
    totalLowerQ80 prefixMoment =
      ((∑ j : Fin 10, momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) / (2 : ℚ)^80 := by
  calc
    totalLowerQ80 prefixMoment =
        ((∑ j : Fin 10, factorFloorQ80 (prefixMoment j) : ℤ) : ℚ) / (2 : ℚ)^80 := by
      simp only [totalLowerQ80, factorLowerQ80, roundDownQ, factorFloorQ80,
        Int.cast_sum, Finset.sum_div]
    _ = _ := by simp_rw [← all_saved_Q80]

theorem total_Q80_value :
    totalLowerQ80 prefixMoment = (9388399269062852289279 : ℚ) / (2 : ℚ)^80 := by
  have h : (∑ j : Fin 10, momentRow.factorFloorsQ80[j.val]! : ℤ) = 9388399269062852289279 := by
    decide +kernel
  rw [total_Q80_eq_saved, h]
  norm_num

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_FLOOR new_Q96_before"
  err.flush

theorem new_Q96_value :
    newFloorQ96 (massOf row) (meansOf row) prefixMoment = 654960955602494 := by
  unfold newFloorQ96 newEvaluator
  rw [← jensen_eq, total_Q80_value]
  decide +kernel

theorem saved_new_Q96_max :
    momentRow.newFloorQ96 =
      max (oldFloorQ96 (massOf row) (meansOf row))
        (newFloorQ96 (massOf row) (meansOf row) prefixMoment) := by
  rw [← moment_old_eq_evaluator, new_Q96_value]
  decide +kernel

def PrefixFloorChecks : Prop :=
  (∀ j : Fin 10, prefixMoment j 1 = 1 - meansOf row j / topsOf row j) ∧
  (∀ j : Fin 10, momentRow.factorFloorsQ80[j.val]! = factorFloorQ80 (prefixMoment j)) ∧
  momentRow.oldFloorQ96 = row.jensenFloorQ96 ∧
  momentRow.oldFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) ∧
  momentRow.newFloorQ96 =
    max (oldFloorQ96 (massOf row) (meansOf row))
      (newFloorQ96 (massOf row) (meansOf row) prefixMoment)

theorem prefix_floor_checks : PrefixFloorChecks :=
  ⟨all_first_moments, all_saved_Q80, moment_old_matches_geometry,
    moment_old_eq_evaluator, saved_new_Q96_max⟩

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW002_FLOOR complete"
  err.flush

#print axioms all_first_moments
#print axioms all_saved_Q80
#print axioms all_Q80_bounds
#print axioms total_Q80_eq_saved
#print axioms total_Q80_value
#print axioms new_Q96_value
#print axioms saved_new_Q96_max
#print axioms prefix_floor_checks

end ImbalancedChen.P2OriginalSaving19Cell01Row002MomentFloor
-- END DONOR PrefixFloorChecks
