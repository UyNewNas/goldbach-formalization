import ImbalancedChen.P2OriginalSaving19Geometry01BoundedAccess
import ImbalancedChen.P2OriginalSaving19RowNumericsPure
import Mathlib.Tactic.FinCases
import ImbalancedChen.P2Winner9FastDetPure
import ImbalancedChen.P2OriginalSaving19Moment01Shape
import ImbalancedChen.P2OriginalSaving19PrefixMoments
import Mathlib.Algebra.BigOperators.Field

/-! SOURCE CANDIDATE: original Cell01 row 16 only.
Twenty-one accepted row000 source bodies are merged into one new owner.
Original ordinal, vertex order and decoded row/record identities are retained.
All host-produced literals remain closed Lean proof obligations. This owner
has not been compiled, independently replayed or audited. No integral or
OriginalFloorBridge claim is included. The shared bounded-access owner is
imported unchanged. -/

-- BEGIN DONOR Input
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! The actual original row 16 and its original nine ordered vertices. The small
selectors refer to the already decoded values, with closed equalities to
the original bounded accesses. No numeric field is recomputed or assumed. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2OriginalSaving19RowNumericsPure
open P2OriginalSaving19Geometry01Decoding
open P2OriginalSaving19Geometry01DirectDecoding
open P2OriginalSaving19Geometry01BoundedAccess

noncomputable def row : GeometryRow := geometryRowsTyped016

noncomputable def vertices : Fin 9 → QPoint :=
  ![(fun j => geometryVerticesTyped039[j.val]!),
    (fun j => geometryVerticesTyped035[j.val]!),
    (fun j => geometryVerticesTyped029[j.val]!),
    (fun j => geometryVerticesTyped028[j.val]!),
    (fun j => geometryVerticesTyped026[j.val]!),
    (fun j => geometryVerticesTyped017[j.val]!),
    (fun j => geometryVerticesTyped012[j.val]!),
    (fun j => geometryVerticesTyped002[j.val]!),
    (fun j => geometryVerticesTyped000[j.val]!)]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_INPUT before_row_binding"
  err.flush

theorem boundedRow_eq : boundedRow (16 : Fin 144) = row := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_INPUT before_vertex_binding"
  err.flush

theorem boundedRowVertex_eq : boundedRowVertex (16 : Fin 144) = vertices := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem raw_row_eq : concreteGeometry01.rows[16]! = row :=
  (row_lookup_no_fallback (16 : Fin 144)).trans boundedRow_eq

theorem raw_vertices_eq (i : Fin 9) (j : Fin 8) :
    ((concreteGeometry01.vertices[
      (concreteGeometry01.rows[16]!).vertexIds[i.val]!]!)[j.val]!) = vertices i j :=
  (raw_vertex_no_fallback (16 : Fin 144) i j).trans
    (congrFun (congrFun boundedRowVertex_eq i) j)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_INPUT bindings_complete"
  err.flush

#print axioms boundedRow_eq
#print axioms boundedRowVertex_eq
#print axioms raw_row_eq
#print axioms raw_vertices_eq

/-- The original factor and mean lookups retain the certified bounds. -/
theorem factor_maximum_no_fallback (j : Fin 10) :
    row.factorMaxima[j.val]! =
      (boundedRow (16 : Fin 144)).factorMaxima[j.val]'(factor_maximum_bound (16 : Fin 144) j) := by
  rw [← raw_row_eq]
  exact factor_maximum_lookup_no_fallback (16 : Fin 144) j

theorem weighted_mean_no_fallback (j : Fin 10) :
    row.gapWeightedMeans[j.val]! =
      (boundedRow (16 : Fin 144)).gapWeightedMeans[j.val]'(weighted_mean_bound (16 : Fin 144) j) := by
  rw [← raw_row_eq]
  exact weighted_mean_lookup_no_fallback (16 : Fin 144) j

#print axioms factor_maximum_no_fallback
#print axioms weighted_mean_no_fallback

end ImbalancedChen.P2OriginalSaving19Cell01Row016
-- END DONOR Input

-- BEGIN DONOR Determinant
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row16.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Determinant_physical_volume_positive_before"
  err.flush

theorem physical_volume_positive :
    0 < row.physicalVolume := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Determinant_volume_eq_before"
  err.flush

theorem volume_eq :
    row.physicalVolume = |(edgeOf vertices).det| / (Nat.factorial 8 : ℚ) := by
  rw [← P2Winner9FastDetPure.fastDet_eq (edgeOf vertices)]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Determinant_det_ne_before"
  err.flush

theorem det_ne :
    (edgeOf vertices).det ≠ 0 := by
  intro hzero
  have h := volume_eq
  rw [hzero, abs_zero, zero_div] at h
  exact (ne_of_gt physical_volume_positive) h

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Determinant_complete"
  err.flush

#print axioms physical_volume_positive
#print axioms volume_eq
#print axioms det_ne

end ImbalancedChen.P2OriginalSaving19Cell01Row016
-- END DONOR Determinant

-- BEGIN DONOR Physical
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row16.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Physical_all_physical_before"
  err.flush

theorem all_physical :
    ∀ i : Fin 9, PhysicalQ (vertices i) := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Physical_complete"
  err.flush

#print axioms all_physical

end ImbalancedChen.P2OriginalSaving19Cell01Row016
-- END DONOR Physical

-- BEGIN DONOR Gap
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row16.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Gap_gap_sum_positive_before"
  err.flush

theorem gap_sum_positive :
    0 < gapSumOf vertices := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Gap_mean_gap_eq_before"
  err.flush

theorem mean_gap_eq :
    row.meanGap = gapSumOf vertices / 9 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Gap_complete"
  err.flush

#print axioms gap_sum_positive
#print axioms mean_gap_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row016
-- END DONOR Gap

-- BEGIN DONOR Means
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row16.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Means_weighted_means_eq_before"
  err.flush

theorem weighted_means_eq :
    ∀ j : Fin 10, meansOf row j = computedMeanOf vertices j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Means_complete"
  err.flush

#print axioms weighted_means_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row016
-- END DONOR Means

-- BEGIN DONOR Maxima
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row16.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Maxima_factor_le_maxima_before"
  err.flush

theorem factor_le_maxima :
    ∀ i : Fin 9, ∀ j : Fin 10, factorsQ (vertices i) j ≤ topsOf row j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Maxima_factor_maxima_attained_before"
  err.flush

theorem factor_maxima_attained :
    ∀ j : Fin 10, ∃ i : Fin 9, factorsQ (vertices i) j = topsOf row j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Maxima_complete"
  err.flush

#print axioms factor_le_maxima
#print axioms factor_maxima_attained

end ImbalancedChen.P2OriginalSaving19Cell01Row016
-- END DONOR Maxima

-- BEGIN DONOR Jensen
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row16.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Jensen_jensen_eq_before"
  err.flush

theorem jensen_eq :
    row.jensenBound = oldEvaluator (massOf row) (meansOf row) := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Jensen_old_floor_eq_before"
  err.flush

theorem old_floor_eq :
    row.jensenFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) := by
  unfold oldFloorQ96
  rw [← jensen_eq]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Jensen_complete"
  err.flush

#print axioms jensen_eq
#print axioms old_floor_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row016
-- END DONOR Jensen

-- BEGIN DONOR Arithmetic
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row16.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Arithmetic_row_data_checks_before"
  err.flush

theorem row_data_checks :
    RowDataChecksFor vertices row := by
  exact ⟨det_ne, all_physical, gap_sum_positive, volume_eq, mean_gap_eq,
    weighted_means_eq, factor_le_maxima, factor_maxima_attained,
    jensen_eq, old_floor_eq⟩

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Arithmetic_bounded_row_data_checks_before"
  err.flush

theorem bounded_row_data_checks :
    RowDataChecksFor
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRowVertex (16 : Fin 144))
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (16 : Fin 144)) := by
  rw [boundedRowVertex_eq, boundedRow_eq]
  exact row_data_checks

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016 Arithmetic_complete"
  err.flush

#print axioms row_data_checks
#print axioms bounded_row_data_checks

end ImbalancedChen.P2OriginalSaving19Cell01Row016
-- END DONOR Arithmetic

-- BEGIN DONOR OldFloor
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! The actual moment row16 old floor is the actual geometry row16 Jensen
floor and the same original exact Q96 arithmetic. The ten Q80 fields and
the new Q96 field are not certified by these old-floor equalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open P2OriginalSaving19Archive
open P2OriginalSaving19Moment01Decoding
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

noncomputable def momentRow : MomentRecord :=
  momentConcrete01.rows[(16 : Fin 144).val]'(P2OriginalSaving19Moment01Shape.row_bound 16)

theorem raw_moment_row_eq : momentConcrete01.rows[16]! = momentRow :=
  P2OriginalSaving19Moment01Shape.row_lookup_no_fallback (16 : Fin 144)

theorem moment_row_eq : momentRow = momentTypedRecord016 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_OLD_FLOOR before_original_moment_geometry_binding"
  err.flush

theorem moment_old_matches_geometry : momentRow.oldFloorQ96 = row.jensenFloorQ96 := by
  decide +kernel

theorem moment_old_eq_evaluator :
    momentRow.oldFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) :=
  moment_old_matches_geometry.trans old_floor_eq

theorem actual_moment_old_eq_bounded_evaluator :
    (momentConcrete01.rows[16]!).oldFloorQ96 =
      oldFloorQ96
        (massOf (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (16 : Fin 144)))
        (meansOf (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (16 : Fin 144))) := by
  rw [raw_moment_row_eq, boundedRow_eq]
  exact moment_old_eq_evaluator

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_OLD_FLOOR complete"
  err.flush

#print axioms raw_moment_row_eq
#print axioms moment_row_eq
#print axioms moment_old_matches_geometry
#print axioms moment_old_eq_evaluator
#print axioms actual_moment_old_eq_bounded_evaluator

/-- The saved ten Q80 fields are accessed at their true bounded indices. -/
theorem moment_floor_bound (j : Fin 10) : j.val < momentRow.factorFloorsQ80.size := by
  have hs : momentRow.factorFloorsQ80.size = 10 :=
    (P2OriginalSaving19Moment01Shape.row_ids_and_floor_sizes_bounded (16 : Fin 144)).2
  rw [hs]
  exact j.isLt

theorem moment_floor_lookup_no_fallback (j : Fin 10) :
    momentRow.factorFloorsQ80[j.val]! =
      momentRow.factorFloorsQ80[j.val]'(moment_floor_bound j) :=
  getElem!_pos momentRow.factorFloorsQ80 j.val (moment_floor_bound j)

#print axioms moment_floor_bound
#print axioms moment_floor_lookup_no_fallback

end ImbalancedChen.P2OriginalSaving19Cell01Row016
-- END DONOR OldFloor

-- BEGIN DONOR MomentEncoding
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact nonnegative integer encodings of the actual nine ordered vertices.
The existing prefix evaluator is used unchanged. Host-generated literals
are connected to the decoded row by closed Lean equalities below. No
saved field, moment value or final floor is an assumption. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row016
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

def gapScale : Nat := 98000000

def gapNats : Fin 9 → Nat := ![0, 0, 0, 0, 0, 0, 0, 515533, 0]

def deviationDenominators : Fin 10 → Nat := ![70256880680, 491798164760, 1181092848600, 1940663417280, 1181092848600, 450032662940, 1350076609140, 1113498394176, 556749197088, 556739695008]

def deviationNats : Fin 10 → Fin 9 → Nat :=
  ![![10035339800, 35785608152, 16070304425, 16070304425, 20764618280, 14815711400, 10035339800, 8331013280, 0],
    ![70247378600, 250499257064, 112492130975, 112492130975, 145352327960, 103709979800, 70247378600, 33324053120, 0],
    ![0, 67594454424, 126739008165, 126739008165, 137692407160, 155043385560, 168986136060, 218405981460, 239233514660],
    ![0, 270377817696, 211233263955, 211233263955, 200279864960, 276624169920, 337972272120, 323777049360, 548714407920],
    ![337972272120, 67594454424, 126739008165, 126739008165, 137692407160, 155043385560, 0, 272658501120, 280989514400],
    ![239233514660, 171639060236, 112494506495, 112494506495, 101541107500, 131037770780, 70247378600, 95806652720, 0],
    ![506956032660, 236578214964, 0, 295722768705, 306676167700, 324027146100, 506956032660, 333137222340, 366461275460],
    ![270377817696, 0, 354867322446, 59144553741, 70097952736, 87448931136, 270377817696, 96559007376, 129883060496],
    ![135188908848, 0, 177443163303, 177443163303, 35048976368, 43724465568, 135188908848, 48279503688, 64941530248],
    ![135188908848, 0, 177433661223, 177433661223, 210293858208, 168651510048, 135188908848, 98265583368, 64941530248]]

def prefixMoment (j : Fin 10) (k : Nat) : ℚ :=
  normalizedMoment gapNats (deviationNats j) (deviationDenominators j) k

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT gap_encoding_before"
  err.flush

theorem gapScale_ne : gapScale ≠ 0 := by decide +kernel

theorem gap_encoding : ∀ i : Fin 9,
    gapQ (vertices i) = (gapNats i : ℚ) / (gapScale : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT deviation_encoding_before"
  err.flush

theorem deviationDenominators_ne : ∀ j : Fin 10, deviationDenominators j ≠ 0 := by
  decide +kernel

theorem deviation_encoding : ∀ (j : Fin 10) (i : Fin 9),
    1 - factorsQ (vertices i) j / topsOf row j =
      (deviationNats j i : ℚ) / (deviationDenominators j : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT encoding_complete"
  err.flush

#print axioms gapScale_ne
#print axioms gap_encoding
#print axioms deviationDenominators_ne
#print axioms deviation_encoding

end ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor
-- END DONOR MomentEncoding

-- BEGIN DONOR MomentFactor00
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row016
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor00_moment1_before"
  err.flush

theorem factor00_moment1 : prefixMoment (0 : Fin 10) 1 = (70119626421 : ℚ) / 351284403400 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor00_moment2_before"
  err.flush

theorem factor00_moment2 : prefixMoment (0 : Fin 10) 2 = (1603933534861674572037 : ℚ) / 38783087222658092776000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor00_moment3_before"
  err.flush

theorem factor00_moment3 : prefixMoment (0 : Fin 10) 3 = (169586825413245675474720295435467 : ℚ) / 19073451119830255516198613773760000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor00_moment4_before"
  err.flush

theorem factor00_moment4 : prefixMoment (0 : Fin 10) 4 = (34554756551396973721519596470370317483861061 : ℚ) / 17420535333262446367521211596097990854438400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor00_moment5_before"
  err.flush

theorem factor00_moment5 : prefixMoment (0 : Fin 10) 5 = (786902124706856529245753995942312663457691621720431511 : ℚ) / 1713477461207041221394972066666524455867213884094156800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor00_moment6_before"
  err.flush

theorem factor00_moment6 : prefixMoment (0 : Fin 10) 6 = (5109175440095115643235987638587991219899808601266048252081695363 : ℚ) / 46301377515343239948995390630662697710063373761093278531850240000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor00_first_moment_before"
  err.flush

theorem factor00_first_moment :
    prefixMoment (0 : Fin 10) 1 = 1 - meansOf row (0 : Fin 10) / topsOf row (0 : Fin 10) := by
  rw [factor00_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor00_gap_before"
  err.flush

theorem factor00_gap_value :
    gapEvaluator (prefixMoment (0 : Fin 10)) = (205941011848987040721542571434549001604112367266765142065440205357489 : ℚ) / 170999405596438102084357976760970190406484050822219494577856000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor00_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor00_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor00_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor
-- END DONOR MomentFactor00

-- BEGIN DONOR MomentFactor01
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row016
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor01_moment1_before"
  err.flush

theorem factor01_moment1 : prefixMoment (1 : Fin 10) 1 = (465844345107 : ℚ) / 2458990823800 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor01_moment2_before"
  err.flush

theorem factor01_moment2 : prefixMoment (1 : Fin 10) 2 = (500038042455714183678771 : ℚ) / 13302598917371725822168000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor01_moment3_before"
  err.flush

theorem factor01_moment3 : prefixMoment (1 : Fin 10) 3 = (51034359181269734501035785720892461 : ℚ) / 6542193734101777642056124524399680000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor01_moment4_before"
  err.flush

theorem factor01_moment4 : prefixMoment (1 : Fin 10) 4 = (70749408340984361559919015756370708083940271141 : ℚ) / 41826705335163133728418429042231276041506598400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor01_moment5_before"
  err.flush

theorem factor01_moment5 : prefixMoment (1 : Fin 10) 5 = (848237489703479034890388530091420128321713894882333032549 : ℚ) / 2215262745423595523691176578804944348443097211536191795200000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor01_moment6_before"
  err.flush

theorem factor01_moment6 : prefixMoment (1 : Fin 10) 6 = (914648482758436213889207555184407457461579133828055776057326509116273 : ℚ) / 10116434274704859839695951894284123485369456596435031519702490787840000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor01_first_moment_before"
  err.flush

theorem factor01_first_moment :
    prefixMoment (1 : Fin 10) 1 = 1 - meansOf row (1 : Fin 10) / topsOf row (1 : Fin 10) := by
  rw [factor01_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor01_gap_before"
  err.flush

theorem factor01_gap_value :
    gapEvaluator (prefixMoment (1 : Fin 10)) = (41726517570151416163680965893351816076991824170693904652573764507308117693 : ℚ) / 31613857108452686999049849669637885891779551863859473499070283712000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor01_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor01_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor01_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor
-- END DONOR MomentFactor01

-- BEGIN DONOR MomentFactor02
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row016
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor02_moment1_before"
  err.flush

theorem factor02_moment1 : prefixMoment (2 : Fin 10) 1 = (243139979519 : ℚ) / 1968488081000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor02_moment2_before"
  err.flush

theorem factor02_moment2 : prefixMoment (2 : Fin 10) 2 = (1194548667147831868978411 : ℚ) / 76723917435773438707800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor02_moment3_before"
  err.flush

theorem factor02_moment3 : prefixMoment (2 : Fin 10) 3 = (60369848105373332707286544457867147 : ℚ) / 30206023399989619422537668346360000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor02_moment4_before"
  err.flush

theorem factor02_moment4 : prefixMoment (2 : Fin 10) 4 = (362910110124778190255834280825288366644956083061 : ℚ) / 1391368610672507875753601168172170969802744000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor02_moment5_before"
  err.flush

theorem factor02_moment5 : prefixMoment (2 : Fin 10) 5 = (26503803274610390328637171786153206210197894517061252134269 : ℚ) / 766889907388181121383885981864886630786255495826393920000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor02_moment6_before"
  err.flush

theorem factor02_moment6 : prefixMoment (2 : Fin 10) 6 = (9013708533372192913260088551894806355750020994584049371001299295813673 : ℚ) / 1940931825599350771345792003839443338010132059913573584368258240000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor02_first_moment_before"
  err.flush

theorem factor02_first_moment :
    prefixMoment (2 : Fin 10) 1 = 1 - meansOf row (2 : Fin 10) / topsOf row (2 : Fin 10) := by
  rw [factor02_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor02_gap_before"
  err.flush

theorem factor02_gap_value :
    gapEvaluator (prefixMoment (2 : Fin 10)) = (284200422695751686758643484597363445319150282254766192486782696790944125343 : ℚ) / 1399710451153377960105138464307290868757306773976134796419417000000000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor02_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor02_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor02_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor
-- END DONOR MomentFactor02

-- BEGIN DONOR MomentFactor03
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row016
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor03_moment1_before"
  err.flush

theorem factor03_moment1 : prefixMoment (3 : Fin 10) 1 = (1351994579623 : ℚ) / 9703317086400 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor03_moment2_before"
  err.flush

theorem factor03_moment2 : prefixMoment (3 : Fin 10) 2 = (4107754695240959435984491 : ℚ) / 207139597454288807142912000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor03_moment3_before"
  err.flush

theorem factor03_moment3 : prefixMoment (3 : Fin 10) 3 = (1157593159436260930746950249580606809 : ℚ) / 401988239049643705062018475250319360000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor03_moment4_before"
  err.flush

theorem factor03_moment4 : prefixMoment (3 : Fin 10) 4 = (105452515221042660952387654927897950312554501741 : ℚ) / 247356348929411321927250334406808252284298854400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor03_moment5_before"
  err.flush

theorem factor03_moment5 : prefixMoment (3 : Fin 10) 5 = (1772186596684444514551798279057829632222742230417620019807213 : ℚ) / 27554032958717262572277434214674113786648152221862987615436800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor03_moment6_before"
  err.flush

theorem factor03_moment6 : prefixMoment (3 : Fin 10) 6 = (377591231596190299434820354507398242498362303770367156851254972690184553 : ℚ) / 38195074115364279963459263196628470559108688519913035909802784834191360000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor03_first_moment_before"
  err.flush

theorem factor03_first_moment :
    prefixMoment (3 : Fin 10) 1 = 1 - meansOf row (3 : Fin 10) / topsOf row (3 : Fin 10) := by
  rw [factor03_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor03_gap_before"
  err.flush

theorem factor03_gap_value :
    gapEvaluator (prefixMoment (3 : Fin 10)) = (3059131061234730621015298699135620172704017469689391774052193716358625668383 : ℚ) / 10850873328228488625982745226314906408837695602248021565284882055168000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor03_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor03_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor03_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor
-- END DONOR MomentFactor03

-- BEGIN DONOR MomentFactor04
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row016
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor04_moment1_before"
  err.flush

theorem factor04_moment1 : prefixMoment (4 : Fin 10) 1 = (296347842039 : ℚ) / 1968488081000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor04_moment2_before"
  err.flush

theorem factor04_moment2 : prefixMoment (4 : Fin 10) 2 = (1791575729379252392919691 : ℚ) / 76723917435773438707800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor04_moment3_before"
  err.flush

theorem factor04_moment3 : prefixMoment (4 : Fin 10) 3 = (112422028414905109020053786526830207 : ℚ) / 30206023399989619422537668346360000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor04_moment4_before"
  err.flush

theorem factor04_moment4 : prefixMoment (4 : Fin 10) 4 = (846262099573809378837262557108895658538682892341 : ℚ) / 1391368610672507875753601168172170969802744000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor04_moment5_before"
  err.flush

theorem factor04_moment5 : prefixMoment (4 : Fin 10) 5 = (78004029072878386256731192502680748542033364254477763418389 : ℚ) / 766889907388181121383885981864886630786255495826393920000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor04_moment6_before"
  err.flush

theorem factor04_moment6 : prefixMoment (4 : Fin 10) 6 = (33728561031098923843953979135672302088706410063339510273312023539696713 : ℚ) / 1940931825599350771345792003839443338010132059913573584368258240000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor04_first_moment_before"
  err.flush

theorem factor04_first_moment :
    prefixMoment (4 : Fin 10) 1 = 1 - meansOf row (4 : Fin 10) / topsOf row (4 : Fin 10) := by
  rw [factor04_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor04_gap_before"
  err.flush

theorem factor04_gap_value :
    gapEvaluator (prefixMoment (4 : Fin 10)) = (112531675382295402044372979114296586098635060164012484706358382126309957127 : ℚ) / 236314751493427447809958442025906250569415429372594186408473000000000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor04_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor04_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor04_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor
-- END DONOR MomentFactor04

-- BEGIN DONOR MomentFactor05
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row016
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor05_moment1_before"
  err.flush

theorem factor05_moment1 : prefixMoment (5 : Fin 10) 1 = (565150575103 : ℚ) / 2250163314700 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor05_moment2_before"
  err.flush

theorem factor05_moment2 : prefixMoment (5 : Fin 10) 2 = (720178688584849461159491 : ℚ) / 11139116874207720719398000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor05_moment3_before"
  err.flush

theorem factor05_moment3 : prefixMoment (5 : Fin 10) 3 = (85416967306689002532696609686334719 : ℚ) / 5012966429699589558058494453710120000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor05_moment4_before"
  err.flush

theorem factor05_moment4 : prefixMoment (5 : Fin 10) 4 = (10365186093760817087225089043739393529473638297 : ℚ) / 2255998631586530593038081995290385866426952800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor05_moment5_before"
  err.flush

theorem factor05_moment5 : prefixMoment (5 : Fin 10) 5 = (23411691877587655538065645614651312502573263479914265286973 : ℚ) / 18477969906066258948736839466104936198878344950641144022400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor05_moment6_before"
  err.flush

theorem factor05_moment6 : prefixMoment (5 : Fin 10) 6 = (2121927660122359071505662031125837087989854240472854550444853173367233 : ℚ) / 5939778573251557267702603438721780219328587870883526360520525007040000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor05_first_moment_before"
  err.flush

theorem factor05_first_moment :
    prefixMoment (5 : Fin 10) 1 = 1 - meansOf row (5 : Fin 10) / topsOf row (5 : Fin 10) := by
  rw [factor05_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor05_gap_before"
  err.flush

theorem factor05_gap_value :
    gapEvaluator (prefixMoment (5 : Fin 10)) = (7135578511386727329593443750319889901561214968615203382636990936942187369 : ℚ) / 5062311284021213580428355203456062686927773753593914511807265631000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor05_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor05_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor05_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor
-- END DONOR MomentFactor05

-- BEGIN DONOR MomentFactor06
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row016
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor06_moment1_before"
  err.flush

theorem factor06_moment1 : prefixMoment (6 : Fin 10) 1 = (1069884027643 : ℚ) / 4500255363800 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor06_moment2_before"
  err.flush

theorem factor06_moment2 : prefixMoment (6 : Fin 10) 2 = (5757297543375383122165681 : ℚ) / 100248876780082818234678000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor06_moment3_before"
  err.flush

theorem factor06_moment3 : prefixMoment (6 : Fin 10) 3 = (2539673565754873109166389949081182203 : ℚ) / 180458218177797190307532046666342560000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor06_moment4_before"
  err.flush

theorem factor06_moment4 : prefixMoment (6 : Fin 10) 4 = (754563714450624705157181933588272421667888362291 : ℚ) / 215946917097003247106260759891864094782913930400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor06_moment5_before"
  err.flush

theorem factor06_moment5 : prefixMoment (6 : Fin 10) 5 = (2628486616879510466976775809296424505119675276960981277891963 : ℚ) / 2993194117642537386103577784855661925624515236579126828921600000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor06_moment6_before"
  err.flush

theorem factor06_moment6 : prefixMoment (6 : Fin 10) 6 = (87863579900408125462575408930930782796479280171886632915994316460131573 : ℚ) / 393607925147204330343155576551964074371170299427631082060955319243840000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor06_first_moment_before"
  err.flush

theorem factor06_first_moment :
    prefixMoment (6 : Fin 10) 1 = 1 - meansOf row (6 : Fin 10) / topsOf row (6 : Fin 10) := by
  rw [factor06_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor06_gap_before"
  err.flush

theorem factor06_gap_value :
    gapEvaluator (prefixMoment (6 : Fin 10)) = (4017293634643366231392676997326068270912110192578650236027910635027885169221537 : ℚ) / 5195624611943097160529653610485925781699447952444730283204610214018688000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor06_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor06_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor06_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor
-- END DONOR MomentFactor06

-- BEGIN DONOR MomentFactor07
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row016
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor07_moment1_before"
  err.flush

theorem factor07_moment1 : prefixMoment (7 : Fin 10) 1 = (478438490233 : ℚ) / 3711661313920 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor07_moment2_before"
  err.flush

theorem factor07_moment2 : prefixMoment (7 : Fin 10) 2 = (21671324141440926566149 : ℚ) / 1239878673832530670718976 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor07_moment3_before"
  err.flush

theorem factor07_moment3 : prefixMoment (7 : Fin 10) 3 = (50330013085069298110079091054366241 : ℚ) / 20248842713522006809805770657442562048 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor07_moment4_before"
  err.flush

theorem factor07_moment4 : prefixMoment (7 : Fin 10) 4 = (81244927369847988026699048028394402591082819159 : ℚ) / 219833774992934241593567707205824218078181607866368 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor07_moment5_before"
  err.flush

theorem factor07_moment5 : prefixMoment (7 : Fin 10) 5 = (21811593081902509208839386364126330431108633727930352780543 : ℚ) / 380775975129325041405692107682423972269356076504242107373846528 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor07_moment6_before"
  err.flush

theorem factor07_moment6 : prefixMoment (7 : Fin 10) 6 = (12575637194091756132223528742906637260802940690437972173006436714986269 : ℚ) / 1362836047009191259924230658875822748182220111246140182826536606019448995840 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor07_first_moment_before"
  err.flush

theorem factor07_first_moment :
    prefixMoment (7 : Fin 10) 1 = 1 - meansOf row (7 : Fin 10) / topsOf row (7 : Fin 10) := by
  rw [factor07_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor07_gap_before"
  err.flush

theorem factor07_gap_value :
    gapEvaluator (prefixMoment (7 : Fin 10)) = (939684700003283350815208148522241433656680176962501273566252023315772788181273 : ℚ) / 1635403256411029511909076790650987297818664133495368219391843927223338795008000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor07_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor07_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor07_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor
-- END DONOR MomentFactor07

-- BEGIN DONOR MomentFactor08
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row016
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor08_moment1_before"
  err.flush

theorem factor08_moment1 : prefixMoment (8 : Fin 10) 1 = (144256353977 : ℚ) / 927915328480 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor08_moment2_before"
  err.flush

theorem factor08_moment2 : prefixMoment (8 : Fin 10) 2 = (86069996135284976108711 : ℚ) / 3409666353039459344477184 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor08_moment3_before"
  err.flush

theorem factor08_moment3 : prefixMoment (8 : Fin 10) 3 = (899575319950279574442100463996081 : ℚ) / 210925444932520904268810111015026688 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor08_moment4_before"
  err.flush

theorem factor08_moment4 : prefixMoment (8 : Fin 10) 4 = (10266421420375597609158386206357139388240804929 : ℚ) / 13739610937058390099597981700364013629886350491648 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor08_moment5_before"
  err.flush

theorem factor08_moment5 : prefixMoment (8 : Fin 10) 5 = (219586636973138065379153418204401368631111767712905635401 : ℚ) / 1622624894017010119626528867964874881829642371466940798468096 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor08_moment6_before"
  err.flush

theorem factor08_moment6 : prefixMoment (8 : Fin 10) 6 = (48906757265349175144980339346297091151409581360705501690220317999011 : ℚ) / 1935846657683510312392373094994066403667926294383721850605875860823080960 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor08_first_moment_before"
  err.flush

theorem factor08_first_moment :
    prefixMoment (8 : Fin 10) 1 = 1 - meansOf row (8 : Fin 10) / topsOf row (8 : Fin 10) := by
  rw [factor08_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor08_gap_before"
  err.flush

theorem factor08_gap_value :
    gapEvaluator (prefixMoment (8 : Fin 10)) = (151291227977511752119052954560273331203637550086990637325894901632676090119 : ℚ) / 199634186573612000965463475421263097878254899108321315843730948147380224000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor08_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor08_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor08_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor
-- END DONOR MomentFactor08

-- BEGIN DONOR MomentFactor09
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row016
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor09_moment1_before"
  err.flush

theorem factor09_moment1 : prefixMoment (9 : Fin 10) 1 = (632831602691 : ℚ) / 2783698475040 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor09_moment2_before"
  err.flush

theorem factor09_moment2 : prefixMoment (9 : Fin 10) 2 = (179761733062059675617351 : ℚ) / 3409549967973609461320704 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor09_moment3_before"
  err.flush

theorem factor09_moment3 : prefixMoment (9 : Fin 10) 3 = (23627986948409536684575990367742189 : ℚ) / 1898231809284163499288591917835845632 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor09_moment4_before"
  err.flush

theorem factor09_moment4 : prefixMoment (9 : Fin 10) 4 = (2413574067377846052322054955806401613407657457 : ℚ) / 808157234189384689539904527119184259023696297984 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor09_moment5_before"
  err.flush

theorem factor09_moment5 : prefixMoment (9 : Fin 10) 5 = (38936899262670374187116855716593908322949660134755525283233 : ℚ) / 53542052237651716597710114498578999998918250705347270586400768 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor09_moment6_before"
  err.flush

theorem factor09_moment6 : prefixMoment (9 : Fin 10) 6 = (224832013937801676148443946163936627232654076509637846994307341582993 : ℚ) / 1252478396340026077005747083072925685243335261664702533655378692805754880 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor09_first_moment_before"
  err.flush

theorem factor09_first_moment :
    prefixMoment (9 : Fin 10) 1 = 1 - meansOf row (9 : Fin 10) / topsOf row (9 : Fin 10) := by
  rw [factor09_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor09_gap_before"
  err.flush

theorem factor09_gap_value :
    gapEvaluator (prefixMoment (9 : Fin 10)) = (57460166720100966212110177672382968995937924193589246055408193825406724933 : ℚ) / 66537914805563885340930313788249177028552185775937322100441993055305728000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor09_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor09_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW016_MOMENT factor09_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor
-- END DONOR MomentFactor09

-- BEGIN DONOR PrefixFloorChecks
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! All five original floor obligations for the actual cell01 row16, expressed
through the existing finite prefix evaluator. The old two equalities are
reused. Both Q80 bounds remain explicit, and the saved new field is the
maximum of the exact old and new Q96 evaluations. The separate bridge to
the original rationalMoment still requires its own acceptance. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row016
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_FLOOR first_moments_before"
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
  err.putStrLn "P26_CELL01_ROW016_FLOOR total_Q80_before"
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
    totalLowerQ80 prefixMoment = (9507158969598507809486 : ℚ) / (2 : ℚ)^80 := by
  have h : (∑ j : Fin 10, momentRow.factorFloorsQ80[j.val]! : ℤ) = 9507158969598507809486 := by
    decide +kernel
  rw [total_Q80_eq_saved, h]
  norm_num

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW016_FLOOR new_Q96_before"
  err.flush

theorem new_Q96_value :
    newFloorQ96 (massOf row) (meansOf row) prefixMoment = 13651523095432447917 := by
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
  err.putStrLn "P26_CELL01_ROW016_FLOOR complete"
  err.flush

#print axioms all_first_moments
#print axioms all_saved_Q80
#print axioms all_Q80_bounds
#print axioms total_Q80_eq_saved
#print axioms total_Q80_value
#print axioms new_Q96_value
#print axioms saved_new_Q96_max
#print axioms prefix_floor_checks

end ImbalancedChen.P2OriginalSaving19Cell01Row016MomentFloor
-- END DONOR PrefixFloorChecks
