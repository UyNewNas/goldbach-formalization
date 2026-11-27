import ImbalancedChen.P2OriginalSaving19Geometry01BoundedAccess
import ImbalancedChen.P2OriginalSaving19RowNumericsPure
import Mathlib.Tactic.FinCases
import ImbalancedChen.P2Winner9FastDetPure
import ImbalancedChen.P2OriginalSaving19Moment01Shape
import ImbalancedChen.P2OriginalSaving19PrefixMoments
import Mathlib.Algebra.BigOperators.Field

/-! SOURCE CANDIDATE: original Cell01 row 8 only.
Twenty-one accepted row000 source bodies are merged into one new owner.
Original ordinal, vertex order and decoded row/record identities are retained.
All host-produced literals remain closed Lean proof obligations. This owner
has not been compiled, independently replayed or audited. No integral or
OriginalFloorBridge claim is included. The shared bounded-access owner is
imported unchanged. -/

-- BEGIN DONOR Input
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! The actual original row 8 and its original nine ordered vertices. The small
selectors refer to the already decoded values, with closed equalities to
the original bounded accesses. No numeric field is recomputed or assumed. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2OriginalSaving19RowNumericsPure
open P2OriginalSaving19Geometry01Decoding
open P2OriginalSaving19Geometry01DirectDecoding
open P2OriginalSaving19Geometry01BoundedAccess

noncomputable def row : GeometryRow := geometryRowsTyped008

noncomputable def vertices : Fin 9 → QPoint :=
  ![(fun j => geometryVerticesTyped039[j.val]!),
    (fun j => geometryVerticesTyped035[j.val]!),
    (fun j => geometryVerticesTyped029[j.val]!),
    (fun j => geometryVerticesTyped028[j.val]!),
    (fun j => geometryVerticesTyped025[j.val]!),
    (fun j => geometryVerticesTyped008[j.val]!),
    (fun j => geometryVerticesTyped006[j.val]!),
    (fun j => geometryVerticesTyped002[j.val]!),
    (fun j => geometryVerticesTyped000[j.val]!)]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_INPUT before_row_binding"
  err.flush

theorem boundedRow_eq : boundedRow (8 : Fin 144) = row := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_INPUT before_vertex_binding"
  err.flush

theorem boundedRowVertex_eq : boundedRowVertex (8 : Fin 144) = vertices := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem raw_row_eq : concreteGeometry01.rows[8]! = row :=
  (row_lookup_no_fallback (8 : Fin 144)).trans boundedRow_eq

theorem raw_vertices_eq (i : Fin 9) (j : Fin 8) :
    ((concreteGeometry01.vertices[
      (concreteGeometry01.rows[8]!).vertexIds[i.val]!]!)[j.val]!) = vertices i j :=
  (raw_vertex_no_fallback (8 : Fin 144) i j).trans
    (congrFun (congrFun boundedRowVertex_eq i) j)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_INPUT bindings_complete"
  err.flush

#print axioms boundedRow_eq
#print axioms boundedRowVertex_eq
#print axioms raw_row_eq
#print axioms raw_vertices_eq

/-- The original factor and mean lookups retain the certified bounds. -/
theorem factor_maximum_no_fallback (j : Fin 10) :
    row.factorMaxima[j.val]! =
      (boundedRow (8 : Fin 144)).factorMaxima[j.val]'(factor_maximum_bound (8 : Fin 144) j) := by
  rw [← raw_row_eq]
  exact factor_maximum_lookup_no_fallback (8 : Fin 144) j

theorem weighted_mean_no_fallback (j : Fin 10) :
    row.gapWeightedMeans[j.val]! =
      (boundedRow (8 : Fin 144)).gapWeightedMeans[j.val]'(weighted_mean_bound (8 : Fin 144) j) := by
  rw [← raw_row_eq]
  exact weighted_mean_lookup_no_fallback (8 : Fin 144) j

#print axioms factor_maximum_no_fallback
#print axioms weighted_mean_no_fallback

end ImbalancedChen.P2OriginalSaving19Cell01Row008
-- END DONOR Input

-- BEGIN DONOR Determinant
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row8.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Determinant_physical_volume_positive_before"
  err.flush

theorem physical_volume_positive :
    0 < row.physicalVolume := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Determinant_volume_eq_before"
  err.flush

theorem volume_eq :
    row.physicalVolume = |(edgeOf vertices).det| / (Nat.factorial 8 : ℚ) := by
  rw [← P2Winner9FastDetPure.fastDet_eq (edgeOf vertices)]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Determinant_det_ne_before"
  err.flush

theorem det_ne :
    (edgeOf vertices).det ≠ 0 := by
  intro hzero
  have h := volume_eq
  rw [hzero, abs_zero, zero_div] at h
  exact (ne_of_gt physical_volume_positive) h

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Determinant_complete"
  err.flush

#print axioms physical_volume_positive
#print axioms volume_eq
#print axioms det_ne

end ImbalancedChen.P2OriginalSaving19Cell01Row008
-- END DONOR Determinant

-- BEGIN DONOR Physical
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row8.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Physical_all_physical_before"
  err.flush

theorem all_physical :
    ∀ i : Fin 9, PhysicalQ (vertices i) := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Physical_complete"
  err.flush

#print axioms all_physical

end ImbalancedChen.P2OriginalSaving19Cell01Row008
-- END DONOR Physical

-- BEGIN DONOR Gap
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row8.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Gap_gap_sum_positive_before"
  err.flush

theorem gap_sum_positive :
    0 < gapSumOf vertices := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Gap_mean_gap_eq_before"
  err.flush

theorem mean_gap_eq :
    row.meanGap = gapSumOf vertices / 9 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Gap_complete"
  err.flush

#print axioms gap_sum_positive
#print axioms mean_gap_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row008
-- END DONOR Gap

-- BEGIN DONOR Means
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row8.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Means_weighted_means_eq_before"
  err.flush

theorem weighted_means_eq :
    ∀ j : Fin 10, meansOf row j = computedMeanOf vertices j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Means_complete"
  err.flush

#print axioms weighted_means_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row008
-- END DONOR Means

-- BEGIN DONOR Maxima
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row8.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Maxima_factor_le_maxima_before"
  err.flush

theorem factor_le_maxima :
    ∀ i : Fin 9, ∀ j : Fin 10, factorsQ (vertices i) j ≤ topsOf row j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Maxima_factor_maxima_attained_before"
  err.flush

theorem factor_maxima_attained :
    ∀ j : Fin 10, ∃ i : Fin 9, factorsQ (vertices i) j = topsOf row j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Maxima_complete"
  err.flush

#print axioms factor_le_maxima
#print axioms factor_maxima_attained

end ImbalancedChen.P2OriginalSaving19Cell01Row008
-- END DONOR Maxima

-- BEGIN DONOR Jensen
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row8.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Jensen_jensen_eq_before"
  err.flush

theorem jensen_eq :
    row.jensenBound = oldEvaluator (massOf row) (meansOf row) := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Jensen_old_floor_eq_before"
  err.flush

theorem old_floor_eq :
    row.jensenFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) := by
  unfold oldFloorQ96
  rw [← jensen_eq]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Jensen_complete"
  err.flush

#print axioms jensen_eq
#print axioms old_floor_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row008
-- END DONOR Jensen

-- BEGIN DONOR Arithmetic
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row8.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Arithmetic_row_data_checks_before"
  err.flush

theorem row_data_checks :
    RowDataChecksFor vertices row := by
  exact ⟨det_ne, all_physical, gap_sum_positive, volume_eq, mean_gap_eq,
    weighted_means_eq, factor_le_maxima, factor_maxima_attained,
    jensen_eq, old_floor_eq⟩

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Arithmetic_bounded_row_data_checks_before"
  err.flush

theorem bounded_row_data_checks :
    RowDataChecksFor
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRowVertex (8 : Fin 144))
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (8 : Fin 144)) := by
  rw [boundedRowVertex_eq, boundedRow_eq]
  exact row_data_checks

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008 Arithmetic_complete"
  err.flush

#print axioms row_data_checks
#print axioms bounded_row_data_checks

end ImbalancedChen.P2OriginalSaving19Cell01Row008
-- END DONOR Arithmetic

-- BEGIN DONOR OldFloor
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! The actual moment row8 old floor is the actual geometry row8 Jensen
floor and the same original exact Q96 arithmetic. The ten Q80 fields and
the new Q96 field are not certified by these old-floor equalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open P2OriginalSaving19Archive
open P2OriginalSaving19Moment01Decoding
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

noncomputable def momentRow : MomentRecord :=
  momentConcrete01.rows[(8 : Fin 144).val]'(P2OriginalSaving19Moment01Shape.row_bound 8)

theorem raw_moment_row_eq : momentConcrete01.rows[8]! = momentRow :=
  P2OriginalSaving19Moment01Shape.row_lookup_no_fallback (8 : Fin 144)

theorem moment_row_eq : momentRow = momentTypedRecord008 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_OLD_FLOOR before_original_moment_geometry_binding"
  err.flush

theorem moment_old_matches_geometry : momentRow.oldFloorQ96 = row.jensenFloorQ96 := by
  decide +kernel

theorem moment_old_eq_evaluator :
    momentRow.oldFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) :=
  moment_old_matches_geometry.trans old_floor_eq

theorem actual_moment_old_eq_bounded_evaluator :
    (momentConcrete01.rows[8]!).oldFloorQ96 =
      oldFloorQ96
        (massOf (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (8 : Fin 144)))
        (meansOf (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (8 : Fin 144))) := by
  rw [raw_moment_row_eq, boundedRow_eq]
  exact moment_old_eq_evaluator

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_OLD_FLOOR complete"
  err.flush

#print axioms raw_moment_row_eq
#print axioms moment_row_eq
#print axioms moment_old_matches_geometry
#print axioms moment_old_eq_evaluator
#print axioms actual_moment_old_eq_bounded_evaluator

/-- The saved ten Q80 fields are accessed at their true bounded indices. -/
theorem moment_floor_bound (j : Fin 10) : j.val < momentRow.factorFloorsQ80.size := by
  have hs : momentRow.factorFloorsQ80.size = 10 :=
    (P2OriginalSaving19Moment01Shape.row_ids_and_floor_sizes_bounded (8 : Fin 144)).2
  rw [hs]
  exact j.isLt

theorem moment_floor_lookup_no_fallback (j : Fin 10) :
    momentRow.factorFloorsQ80[j.val]! =
      momentRow.factorFloorsQ80[j.val]'(moment_floor_bound j) :=
  getElem!_pos momentRow.factorFloorsQ80 j.val (moment_floor_bound j)

#print axioms moment_floor_bound
#print axioms moment_floor_lookup_no_fallback

end ImbalancedChen.P2OriginalSaving19Cell01Row008
-- END DONOR OldFloor

-- BEGIN DONOR MomentEncoding
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact nonnegative integer encodings of the actual nine ordered vertices.
The existing prefix evaluator is used unchanged. Host-generated literals
are connected to the decoded row by closed Lean equalities below. No
saved field, moment value or final floor is an assumption. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row008
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

def gapScale : Nat := 98000000

def gapNats : Fin 9 → Nat := ![0, 0, 0, 0, 0, 0, 0, 515533, 0]

def deviationDenominators : Fin 10 → Nat := ![443105277160, 443105277160, 11693988600, 582839508160, 143321575488, 405474973540, 173772236820, 148833972000, 508792742640, 501616952928]

def deviationNats : Fin 10 → Fin 9 → Nat :=
  ![![63292192600, 225697350424, 101354296225, 101354296225, 75719810920, 35363862520, 60424591864, 52543123360, 0],
    ![63292192600, 225697350424, 101354296225, 101354296225, 75719810920, 35363862520, 60424591864, 30024641920, 0],
    ![0, 669252024, 1254841665, 1254841665, 1434103800, 1863422400, 1921166016, 2162435460, 2368648660],
    ![0, 81202578912, 63439693135, 63439693135, 82859757760, 122357068960, 117506605216, 97239971920, 164795416240],
    ![34801105248, 0, 7612665333, 7612665333, 9943073088, 36560826288, 34597543344, 26394382248, 27466690888],
    ![215547028060, 154645093876, 101356436545, 101356436545, 122330106340, 88413936940, 88009731628, 86320845520, 0],
    ![65251766580, 30450661332, 0, 38063326665, 40393734420, 24938264820, 28402881780, 42879048420, 47168282980],
    ![40313501760, 5512396512, 51188388510, 13125061845, 15455469600, 0, 3464616960, 17940783600, 22230018160],
    ![128971096800, 7167228432, 167041761705, 167041761705, 141407276400, 101051328000, 0, 50666583240, 65678904200],
    ![121803868368, 0, 159865971993, 159865971993, 134231486688, 93875538288, 118936267632, 88536317688, 58511675768]]

def prefixMoment (j : Fin 10) (k : Nat) : ℚ :=
  normalizedMoment gapNats (deviationNats j) (deviationDenominators j) k

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT gap_encoding_before"
  err.flush

theorem gapScale_ne : gapScale ≠ 0 := by decide +kernel

theorem gap_encoding : ∀ i : Fin 9,
    gapQ (vertices i) = (gapNats i : ℚ) / (gapScale : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT deviation_encoding_before"
  err.flush

theorem deviationDenominators_ne : ∀ j : Fin 10, deviationDenominators j ≠ 0 := by
  decide +kernel

theorem deviation_encoding : ∀ (j : Fin 10) (i : Fin 9),
    1 - factorsQ (vertices i) j / topsOf row j =
      (deviationNats j i : ℚ) / (deviationDenominators j : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT encoding_complete"
  err.flush

#print axioms gapScale_ne
#print axioms gap_encoding
#print axioms deviationDenominators_ne
#print axioms deviation_encoding

end ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor
-- END DONOR MomentEncoding

-- BEGIN DONOR MomentFactor00
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row008
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor00_moment1_before"
  err.flush

theorem factor00_moment1 : prefixMoment (0 : Fin 10) 1 = (384146323749 : ℚ) / 2215526385800 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor00_moment2_before"
  err.flush

theorem factor00_moment2 : prefixMoment (0 : Fin 10) 2 = (340960479011709437135763 : ℚ) / 10798825765587222971608000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor00_moment3_before"
  err.flush

theorem factor00_moment3 : prefixMoment (0 : Fin 10) 3 = (28932608220526650954862800165961479 : ℚ) / 4785016683863075624989081650873280000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor00_moment4_before"
  err.flush

theorem factor00_moment4 : prefixMoment (0 : Fin 10) 4 = (6721771636360972936035552166510337193963708513 : ℚ) / 5512691974187767783182150841898595235139540480000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor00_moment5_before"
  err.flush

theorem factor00_moment5 : prefixMoment (0 : Fin 10) 5 = (4431016886083738087616733615430088405407857137296729289847 : ℚ) / 17098920335841248866140520148950830675968130189658076057600000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor00_moment6_before"
  err.flush

theorem factor00_moment6 : prefixMoment (0 : Fin 10) 6 = (2198804465561206950292013364747246468319365983292399370498962016132407 : ℚ) / 37883109172748484302958654600537111549435442395077025785676040622080000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor00_first_moment_before"
  err.flush

theorem factor00_first_moment :
    prefixMoment (0 : Fin 10) 1 = 1 - meansOf row (0 : Fin 10) / topsOf row (0 : Fin 10) := by
  rw [factor00_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor00_gap_before"
  err.flush

theorem factor00_gap_value :
    gapEvaluator (prefixMoment (0 : Fin 10)) = (12243470426368223156901384549698874400211741210362833305174217982722256649 : ℚ) / 10762246924076273949704163238788952144725977953146882325476147904000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor00_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor00_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor00_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor
-- END DONOR MomentFactor00

-- BEGIN DONOR MomentFactor01
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row008
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor01_moment1_before"
  err.flush

theorem factor01_moment1 : prefixMoment (1 : Fin 10) 1 = (361627842309 : ℚ) / 2215526385800 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor01_moment2_before"
  err.flush

theorem factor01_moment2 : prefixMoment (1 : Fin 10) 2 = (305513774888092378805523 : ℚ) / 10798825765587222971608000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor01_moment3_before"
  err.flush

theorem factor01_moment3 : prefixMoment (1 : Fin 10) 3 = (24928786544896571734722834726268119 : ℚ) / 4785016683863075624989081650873280000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor01_moment4_before"
  err.flush

theorem factor01_moment4 : prefixMoment (1 : Fin 10) 4 = (5620181398528770867484148263131295502492422497 : ℚ) / 5512691974187767783182150841898595235139540480000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor01_moment5_before"
  err.flush

theorem factor01_moment5 : prefixMoment (1 : Fin 10) 5 = (3623629734886602959664834617753473777968912310240071116247 : ℚ) / 17098920335841248866140520148950830675968130189658076057600000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor01_moment6_before"
  err.flush

theorem factor01_moment6 : prefixMoment (1 : Fin 10) 6 = (1770173615312683201224161294266360710072443088278702367434553784245687 : ℚ) / 37883109172748484302958654600537111549435442395077025785676040622080000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor01_first_moment_before"
  err.flush

theorem factor01_first_moment :
    prefixMoment (1 : Fin 10) 1 = 1 - meansOf row (1 : Fin 10) / topsOf row (1 : Fin 10) := by
  rw [factor01_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor01_gap_before"
  err.flush

theorem factor01_gap_value :
    gapEvaluator (prefixMoment (1 : Fin 10)) = (143589798426239552803479468676650114042726257753193484437626290543505749699 : ℚ) / 118384716164839013446745795626678473591985757484615705580237626944000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor01_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor01_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor01_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor
-- END DONOR MomentFactor01

-- BEGIN DONOR MomentFactor02
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row008
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor02_moment1_before"
  err.flush

theorem factor02_moment1 : prefixMoment (2 : Fin 10) 1 = (301822943 : ℚ) / 2338797720 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor02_moment2_before"
  err.flush

theorem factor02_moment2 : prefixMoment (2 : Fin 10) 2 = (127761251052950647291 : ℚ) / 7521215315731147800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor02_moment3_before"
  err.flush

theorem factor02_moment3 : prefixMoment (2 : Fin 10) 3 = (20013064890604661910521989801 : ℚ) / 8795300616030544303811508000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor02_moment4_before"
  err.flush

theorem factor02_moment4 : prefixMoment (2 : Fin 10) 4 = (4139834467340957711911649477763570448981 : ℚ) / 13370778867866441104273672443105144000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor02_moment5_before"
  err.flush

theorem factor02_moment5 : prefixMoment (2 : Fin 10) 5 = (267262537127361318725928041910299750390352114859 : ℚ) / 6254309426158042743837909473192228101494336000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor02_moment6_before"
  err.flush

theorem factor02_moment6 : prefixMoment (2 : Fin 10) 6 = (10924670539170754995674175624761094503690994663173716278553 : ℚ) / 1828445578259117341118830840683548025686860203714240000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor02_first_moment_before"
  err.flush

theorem factor02_first_moment :
    prefixMoment (2 : Fin 10) 1 = 1 - meansOf row (2 : Fin 10) / topsOf row (2 : Fin 10) := by
  rw [factor02_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor02_gap_before"
  err.flush

theorem factor02_gap_value :
    gapEvaluator (prefixMoment (2 : Fin 10)) = (30680102045790656363929876711403357877703343190982499688701 : ℚ) / 140649659866085949316833141591042155822066169516480000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor02_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor02_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor02_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor
-- END DONOR MomentFactor02

-- BEGIN DONOR MomentFactor03
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row008
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor03_moment1_before"
  err.flush

theorem factor03_moment1 : prefixMoment (3 : Fin 10) 1 = (445040378599 : ℚ) / 2914197540800 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor03_moment2_before"
  err.flush

theorem factor03_moment2 : prefixMoment (3 : Fin 10) 2 = (444300175013943567493827 : ℚ) / 18683604074970488862208000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor03_moment3_before"
  err.flush

theorem factor03_moment3 : prefixMoment (3 : Fin 10) 3 = (8210197792968887224483791599705847 : ℚ) / 2177908521942394298992813746323456000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor03_moment4_before"
  err.flush

theorem factor03_moment4 : prefixMoment (3 : Fin 10) 4 = (50138145608780444708676315034034896335130637061 : ℚ) / 82509123563514547970054370573307256715241062400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor03_moment5_before"
  err.flush

theorem factor03_moment5 : prefixMoment (3 : Fin 10) 5 = (6699946834980306470288753894310360283792014981881708154789 : ℚ) / 67325407795060079923819702054766690219857941179072616857600000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor03_moment6_before"
  err.flush

theorem factor03_moment6 : prefixMoment (3 : Fin 10) 6 = (295126702672047925646053370133615460707159335166771333973266743473077 : ℚ) / 17836321620883748663840620642780890505133220319036770224639867617280000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor03_first_moment_before"
  err.flush

theorem factor03_first_moment :
    prefixMoment (3 : Fin 10) 1 = 1 - meansOf row (3 : Fin 10) / topsOf row (3 : Fin 10) := by
  rw [factor03_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor03_gap_before"
  err.flush

theorem factor03_gap_value :
    gapEvaluator (prefixMoment (3 : Fin 10)) = (585867020228709194161534973334081958962778025720592782288423249186332630717 : ℚ) / 1839370667153636580958564003786779333341863345400666929415986348032000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor03_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor03_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor03_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor
-- END DONOR MomentFactor03

-- BEGIN DONOR MomentFactor04
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row008
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor04_moment1_before"
  err.flush

theorem factor04_moment1 : prefixMoment (4 : Fin 10) 1 = (105691667009 : ℚ) / 716607877440 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor04_moment2_before"
  err.flush

theorem factor04_moment2 : prefixMoment (4 : Fin 10) 2 = (25395115418785423440091 : ℚ) / 1129759070019936534097920 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor04_moment3_before"
  err.flush

theorem factor04_moment3 : prefixMoment (4 : Fin 10) 3 = (570906975418708491616968220086511 : ℚ) / 161918849837115011636684127263784960 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor04_moment4_before"
  err.flush

theorem factor04_moment4 : prefixMoment (4 : Fin 10) 4 = (171150430851460335943411150220223441186310741 : ℚ) / 301684040578182803377525293483423415432107786240 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor04_moment5_before"
  err.flush

theorem factor04_moment5 : prefixMoment (4 : Fin 10) 5 = (5652277006806095603752021579297374327190200662811560555 : ℚ) / 60532964793351234548189633797659352916127468314368218759168 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor04_moment6_before"
  err.flush

theorem factor04_moment6 : prefixMoment (4 : Fin 10) 6 = (680366742135031385453299027808237790869352443176218010124267700079 : ℚ) / 43378399415713676413981770870351555333389979413240263899600971020369920 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor04_first_moment_before"
  err.flush

theorem factor04_first_moment :
    prefixMoment (4 : Fin 10) 1 = 1 - meansOf row (4 : Fin 10) / topsOf row (4 : Fin 10) := by
  rw [factor04_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor04_gap_before"
  err.flush

theorem factor04_gap_value :
    gapEvaluator (prefixMoment (4 : Fin 10)) = (681478136627431817694980211750517521037314829966795051981391458291873 : ℚ) / 1369267658324295341350434686564127377947916016832079037234879135744000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor04_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor04_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor04_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor
-- END DONOR MomentFactor04

-- BEGIN DONOR MomentFactor05
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row008
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor05_moment1_before"
  err.flush

theorem factor05_moment1 : prefixMoment (5 : Fin 10) 1 = (522150230487 : ℚ) / 2027374867700 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor05_moment2_before"
  err.flush

theorem factor05_moment2 : prefixMoment (5 : Fin 10) 2 = (613457651190159698300043 : ℚ) / 9042547479199503507238000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor05_moment3_before"
  err.flush

theorem factor05_moment3 : prefixMoment (5 : Fin 10) 3 = (267770515417021751985237009844521 : ℚ) / 14666106799450449539913860993930080 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor05_moment4_before"
  err.flush

theorem factor05_moment4 : prefixMoment (5 : Fin 10) 4 = (96965102706380398555347271114584525132120471621 : ℚ) / 19326902615936451619647453371277371187982770400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor05_moment5_before"
  err.flush

theorem factor05_moment5 : prefixMoment (5 : Fin 10) 5 = (15438675015320160627212716789774380447285583871724451957617 : ℚ) / 10971205457529785303917257819785906229827301071482253302400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor05_moment6_before"
  err.flush

theorem factor05_moment6 : prefixMoment (5 : Fin 10) 6 = (8959052748395113834358511985322233398624090922800603247027208783309823 : ℚ) / 22242746212968966449338654864135242085020730303644401531851088092480000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor05_first_moment_before"
  err.flush

theorem factor05_first_moment :
    prefixMoment (5 : Fin 10) 1 = 1 - meansOf row (5 : Fin 10) / topsOf row (5 : Fin 10) := by
  rw [factor05_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor05_gap_before"
  err.flush

theorem factor05_gap_value :
    gapEvaluator (prefixMoment (5 : Fin 10)) = (95473631625864755667176605115424618880910998970373451009926023864680289731 : ℚ) / 69508581915528020154183296450422631515689782198888754787034650289000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor05_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor05_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor05_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor
-- END DONOR MomentFactor05

-- BEGIN DONOR MomentFactor06
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row008
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor06_moment1_before"
  err.flush

theorem factor06_moment1 : prefixMoment (6 : Fin 10) 1 = (51489573631 : ℚ) / 248246052600 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor06_moment2_before"
  err.flush

theorem factor06_moment2 : prefixMoment (6 : Fin 10) 2 = (72751926564352592813569 : ℚ) / 1660823465918439004182000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor06_moment3_before"
  err.flush

theorem factor06_moment3 : prefixMoment (6 : Fin 10) 3 = (10857072891699129756502804479289033 : ℚ) / 1154420034543168725757757897524960000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor06_moment4_before"
  err.flush

theorem factor06_moment4 : prefixMoment (6 : Fin 10) 4 = (1336696102932568330550166192235176502808080081 : ℚ) / 651969992805261313058182902793031083188338400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor06_moment5_before"
  err.flush

theorem factor06_moment5 : prefixMoment (6 : Fin 10) 5 = (143837765584466824960409015873298500786557403853481781017 : ℚ) / 317223995170010782097246009904471783133590171099879686400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor06_moment6_before"
  err.flush

theorem factor06_moment6 : prefixMoment (6 : Fin 10) 6 = (14010526693814822434310673337095812587066276274456492457251736612769 : ℚ) / 137811808034174124471390124757299840689244782272981531846520333120000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor06_first_moment_before"
  err.flush

theorem factor06_first_moment :
    prefixMoment (6 : Fin 10) 1 = 1 - meansOf row (6 : Fin 10) / topsOf row (6 : Fin 10) := by
  rw [factor06_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor06_gap_before"
  err.flush

theorem factor06_gap_value :
    gapEvaluator (prefixMoment (6 : Fin 10)) = (34190956768986419783900463450918370232095239543882076997944245477585489917 : ℚ) / 55124723213669649788556049902919936275697912909192612738608133248000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor06_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor06_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor06_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor
-- END DONOR MomentFactor06

-- BEGIN DONOR MomentFactor07
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row008
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor07_moment1_before"
  err.flush

theorem factor07_moment1 : prefixMoment (7 : Fin 10) 1 = (26738717221 : ℚ) / 212619960000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor07_moment2_before"
  err.flush

theorem factor07_moment2 : prefixMoment (7 : Fin 10) 2 = (20434933244872167687139 : ℚ) / 1218335317171323120000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor07_moment3_before"
  err.flush

theorem factor07_moment3 : prefixMoment (7 : Fin 10) 3 = (1715220354369094494927527458267543 : ℚ) / 725318737929951297780130560000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor07_moment4_before"
  err.flush

theorem factor07_moment4 : prefixMoment (7 : Fin 10) 4 = (123275108479754813378657411536360060659811891 : ℚ) / 350844223379460555599307745250999040000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor07_moment5_before"
  err.flush

theorem factor07_moment5 : prefixMoment (7 : Fin 10) 5 = (616920824841571488083401296265230931061301902292275659 : ℚ) / 11246854622515158275390851853307454419683328000000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor07_moment6_before"
  err.flush

theorem factor07_moment6 : prefixMoment (7 : Fin 10) 6 = (37535149632167445437349109894927316422458718816903330688150335783 : ℚ) / 4184785114938729090837725834478274446226061721047040000000000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor07_first_moment_before"
  err.flush

theorem factor07_first_moment :
    prefixMoment (7 : Fin 10) 1 = 1 - meansOf row (7 : Fin 10) / topsOf row (7 : Fin 10) := by
  rw [factor07_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor07_gap_before"
  err.flush

theorem factor07_gap_value :
    gapEvaluator (prefixMoment (7 : Fin 10)) = (139571134685588700131555985964093232444370074839699925679115487065208743 : ℚ) / 219806894926074659316729033730171991114904252014592000000000000000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor07_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor07_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor07_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor
-- END DONOR MomentFactor07

-- BEGIN DONOR MomentFactor08
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row008
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor08_moment1_before"
  err.flush

theorem factor08_moment1 : prefixMoment (8 : Fin 10) 1 = (439846261861 : ℚ) / 2543963713200 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor08_moment2_before"
  err.flush

theorem factor08_moment2 : prefixMoment (8 : Fin 10) 2 = (443002531026683518780579 : ℚ) / 14237853022972330079328000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor08_moment3_before"
  err.flush

theorem factor08_moment3 : prefixMoment (8 : Fin 10) 3 = (42019213445383806234420786232921907 : ℚ) / 7244116288863306745892661888145920000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor08_moment4_before"
  err.flush

theorem factor08_moment4 : prefixMoment (8 : Fin 10) 4 = (53466950739135593501338158700779747291686652421 : ℚ) / 47914799329980184254930432962559526037238374400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor08_moment5_before"
  err.flush

theorem factor08_moment5 : prefixMoment (8 : Fin 10) 5 = (7536368013340897460441103500092389905904396389530085426311 : ℚ) / 34130183029804193253486039901192650361443004595403630182400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor08_moment6_before"
  err.flush

theorem factor08_moment6 : prefixMoment (8 : Fin 10) 6 = (3891805744537229111338738020606583722151446512466648204242835601383079 : ℚ) / 86825947152696301738068734911401415922045868080687682691577897287680000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor08_first_moment_before"
  err.flush

theorem factor08_first_moment :
    prefixMoment (8 : Fin 10) 1 = 1 - meansOf row (8 : Fin 10) / topsOf row (8 : Fin 10) := by
  rw [factor08_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor08_gap_before"
  err.flush

theorem factor08_gap_value :
    gapEvaluator (prefixMoment (8 : Fin 10)) = (242249884982553007577388718724571543293231869525999979965537013641985577979 : ℚ) / 271331084852175942931464796598129424756393337752149008411180929024000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor08_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor08_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor08_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor
-- END DONOR MomentFactor08

-- BEGIN DONOR MomentFactor09
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row008
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor09_moment1_before"
  err.flush

theorem factor09_moment1 : prefixMoment (9 : Fin 10) 1 = (512081708053 : ℚ) / 2508084764640 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor09_moment2_before"
  err.flush

theorem factor09_moment2 : prefixMoment (9 : Fin 10) 2 = (587469331504048889879491 : ℚ) / 13839076210562425227525120 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor09_moment3_before"
  err.flush

theorem factor09_moment3 : prefixMoment (9 : Fin 10) 3 = (62269419416603860385773869320449763 : ℚ) / 6941915240080696671760987808977551360 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor09_moment4_before"
  err.flush

theorem factor09_moment4 : prefixMoment (9 : Fin 10) 4 = (87072768052698346828210943765148295747513062469 : ℚ) / 45268370812778420337162309952354765072651690967040 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor09_moment5_before"
  err.flush

theorem factor09_moment5 : prefixMoment (9 : Fin 10) 5 = (13289797724357897336456182773000793306576766036069878654807 : ℚ) / 31790335123569010765224762048652520559886750475134629071290368 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor09_moment6_before"
  err.flush

theorem factor09_moment6 : prefixMoment (9 : Fin 10) 6 = (7335074127086754393417482677172207394521853379703672133670578862558087 : ℚ) / 79732855186223307681896373619494661257586321590482444326581004406378987520 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor09_first_moment_before"
  err.flush

theorem factor09_first_moment :
    prefixMoment (9 : Fin 10) 1 = 1 - meansOf row (9 : Fin 10) / topsOf row (9 : Fin 10) := by
  rw [factor09_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor09_gap_before"
  err.flush

theorem factor09_gap_value :
    gapEvaluator (prefixMoment (9 : Fin 10)) = (148782719606032611336040170071397639300835321030595506172984735562753683387 : ℚ) / 249165172456947836505926167560920816429957254970257638520565638769934336000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor09_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor09_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW008_MOMENT factor09_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor
-- END DONOR MomentFactor09

-- BEGIN DONOR PrefixFloorChecks
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! All five original floor obligations for the actual cell01 row8, expressed
through the existing finite prefix evaluator. The old two equalities are
reused. Both Q80 bounds remain explicit, and the saved new field is the
maximum of the exact old and new Q96 evaluations. The separate bridge to
the original rationalMoment still requires its own acceptance. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row008
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_FLOOR first_moments_before"
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
  err.putStrLn "P26_CELL01_ROW008_FLOOR total_Q80_before"
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
    totalLowerQ80 prefixMoment = (9071292103859174540300 : ℚ) / (2 : ℚ)^80 := by
  have h : (∑ j : Fin 10, momentRow.factorFloorsQ80[j.val]! : ℤ) = 9071292103859174540300 := by
    decide +kernel
  rw [total_Q80_eq_saved, h]
  norm_num

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW008_FLOOR new_Q96_before"
  err.flush

theorem new_Q96_value :
    newFloorQ96 (massOf row) (meansOf row) prefixMoment = 7126303629670592339 := by
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
  err.putStrLn "P26_CELL01_ROW008_FLOOR complete"
  err.flush

#print axioms all_first_moments
#print axioms all_saved_Q80
#print axioms all_Q80_bounds
#print axioms total_Q80_eq_saved
#print axioms total_Q80_value
#print axioms new_Q96_value
#print axioms saved_new_Q96_max
#print axioms prefix_floor_checks

end ImbalancedChen.P2OriginalSaving19Cell01Row008MomentFloor
-- END DONOR PrefixFloorChecks
