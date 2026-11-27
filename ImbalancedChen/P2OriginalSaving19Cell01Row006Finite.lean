import ImbalancedChen.P2OriginalSaving19Geometry01BoundedAccess
import ImbalancedChen.P2OriginalSaving19RowNumericsPure
import Mathlib.Tactic.FinCases
import ImbalancedChen.P2Winner9FastDetPure
import ImbalancedChen.P2OriginalSaving19Moment01Shape
import ImbalancedChen.P2OriginalSaving19PrefixMoments
import Mathlib.Algebra.BigOperators.Field

/-! SOURCE CANDIDATE: original Cell01 row 6 only.
Twenty-one accepted row000 source bodies are merged into one new owner.
Original ordinal, vertex order and decoded row/record identities are retained.
All host-produced literals remain closed Lean proof obligations. This owner
has not been compiled, independently replayed or audited. No integral or
OriginalFloorBridge claim is included. The shared bounded-access owner is
imported unchanged. -/

-- BEGIN DONOR Input
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! The actual original row 6 and its original nine ordered vertices. The small
selectors refer to the already decoded values, with closed equalities to
the original bounded accesses. No numeric field is recomputed or assumed. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2OriginalSaving19RowNumericsPure
open P2OriginalSaving19Geometry01Decoding
open P2OriginalSaving19Geometry01DirectDecoding
open P2OriginalSaving19Geometry01BoundedAccess

noncomputable def row : GeometryRow := geometryRowsTyped006

noncomputable def vertices : Fin 9 → QPoint :=
  ![(fun j => geometryVerticesTyped039[j.val]!),
    (fun j => geometryVerticesTyped035[j.val]!),
    (fun j => geometryVerticesTyped029[j.val]!),
    (fun j => geometryVerticesTyped028[j.val]!),
    (fun j => geometryVerticesTyped025[j.val]!),
    (fun j => geometryVerticesTyped008[j.val]!),
    (fun j => geometryVerticesTyped003[j.val]!),
    (fun j => geometryVerticesTyped001[j.val]!),
    (fun j => geometryVerticesTyped000[j.val]!)]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_INPUT before_row_binding"
  err.flush

theorem boundedRow_eq : boundedRow (6 : Fin 144) = row := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_INPUT before_vertex_binding"
  err.flush

theorem boundedRowVertex_eq : boundedRowVertex (6 : Fin 144) = vertices := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem raw_row_eq : concreteGeometry01.rows[6]! = row :=
  (row_lookup_no_fallback (6 : Fin 144)).trans boundedRow_eq

theorem raw_vertices_eq (i : Fin 9) (j : Fin 8) :
    ((concreteGeometry01.vertices[
      (concreteGeometry01.rows[6]!).vertexIds[i.val]!]!)[j.val]!) = vertices i j :=
  (raw_vertex_no_fallback (6 : Fin 144) i j).trans
    (congrFun (congrFun boundedRowVertex_eq i) j)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_INPUT bindings_complete"
  err.flush

#print axioms boundedRow_eq
#print axioms boundedRowVertex_eq
#print axioms raw_row_eq
#print axioms raw_vertices_eq

/-- The original factor and mean lookups retain the certified bounds. -/
theorem factor_maximum_no_fallback (j : Fin 10) :
    row.factorMaxima[j.val]! =
      (boundedRow (6 : Fin 144)).factorMaxima[j.val]'(factor_maximum_bound (6 : Fin 144) j) := by
  rw [← raw_row_eq]
  exact factor_maximum_lookup_no_fallback (6 : Fin 144) j

theorem weighted_mean_no_fallback (j : Fin 10) :
    row.gapWeightedMeans[j.val]! =
      (boundedRow (6 : Fin 144)).gapWeightedMeans[j.val]'(weighted_mean_bound (6 : Fin 144) j) := by
  rw [← raw_row_eq]
  exact weighted_mean_lookup_no_fallback (6 : Fin 144) j

#print axioms factor_maximum_no_fallback
#print axioms weighted_mean_no_fallback

end ImbalancedChen.P2OriginalSaving19Cell01Row006
-- END DONOR Input

-- BEGIN DONOR Determinant
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row6.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Determinant_physical_volume_positive_before"
  err.flush

theorem physical_volume_positive :
    0 < row.physicalVolume := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Determinant_volume_eq_before"
  err.flush

theorem volume_eq :
    row.physicalVolume = |(edgeOf vertices).det| / (Nat.factorial 8 : ℚ) := by
  rw [← P2Winner9FastDetPure.fastDet_eq (edgeOf vertices)]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Determinant_det_ne_before"
  err.flush

theorem det_ne :
    (edgeOf vertices).det ≠ 0 := by
  intro hzero
  have h := volume_eq
  rw [hzero, abs_zero, zero_div] at h
  exact (ne_of_gt physical_volume_positive) h

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Determinant_complete"
  err.flush

#print axioms physical_volume_positive
#print axioms volume_eq
#print axioms det_ne

end ImbalancedChen.P2OriginalSaving19Cell01Row006
-- END DONOR Determinant

-- BEGIN DONOR Physical
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row6.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Physical_all_physical_before"
  err.flush

theorem all_physical :
    ∀ i : Fin 9, PhysicalQ (vertices i) := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Physical_complete"
  err.flush

#print axioms all_physical

end ImbalancedChen.P2OriginalSaving19Cell01Row006
-- END DONOR Physical

-- BEGIN DONOR Gap
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row6.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Gap_gap_sum_positive_before"
  err.flush

theorem gap_sum_positive :
    0 < gapSumOf vertices := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Gap_mean_gap_eq_before"
  err.flush

theorem mean_gap_eq :
    row.meanGap = gapSumOf vertices / 9 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Gap_complete"
  err.flush

#print axioms gap_sum_positive
#print axioms mean_gap_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row006
-- END DONOR Gap

-- BEGIN DONOR Means
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row6.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Means_weighted_means_eq_before"
  err.flush

theorem weighted_means_eq :
    ∀ j : Fin 10, meansOf row j = computedMeanOf vertices j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Means_complete"
  err.flush

#print axioms weighted_means_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row006
-- END DONOR Means

-- BEGIN DONOR Maxima
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row6.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Maxima_factor_le_maxima_before"
  err.flush

theorem factor_le_maxima :
    ∀ i : Fin 9, ∀ j : Fin 10, factorsQ (vertices i) j ≤ topsOf row j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Maxima_factor_maxima_attained_before"
  err.flush

theorem factor_maxima_attained :
    ∀ j : Fin 10, ∃ i : Fin 9, factorsQ (vertices i) j = topsOf row j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Maxima_complete"
  err.flush

#print axioms factor_le_maxima
#print axioms factor_maxima_attained

end ImbalancedChen.P2OriginalSaving19Cell01Row006
-- END DONOR Maxima

-- BEGIN DONOR Jensen
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row6.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Jensen_jensen_eq_before"
  err.flush

theorem jensen_eq :
    row.jensenBound = oldEvaluator (massOf row) (meansOf row) := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Jensen_old_floor_eq_before"
  err.flush

theorem old_floor_eq :
    row.jensenFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) := by
  unfold oldFloorQ96
  rw [← jensen_eq]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Jensen_complete"
  err.flush

#print axioms jensen_eq
#print axioms old_floor_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row006
-- END DONOR Jensen

-- BEGIN DONOR Arithmetic
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row6.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Arithmetic_row_data_checks_before"
  err.flush

theorem row_data_checks :
    RowDataChecksFor vertices row := by
  exact ⟨det_ne, all_physical, gap_sum_positive, volume_eq, mean_gap_eq,
    weighted_means_eq, factor_le_maxima, factor_maxima_attained,
    jensen_eq, old_floor_eq⟩

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Arithmetic_bounded_row_data_checks_before"
  err.flush

theorem bounded_row_data_checks :
    RowDataChecksFor
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRowVertex (6 : Fin 144))
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (6 : Fin 144)) := by
  rw [boundedRowVertex_eq, boundedRow_eq]
  exact row_data_checks

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006 Arithmetic_complete"
  err.flush

#print axioms row_data_checks
#print axioms bounded_row_data_checks

end ImbalancedChen.P2OriginalSaving19Cell01Row006
-- END DONOR Arithmetic

-- BEGIN DONOR OldFloor
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! The actual moment row6 old floor is the actual geometry row6 Jensen
floor and the same original exact Q96 arithmetic. The ten Q80 fields and
the new Q96 field are not certified by these old-floor equalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open P2OriginalSaving19Archive
open P2OriginalSaving19Moment01Decoding
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

noncomputable def momentRow : MomentRecord :=
  momentConcrete01.rows[(6 : Fin 144).val]'(P2OriginalSaving19Moment01Shape.row_bound 6)

theorem raw_moment_row_eq : momentConcrete01.rows[6]! = momentRow :=
  P2OriginalSaving19Moment01Shape.row_lookup_no_fallback (6 : Fin 144)

theorem moment_row_eq : momentRow = momentTypedRecord006 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_OLD_FLOOR before_original_moment_geometry_binding"
  err.flush

theorem moment_old_matches_geometry : momentRow.oldFloorQ96 = row.jensenFloorQ96 := by
  decide +kernel

theorem moment_old_eq_evaluator :
    momentRow.oldFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) :=
  moment_old_matches_geometry.trans old_floor_eq

theorem actual_moment_old_eq_bounded_evaluator :
    (momentConcrete01.rows[6]!).oldFloorQ96 =
      oldFloorQ96
        (massOf (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (6 : Fin 144)))
        (meansOf (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (6 : Fin 144))) := by
  rw [raw_moment_row_eq, boundedRow_eq]
  exact moment_old_eq_evaluator

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_OLD_FLOOR complete"
  err.flush

#print axioms raw_moment_row_eq
#print axioms moment_row_eq
#print axioms moment_old_matches_geometry
#print axioms moment_old_eq_evaluator
#print axioms actual_moment_old_eq_bounded_evaluator

/-- The saved ten Q80 fields are accessed at their true bounded indices. -/
theorem moment_floor_bound (j : Fin 10) : j.val < momentRow.factorFloorsQ80.size := by
  have hs : momentRow.factorFloorsQ80.size = 10 :=
    (P2OriginalSaving19Moment01Shape.row_ids_and_floor_sizes_bounded (6 : Fin 144)).2
  rw [hs]
  exact j.isLt

theorem moment_floor_lookup_no_fallback (j : Fin 10) :
    momentRow.factorFloorsQ80[j.val]! =
      momentRow.factorFloorsQ80[j.val]'(moment_floor_bound j) :=
  getElem!_pos momentRow.factorFloorsQ80 j.val (moment_floor_bound j)

#print axioms moment_floor_bound
#print axioms moment_floor_lookup_no_fallback

end ImbalancedChen.P2OriginalSaving19Cell01Row006
-- END DONOR OldFloor

-- BEGIN DONOR MomentEncoding
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact nonnegative integer encodings of the actual nine ordered vertices.
The existing prefix evaluator is used unchanged. Host-generated literals
are connected to the decoded row by closed Lean equalities below. No
saved field, moment value or final floor is an assumption. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row006
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

def gapScale : Nat := 34000000

def gapNats : Fin 9 → Nat := ![0, 0, 0, 0, 0, 0, 171843, 0, 0]

def deviationDenominators : Fin 10 → Nat := ![7532813968680, 7532813968680, 198797806200, 9908271638720, 143321575488, 6893074550180, 2954128025940, 2530177524000, 8527633741536, 8527488199776]

def deviationNats : Fin 10 → Fin 9 → Nat :=
  ![![1075991531160, 3836879214168, 1723047292785, 1723047292785, 1287261042600, 601209919800, 735598019520, 0, 24256960],
    ![1075991531160, 3836879214168, 1723047292785, 1723047292785, 1287261042600, 601209919800, 367799009760, 0, 24256960],
    ![0, 11377284408, 21332308305, 21332308305, 24379764600, 31678180800, 36225146580, 40266893940, 40267027220],
    ![0, 1380443841504, 1078474783295, 1078474783295, 1408615881920, 2080070172320, 1698125046800, 2801522076080, 2801522076080],
    ![34801105248, 0, 7612665333, 7612665333, 9943073088, 36560826288, 27466894728, 27466894728, 27466690888],
    ![3664299477020, 2628966595892, 1723059421265, 1723059421265, 2079611807780, 1503036927980, 1471208167520, 12128480, 0],
    ![1109280031860, 517661242644, 0, 647076553305, 686693485140, 423950501940, 696768448740, 801853880100, 801860810660],
    ![685329529920, 93710740704, 870202604670, 223126051365, 262742983200, 0, 272817946800, 377903378160, 377910308720],
    ![2070665762256, 0, 2717867065641, 2717867065641, 2282080815456, 1596029692656, 1362618782616, 994819772856, 994698488056],
    ![2070665762256, 0, 2717721523881, 2717721523881, 2281935273696, 1595884150896, 1362473240856, 994674231096, 994698488056]]

def prefixMoment (j : Fin 10) (k : Nat) : ℚ :=
  normalizedMoment gapNats (deviationNats j) (deviationDenominators j) k

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT gap_encoding_before"
  err.flush

theorem gapScale_ne : gapScale ≠ 0 := by decide +kernel

theorem gap_encoding : ∀ i : Fin 9,
    gapQ (vertices i) = (gapNats i : ℚ) / (gapScale : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT deviation_encoding_before"
  err.flush

theorem deviationDenominators_ne : ∀ j : Fin 10, deviationDenominators j ≠ 0 := by
  decide +kernel

theorem deviation_encoding : ∀ (j : Fin 10) (i : Fin 9),
    1 - factorsQ (vertices i) j / topsOf row j =
      (deviationNats j i : ℚ) / (deviationDenominators j : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT encoding_complete"
  err.flush

#print axioms gapScale_ne
#print axioms gap_encoding
#print axioms deviationDenominators_ne
#print axioms deviation_encoding

end ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor
-- END DONOR MomentEncoding

-- BEGIN DONOR MomentFactor00
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row006
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor00_moment1_before"
  err.flush

theorem factor00_moment1 : prefixMoment (0 : Fin 10) 1 = (5859328294649 : ℚ) / 37664069843400 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor00_moment2_before"
  err.flush

theorem factor00_moment2 : prefixMoment (0 : Fin 10) 2 = (81122399668090406947212739 : ℚ) / 3120880745770729261151832000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor00_moment3_before"
  err.flush

theorem factor00_moment3 : prefixMoment (0 : Fin 10) 3 = (109479842674771625031303752868764528413 : ℚ) / 23509014076326205211074935755972621760000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor00_moment4_before"
  err.flush

theorem factor00_moment4 : prefixMoment (0 : Fin 10) 4 = (2056419581639257154847920214125195732081794878054661 : ℚ) / 2302157385112582222034179290710714092133811644198400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor00_moment5_before"
  err.flush

theorem factor00_moment5 : prefixMoment (0 : Fin 10) 5 = (4444900860816985413851371192883464095790373650750538837293827899 : ℚ) / 24278412632146234291189738663651338349428621205609643841828556800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor00_moment6_before"
  err.flush

theorem factor00_moment6 : prefixMoment (0 : Fin 10) 6 = (36562214885565011439185715856055660336774947079176740413784228091788141930439 : ℚ) / 914423829064040600385670410309157388458764463571043937535229465683824005120000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor00_first_moment_before"
  err.flush

theorem factor00_first_moment :
    prefixMoment (0 : Fin 10) 1 = 1 - meansOf row (0 : Fin 10) / topsOf row (0 : Fin 10) := by
  rw [factor00_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor00_gap_before"
  err.flush

theorem factor00_gap_value :
    gapEvaluator (prefixMoment (0 : Fin 10)) = (3694550018386183559661257140163050631212528957817956767305905635922306932263440559 : ℚ) / 2857574465825126876205220032216116838933638948659512304797592080261950016000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor00_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor00_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor00_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor
-- END DONOR MomentFactor00

-- BEGIN DONOR MomentFactor01
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row006
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor01_moment1_before"
  err.flush

theorem factor01_moment1 : prefixMoment (1 : Fin 10) 1 = (5491529284889 : ℚ) / 37664069843400 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor01_moment2_before"
  err.flush

theorem factor01_moment2 : prefixMoment (1 : Fin 10) 2 = (72366902977987363544858179 : ℚ) / 3120880745770729261151832000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor01_moment3_before"
  err.flush

theorem factor01_moment3 : prefixMoment (1 : Fin 10) 3 = (94165159967045649219286108192697570893 : ℚ) / 23509014076326205211074935755972621760000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor01_moment4_before"
  err.flush

theorem factor01_moment4 : prefixMoment (1 : Fin 10) 4 = (1723331336680755361320895755815378395499852034761221 : ℚ) / 2302157385112582222034179290710714092133811644198400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor01_moment5_before"
  err.flush

theorem factor01_moment5 : prefixMoment (1 : Fin 10) 5 = (3659045714315024815226627596813137945447939284595770649716798939 : ℚ) / 24278412632146234291189738663651338349428621205609643841828556800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor01_moment6_before"
  err.flush

theorem factor01_moment6 : prefixMoment (1 : Fin 10) 6 = (29746359583349911451148716835346769143413926544047104946636185585935783319879 : ℚ) / 914423829064040600385670410309157388458764463571043937535229465683824005120000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor01_first_moment_before"
  err.flush

theorem factor01_first_moment :
    prefixMoment (1 : Fin 10) 1 = 1 - meansOf row (1 : Fin 10) / topsOf row (1 : Fin 10) := by
  rw [factor01_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor01_gap_before"
  err.flush

theorem factor01_gap_value :
    gapEvaluator (prefixMoment (1 : Fin 10)) = (3891096704704670893142418646144648636474454005233861716516661307226953481758990799 : ℚ) / 2857574465825126876205220032216116838933638948659512304797592080261950016000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor01_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor01_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor01_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor
-- END DONOR MomentFactor01

-- BEGIN DONOR MomentFactor02
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row006
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor02_moment1_before"
  err.flush

theorem factor02_moment1 : prefixMoment (2 : Fin 10) 1 = (131542030369 : ℚ) / 993989031000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor02_moment2_before"
  err.flush

theorem factor02_moment2 : prefixMoment (2 : Fin 10) 2 = (38859029574540319902979 : ℚ) / 2173631226246301714200000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor02_moment3_before"
  err.flush

theorem factor02_moment3 : prefixMoment (2 : Fin 10) 3 = (1062791644318518005656298445366233 : ℚ) / 432113119265580641646259388040000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor02_moment4_before"
  err.flush

theorem factor02_moment4 : prefixMoment (2 : Fin 10) 4 = (34918952136356883602327688685886840446926671 : ℚ) / 101521892893006638860912854192780430184000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor02_moment5_before"
  err.flush

theorem factor02_moment5 : prefixMoment (2 : Fin 10) 5 = (15173371618282276472981071156426039727173853035736836099 : ℚ) / 310807875661376803364811192080740409542620520048320000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor02_moment6_before"
  err.flush

theorem factor02_moment6 : prefixMoment (2 : Fin 10) 6 = (2169855462295314344031930013647312867589279439908307738155076473159 : ℚ) / 308939619155820412902466216314290033443812523923545669977920000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor02_first_moment_before"
  err.flush

theorem factor02_first_moment :
    prefixMoment (2 : Fin 10) 1 = 1 - meansOf row (2 : Fin 10) / topsOf row (2 : Fin 10) := by
  rw [factor02_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor02_gap_before"
  err.flush

theorem factor02_gap_value :
    gapEvaluator (prefixMoment (2 : Fin 10)) = (232330629964753362650726637671427727389406329857368929087160989069057799 : ℚ) / 965436309861938790320206925982156354511914137261080218681000000000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor02_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor02_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor02_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor
-- END DONOR MomentFactor02

-- BEGIN DONOR MomentFactor03
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row006
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor03_moment1_before"
  err.flush

theorem factor03_moment1 : prefixMoment (3 : Fin 10) 1 = (8012686854047 : ℚ) / 49541358193600 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor03_moment2_before"
  err.flush

theorem factor03_moment2 : prefixMoment (3 : Fin 10) 2 = (144409821629630979745045251 : ℚ) / 5399561577666471281178112000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor03_moment3_before"
  err.flush

theorem factor03_moment3 : prefixMoment (3 : Fin 10) 3 = (241487456680649724703828386109117004751 : ℚ) / 53500322841514915954758469678435696640000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor03_moment4_before"
  err.flush

theorem factor03_moment4 : prefixMoment (3 : Fin 10) 4 = (5350927255311811270667908863472796697276859377435141 : ℚ) / 6891244509148298561006911084653195388113648772710400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor03_moment5_before"
  err.flush

theorem factor03_moment5 : prefixMoment (3 : Fin 10) 5 = (13000932386434503966096286733273148939604227495296980828481024157 : ℚ) / 95592451535670619900394870700374868475496836788694508553581363200000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor03_moment6_before"
  err.flush

theorem factor03_moment6 : prefixMoment (3 : Fin 10) 6 = (114761666528397885539844584655287215673849244652188134476368383063051041658631 : ℚ) / 4735779882133006567873218643447429060940077556072472603178293352392577515520000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor03_first_moment_before"
  err.flush

theorem factor03_first_moment :
    prefixMoment (3 : Fin 10) 1 = 1 - meansOf row (3 : Fin 10) / topsOf row (3 : Fin 10) := by
  rw [factor03_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor03_gap_before"
  err.flush

theorem factor03_gap_value :
    gapEvaluator (prefixMoment (3 : Fin 10)) = (18484850753623399466466618269372767267349893706363754542348117964733074120937151653 : ℚ) / 44397936394996936573811424782319647446313227088179430654796500178680414208000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor03_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor03_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor03_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor
-- END DONOR MomentFactor03

-- BEGIN DONOR MomentFactor04
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row006
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor04_moment1_before"
  err.flush

theorem factor04_moment1 : prefixMoment (4 : Fin 10) 1 = (103198855181 : ℚ) / 716607877440 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor04_moment2_before"
  err.flush

theorem factor04_moment2 : prefixMoment (4 : Fin 10) 2 = (4838030586373160183951 : ℚ) / 225951814003987306819584 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor04_moment3_before"
  err.flush

theorem factor04_moment3 : prefixMoment (4 : Fin 10) 3 = (106026703221273827340113887226909 : ℚ) / 32383769967423002327336825452756992 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor04_moment4_before"
  err.flush

theorem factor04_moment4 : prefixMoment (4 : Fin 10) 4 = (30966247946839917214736385433333234233202289 : ℚ) / 60336808115636560675505058696684683086421557248 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor04_moment5_before"
  err.flush

theorem factor04_moment5 : prefixMoment (4 : Fin 10) 5 = (4978992528561211077181320221227027527686854831752854183 : ℚ) / 60532964793351234548189633797659352916127468314368218759168 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor04_moment6_before"
  err.flush

theorem factor04_moment6 : prefixMoment (4 : Fin 10) 6 = (583336442209431117423726170775977332770799081205346128064918122047 : ℚ) / 43378399415713676413981770870351555333389979413240263899600971020369920 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor04_first_moment_before"
  err.flush

theorem factor04_first_moment :
    prefixMoment (4 : Fin 10) 1 = 1 - meansOf row (4 : Fin 10) / topsOf row (4 : Fin 10) := by
  rw [factor04_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor04_gap_before"
  err.flush

theorem factor04_gap_value :
    gapEvaluator (prefixMoment (4 : Fin 10)) = (6895849756762172649860491280471731076104981099980902673191648310240079 : ℚ) / 15061944241567248754854781552205401157427076185152869409583670493184000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor04_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor04_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor04_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor
-- END DONOR MomentFactor04

-- BEGIN DONOR MomentFactor05
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row006
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor05_moment1_before"
  err.flush

theorem factor05_moment1 : prefixMoment (5 : Fin 10) 1 = (8132231057361 : ℚ) / 34465372750900 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor05_moment2_before"
  err.flush

theorem factor05_moment2 : prefixMoment (5 : Fin 10) 2 = (150860981830842084932656899 : ℚ) / 2613296221488656513591782000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor05_moment3_before"
  err.flush

theorem factor05_moment3 : prefixMoment (5 : Fin 10) 3 = (262907997500994818580001131964191958977 : ℚ) / 18013645676425014647399199765794620760000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor05_moment4_before"
  err.flush

theorem factor05_moment4 : prefixMoment (5 : Fin 10) 4 = (6140185895284726365799345936010246180118913617713061 : ℚ) / 1614202233385628375724574953022457318991508966578400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor05_moment5_before"
  err.flush

theorem factor05_moment5 : prefixMoment (5 : Fin 10) 5 = (15892568939860340622493074884238234020662518813489369388517513331 : ℚ) / 15577542867311868372264045936227757461763902217451577727185756800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor05_moment6_before"
  err.flush

theorem factor05_moment6 : prefixMoment (5 : Fin 10) 6 = (150983446510829928384702251741052944635240159070667767659875048670006013031879 : ℚ) / 536885821465027122529596786150250031158891744134607693438761336557314381120000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor05_first_moment_before"
  err.flush

theorem factor05_first_moment :
    prefixMoment (5 : Fin 10) 1 = 1 - meansOf row (5 : Fin 10) / topsOf row (5 : Fin 10) := by
  rw [factor05_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor05_gap_before"
  err.flush

theorem factor05_gap_value :
    gapEvaluator (prefixMoment (5 : Fin 10)) = (2961484094686750895946650336846746109215614469254801137872414307674841115065880439 : ℚ) / 1677768192078209757904989956719531347371536700420649041996129176741607441000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor05_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor05_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor05_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor
-- END DONOR MomentFactor05

-- BEGIN DONOR MomentFactor06
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row006
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor06_moment1_before"
  err.flush

theorem factor06_moment1 : prefixMoment (6 : Fin 10) 1 = (6381913403129 : ℚ) / 29541280259400 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor06_moment2_before"
  err.flush

theorem factor06_moment2 : prefixMoment (6 : Fin 10) 2 = (22777103509872716168994001 : ℚ) / 479977981650428872208598000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor06_moment3_before"
  err.flush

theorem factor06_moment3 : prefixMoment (6 : Fin 10) 3 = (60013012901269412644006859604671257769 : ℚ) / 5671665629710587949647864550540128480000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor06_moment4_before"
  err.flush

theorem factor06_moment4 : prefixMoment (6 : Fin 10) 4 = (130249260277478880812156024687960186382592774599361 : ℚ) / 54453185769088230127932494224176749098973211506400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor06_moment5_before"
  err.flush

theorem factor06_moment5 : prefixMoment (6 : Fin 10) 5 = (246678484295906317805840960441161419136147161404953476010403609 : ℚ) / 450412710110105999036249427884933592584709939567361871892844800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor06_moment6_before"
  err.flush

theorem factor06_moment6 : prefixMoment (6 : Fin 10) 6 = (38381171507029018888863402131054636356754169586914477966512472855255148211 : ℚ) / 302403820494512026131160696567993923484150317273097141879189268235180480000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor06_first_moment_before"
  err.flush

theorem factor06_first_moment :
    prefixMoment (6 : Fin 10) 1 = 1 - meansOf row (6 : Fin 10) / topsOf row (6 : Fin 10) := by
  rw [factor06_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor06_gap_before"
  err.flush

theorem factor06_gap_value :
    gapEvaluator (prefixMoment (6 : Fin 10)) = (839985061969554280738781817406377849373482858113660118007202311742524559456857853 : ℚ) / 1330576810175852914977107064899173263330261396001627424268432780234794112000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor06_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor06_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor06_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor
-- END DONOR MomentFactor06

-- BEGIN DONOR MomentFactor07
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row006
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor07_moment1_before"
  err.flush

theorem factor07_moment1 : prefixMoment (7 : Fin 10) 1 = (3436561490339 : ℚ) / 25301775240000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor07_moment2_before"
  err.flush

theorem factor07_moment2 : prefixMoment (7 : Fin 10) 2 = (6799485628215807313936531 : ℚ) / 352098906662512381680000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor07_moment3_before"
  err.flush

theorem factor07_moment3 : prefixMoment (7 : Fin 10) 3 = (10224794356157304294386010404616358199 : ℚ) / 3563490959449850725993781441280000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor07_moment4_before"
  err.flush

theorem factor07_moment4 : prefixMoment (7 : Fin 10) 4 = (13035081997827030042754964422184087014224830003971 : ℚ) / 29302860380875925064209782191108690819840000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor07_moment5_before"
  err.flush

theorem factor07_moment5 : prefixMoment (7 : Fin 10) 5 = (1147300703056110533622323231974315036753736340535143170768843 : ℚ) / 15968925263760505083421628739881562309968311044096000000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor07_moment6_before"
  err.flush

theorem factor07_moment6 : prefixMoment (7 : Fin 10) 6 = (1218995931265798826627189714267940551466626519525550823486808673603069847 : ℚ) / 101010539462006504202402875132801928446718354390031680245760000000000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor07_first_moment_before"
  err.flush

theorem factor07_first_moment :
    prefixMoment (7 : Fin 10) 1 = 1 - meansOf row (7 : Fin 10) / topsOf row (7 : Fin 10) := by
  rw [factor07_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor07_gap_before"
  err.flush

theorem factor07_gap_value :
    gapEvaluator (prefixMoment (7 : Fin 10)) = (102451868333919999411246573889369963073719599183297365362932042658752226367801671 : ℚ) / 175084935067477940617498316896856675974311814276054912425984000000000000000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor07_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor07_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor07_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor
-- END DONOR MomentFactor07

-- BEGIN DONOR MomentFactor08
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row006
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor08_moment1_before"
  err.flush

theorem factor08_moment1 : prefixMoment (8 : Fin 10) 1 = (8049633113897 : ℚ) / 42638168707680 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor08_moment2_before"
  err.flush

theorem factor08_moment2 : prefixMoment (8 : Fin 10) 2 = (29169538752955361470328279 : ℚ) / 799925909527616062968032256 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor08_moment3_before"
  err.flush

theorem factor08_moment3 : prefixMoment (8 : Fin 10) 3 = (49057038117030496560380270589344783717 : ℚ) / 6821475176816572397366574680392814985216 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor08_moment4_before"
  err.flush

theorem factor08_moment4 : prefixMoment (8 : Fin 10) 4 = (1093314986531173008593352725348818774233983496381089 : ℚ) / 756223544503326307700839879736333074997656045866713088 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor08_moment5_before"
  err.flush

theorem factor08_moment5 : prefixMoment (8 : Fin 10) 5 = (13356106093029207775204870451621819736916294810589926036029485531 : ℚ) / 45141581899753614296954892353839104026520788045910588310057622962176 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor08_moment6_before"
  err.flush

theorem factor08_moment6 : prefixMoment (8 : Fin 10) 6 = (118499021806018019299595895900985248515666906423758075709212071138965138100823 : ℚ) / 1924754384773248443818402354273945383417126953682158661673078152803496551440711680 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor08_first_moment_before"
  err.flush

theorem factor08_first_moment :
    prefixMoment (8 : Fin 10) 1 = 1 - meansOf row (8 : Fin 10) / topsOf row (8 : Fin 10) := by
  rw [factor08_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor08_gap_before"
  err.flush

theorem factor08_gap_value :
    gapEvaluator (prefixMoment (8 : Fin 10)) = (3753280997095289310267383365737216977041754509421925902900233678422777066746200039 : ℚ) / 6014857452416401386932507357106079323178521730256745817728369227510926723252224000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor08_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor08_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor08_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor
-- END DONOR MomentFactor08

-- BEGIN DONOR MomentFactor09
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row006
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor09_moment1_before"
  err.flush

theorem factor09_moment1 : prefixMoment (9 : Fin 10) 1 = (8049123717737 : ℚ) / 42637440998880 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor09_moment2_before"
  err.flush

theorem factor09_moment2 : prefixMoment (9 : Fin 10) 2 = (29165879114412026910476759 : ℚ) / 799898604970508178150951936 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor09_moment3_before"
  err.flush

theorem factor09_moment3 : prefixMoment (9 : Fin 10) 3 = (49047884113283080347716286377995149317 : ℚ) / 6821125914903292549672346621101341966336 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor09_moment4_before"
  err.flush

theorem factor09_moment4 : prefixMoment (9 : Fin 10) 4 = (1093045192073822865459114218358245973465423724436129 : ℚ) / 756171919730813288996026657906124466726588376251629568 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor09_moment5_before"
  err.flush

theorem factor09_moment5 : prefixMoment (9 : Fin 10) 5 = (13352018560496668333083759651619810800879818720246382454650523931 : ℚ) / 45137729857545324918079734968113621884599121869373229029275128037376 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor09_moment6_before"
  err.flush

theorem factor09_moment6 : prefixMoment (9 : Fin 10) 6 = (118455828453669221810154316284151354778227711569849031462127083030602202333783 : ℚ) / 1924557293624472938580003769090332131236616610846459743221507527948276851414138880 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor09_first_moment_before"
  err.flush

theorem factor09_first_moment :
    prefixMoment (9 : Fin 10) 1 = 1 - meansOf row (9 : Fin 10) / topsOf row (9 : Fin 10) := by
  rw [factor09_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor09_gap_before"
  err.flush

theorem factor09_gap_value :
    gapEvaluator (prefixMoment (9 : Fin 10)) = (3752655687393018937650023281028497461053750820414746711151049442198286587237882279 : ℚ) / 6014241542576477933062511778407287910114426908895186697567211024838365160669184000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor09_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor09_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW006_MOMENT factor09_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor
-- END DONOR MomentFactor09

-- BEGIN DONOR PrefixFloorChecks
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! All five original floor obligations for the actual cell01 row6, expressed
through the existing finite prefix evaluator. The old two equalities are
reused. Both Q80 bounds remain explicit, and the saved new field is the
maximum of the exact old and new Q96 evaluations. The separate bridge to
the original rationalMoment still requires its own acceptance. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row006
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_FLOOR first_moments_before"
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
  err.putStrLn "P26_CELL01_ROW006_FLOOR total_Q80_before"
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
    totalLowerQ80 prefixMoment = (9670133075035730448439 : ℚ) / (2 : ℚ)^80 := by
  have h : (∑ j : Fin 10, momentRow.factorFloorsQ80[j.val]! : ℤ) = 9670133075035730448439 := by
    decide +kernel
  rw [total_Q80_eq_saved, h]
  norm_num

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW006_FLOOR new_Q96_before"
  err.flush

theorem new_Q96_value :
    newFloorQ96 (massOf row) (meansOf row) prefixMoment = 436520528746544 := by
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
  err.putStrLn "P26_CELL01_ROW006_FLOOR complete"
  err.flush

#print axioms all_first_moments
#print axioms all_saved_Q80
#print axioms all_Q80_bounds
#print axioms total_Q80_eq_saved
#print axioms total_Q80_value
#print axioms new_Q96_value
#print axioms saved_new_Q96_max
#print axioms prefix_floor_checks

end ImbalancedChen.P2OriginalSaving19Cell01Row006MomentFloor
-- END DONOR PrefixFloorChecks
