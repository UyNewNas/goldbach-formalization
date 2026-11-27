import ImbalancedChen.P2OriginalSaving19Geometry01BoundedAccess
import ImbalancedChen.P2OriginalSaving19RowNumericsPure
import Mathlib.Tactic.FinCases
import ImbalancedChen.P2Winner9FastDetPure
import ImbalancedChen.P2OriginalSaving19Moment01Shape
import ImbalancedChen.P2OriginalSaving19PrefixMoments
import Mathlib.Algebra.BigOperators.Field

/-! SOURCE CANDIDATE: original Cell01 row 10 only.
Twenty-one accepted row000 source bodies are merged into one new owner.
Original ordinal, vertex order and decoded row/record identities are retained.
All host-produced literals remain closed Lean proof obligations. This owner
has not been compiled, independently replayed or audited. No integral or
OriginalFloorBridge claim is included. The shared bounded-access owner is
imported unchanged. -/

-- BEGIN DONOR Input
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! The actual original row 10 and its original nine ordered vertices. The small
selectors refer to the already decoded values, with closed equalities to
the original bounded accesses. No numeric field is recomputed or assumed. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2OriginalSaving19RowNumericsPure
open P2OriginalSaving19Geometry01Decoding
open P2OriginalSaving19Geometry01DirectDecoding
open P2OriginalSaving19Geometry01BoundedAccess

noncomputable def row : GeometryRow := geometryRowsTyped010

noncomputable def vertices : Fin 9 → QPoint :=
  ![(fun j => geometryVerticesTyped039[j.val]!),
    (fun j => geometryVerticesTyped035[j.val]!),
    (fun j => geometryVerticesTyped029[j.val]!),
    (fun j => geometryVerticesTyped028[j.val]!),
    (fun j => geometryVerticesTyped025[j.val]!),
    (fun j => geometryVerticesTyped017[j.val]!),
    (fun j => geometryVerticesTyped012[j.val]!),
    (fun j => geometryVerticesTyped004[j.val]!),
    (fun j => geometryVerticesTyped002[j.val]!)]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_INPUT before_row_binding"
  err.flush

theorem boundedRow_eq : boundedRow (10 : Fin 144) = row := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_INPUT before_vertex_binding"
  err.flush

theorem boundedRowVertex_eq : boundedRowVertex (10 : Fin 144) = vertices := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem raw_row_eq : concreteGeometry01.rows[10]! = row :=
  (row_lookup_no_fallback (10 : Fin 144)).trans boundedRow_eq

theorem raw_vertices_eq (i : Fin 9) (j : Fin 8) :
    ((concreteGeometry01.vertices[
      (concreteGeometry01.rows[10]!).vertexIds[i.val]!]!)[j.val]!) = vertices i j :=
  (raw_vertex_no_fallback (10 : Fin 144) i j).trans
    (congrFun (congrFun boundedRowVertex_eq i) j)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_INPUT bindings_complete"
  err.flush

#print axioms boundedRow_eq
#print axioms boundedRowVertex_eq
#print axioms raw_row_eq
#print axioms raw_vertices_eq

/-- The original factor and mean lookups retain the certified bounds. -/
theorem factor_maximum_no_fallback (j : Fin 10) :
    row.factorMaxima[j.val]! =
      (boundedRow (10 : Fin 144)).factorMaxima[j.val]'(factor_maximum_bound (10 : Fin 144) j) := by
  rw [← raw_row_eq]
  exact factor_maximum_lookup_no_fallback (10 : Fin 144) j

theorem weighted_mean_no_fallback (j : Fin 10) :
    row.gapWeightedMeans[j.val]! =
      (boundedRow (10 : Fin 144)).gapWeightedMeans[j.val]'(weighted_mean_bound (10 : Fin 144) j) := by
  rw [← raw_row_eq]
  exact weighted_mean_lookup_no_fallback (10 : Fin 144) j

#print axioms factor_maximum_no_fallback
#print axioms weighted_mean_no_fallback

end ImbalancedChen.P2OriginalSaving19Cell01Row010
-- END DONOR Input

-- BEGIN DONOR Determinant
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row10.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Determinant_physical_volume_positive_before"
  err.flush

theorem physical_volume_positive :
    0 < row.physicalVolume := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Determinant_volume_eq_before"
  err.flush

theorem volume_eq :
    row.physicalVolume = |(edgeOf vertices).det| / (Nat.factorial 8 : ℚ) := by
  rw [← P2Winner9FastDetPure.fastDet_eq (edgeOf vertices)]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Determinant_det_ne_before"
  err.flush

theorem det_ne :
    (edgeOf vertices).det ≠ 0 := by
  intro hzero
  have h := volume_eq
  rw [hzero, abs_zero, zero_div] at h
  exact (ne_of_gt physical_volume_positive) h

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Determinant_complete"
  err.flush

#print axioms physical_volume_positive
#print axioms volume_eq
#print axioms det_ne

end ImbalancedChen.P2OriginalSaving19Cell01Row010
-- END DONOR Determinant

-- BEGIN DONOR Physical
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row10.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Physical_all_physical_before"
  err.flush

theorem all_physical :
    ∀ i : Fin 9, PhysicalQ (vertices i) := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Physical_complete"
  err.flush

#print axioms all_physical

end ImbalancedChen.P2OriginalSaving19Cell01Row010
-- END DONOR Physical

-- BEGIN DONOR Gap
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row10.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Gap_gap_sum_positive_before"
  err.flush

theorem gap_sum_positive :
    0 < gapSumOf vertices := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Gap_mean_gap_eq_before"
  err.flush

theorem mean_gap_eq :
    row.meanGap = gapSumOf vertices / 9 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Gap_complete"
  err.flush

#print axioms gap_sum_positive
#print axioms mean_gap_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row010
-- END DONOR Gap

-- BEGIN DONOR Means
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row10.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Means_weighted_means_eq_before"
  err.flush

theorem weighted_means_eq :
    ∀ j : Fin 10, meansOf row j = computedMeanOf vertices j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Means_complete"
  err.flush

#print axioms weighted_means_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row010
-- END DONOR Means

-- BEGIN DONOR Maxima
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row10.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Maxima_factor_le_maxima_before"
  err.flush

theorem factor_le_maxima :
    ∀ i : Fin 9, ∀ j : Fin 10, factorsQ (vertices i) j ≤ topsOf row j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Maxima_factor_maxima_attained_before"
  err.flush

theorem factor_maxima_attained :
    ∀ j : Fin 10, ∃ i : Fin 9, factorsQ (vertices i) j = topsOf row j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Maxima_complete"
  err.flush

#print axioms factor_le_maxima
#print axioms factor_maxima_attained

end ImbalancedChen.P2OriginalSaving19Cell01Row010
-- END DONOR Maxima

-- BEGIN DONOR Jensen
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row10.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Jensen_jensen_eq_before"
  err.flush

theorem jensen_eq :
    row.jensenBound = oldEvaluator (massOf row) (meansOf row) := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Jensen_old_floor_eq_before"
  err.flush

theorem old_floor_eq :
    row.jensenFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) := by
  unfold oldFloorQ96
  rw [← jensen_eq]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Jensen_complete"
  err.flush

#print axioms jensen_eq
#print axioms old_floor_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row010
-- END DONOR Jensen

-- BEGIN DONOR Arithmetic
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row10.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Arithmetic_row_data_checks_before"
  err.flush

theorem row_data_checks :
    RowDataChecksFor vertices row := by
  exact ⟨det_ne, all_physical, gap_sum_positive, volume_eq, mean_gap_eq,
    weighted_means_eq, factor_le_maxima, factor_maxima_attained,
    jensen_eq, old_floor_eq⟩

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Arithmetic_bounded_row_data_checks_before"
  err.flush

theorem bounded_row_data_checks :
    RowDataChecksFor
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRowVertex (10 : Fin 144))
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (10 : Fin 144)) := by
  rw [boundedRowVertex_eq, boundedRow_eq]
  exact row_data_checks

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010 Arithmetic_complete"
  err.flush

#print axioms row_data_checks
#print axioms bounded_row_data_checks

end ImbalancedChen.P2OriginalSaving19Cell01Row010
-- END DONOR Arithmetic

-- BEGIN DONOR OldFloor
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! The actual moment row10 old floor is the actual geometry row10 Jensen
floor and the same original exact Q96 arithmetic. The ten Q80 fields and
the new Q96 field are not certified by these old-floor equalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open P2OriginalSaving19Archive
open P2OriginalSaving19Moment01Decoding
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

noncomputable def momentRow : MomentRecord :=
  momentConcrete01.rows[(10 : Fin 144).val]'(P2OriginalSaving19Moment01Shape.row_bound 10)

theorem raw_moment_row_eq : momentConcrete01.rows[10]! = momentRow :=
  P2OriginalSaving19Moment01Shape.row_lookup_no_fallback (10 : Fin 144)

theorem moment_row_eq : momentRow = momentTypedRecord010 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_OLD_FLOOR before_original_moment_geometry_binding"
  err.flush

theorem moment_old_matches_geometry : momentRow.oldFloorQ96 = row.jensenFloorQ96 := by
  decide +kernel

theorem moment_old_eq_evaluator :
    momentRow.oldFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) :=
  moment_old_matches_geometry.trans old_floor_eq

theorem actual_moment_old_eq_bounded_evaluator :
    (momentConcrete01.rows[10]!).oldFloorQ96 =
      oldFloorQ96
        (massOf (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (10 : Fin 144)))
        (meansOf (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (10 : Fin 144))) := by
  rw [raw_moment_row_eq, boundedRow_eq]
  exact moment_old_eq_evaluator

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_OLD_FLOOR complete"
  err.flush

#print axioms raw_moment_row_eq
#print axioms moment_row_eq
#print axioms moment_old_matches_geometry
#print axioms moment_old_eq_evaluator
#print axioms actual_moment_old_eq_bounded_evaluator

/-- The saved ten Q80 fields are accessed at their true bounded indices. -/
theorem moment_floor_bound (j : Fin 10) : j.val < momentRow.factorFloorsQ80.size := by
  have hs : momentRow.factorFloorsQ80.size = 10 :=
    (P2OriginalSaving19Moment01Shape.row_ids_and_floor_sizes_bounded (10 : Fin 144)).2
  rw [hs]
  exact j.isLt

theorem moment_floor_lookup_no_fallback (j : Fin 10) :
    momentRow.factorFloorsQ80[j.val]! =
      momentRow.factorFloorsQ80[j.val]'(moment_floor_bound j) :=
  getElem!_pos momentRow.factorFloorsQ80 j.val (moment_floor_bound j)

#print axioms moment_floor_bound
#print axioms moment_floor_lookup_no_fallback

end ImbalancedChen.P2OriginalSaving19Cell01Row010
-- END DONOR OldFloor

-- BEGIN DONOR MomentEncoding
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact nonnegative integer encodings of the actual nine ordered vertices.
The existing prefix evaluator is used unchanged. Host-generated literals
are connected to the decoded row by closed Lean equalities below. No
saved field, moment value or final floor is an assumption. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row010
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

def gapScale : Nat := 4312000000

def gapNats : Fin 9 → Nat := ![0, 0, 0, 0, 0, 0, 0, 21688723, 22683452]

def deviationDenominators : Fin 10 → Nat := ![11126014176200, 3922500732920, 4330673778200, 49810361043520, 4330673778200, 9747822298060, 4950280900180, 4082827445312, 14289896058592, 4763217390624]

def deviationNats : Fin 10 → Fin 9 → Nat :=
  ![![306210664760, 4932675545336, 1390492642385, 1390492642385, 660238458440, 1165084095560, 306210664760, 393833105680, 0],
    ![315899562440, 1858054522632, 677326888315, 677326888315, 433908827000, 602190706040, 315899562440, 140654680600, 0],
    ![0, 247846332888, 464709696605, 464709696605, 531096440600, 568492413720, 619615832220, 738532002040, 800821932020],
    ![0, 6939697320864, 5421653774845, 5421653774845, 7081322374720, 7100020361280, 8674621651080, 7185040155440, 8310277600240],
    ![1239231664440, 247846332888, 464709696605, 464709696605, 531096440600, 568492413720, 0, 738532002040, 999747837440],
    ![4337310825540, 2602386495324, 1084342949305, 1084342949305, 1681823645260, 1560286732620, 0, 1007658070580, 656021369080],
    ![1858838786420, 867453454868, 0, 1084316818585, 1150703562580, 1188099535700, 1858838786420, 1358139124020, 1221503148580],
    ![991385331552, 0, 1301180182302, 216863363717, 283250107712, 320646080832, 991385331552, 490685669152, 354049693712],
    ![3469848660432, 0, 4554374524777, 4554374524777, 3824120340832, 1122261282912, 3469848660432, 1717399842032, 1239173927992],
    ![1156616220144, 0, 1518043546019, 1518043546019, 1274625484704, 1442907363744, 1156616220144, 981371338304, 840716657704]]

def prefixMoment (j : Fin 10) (k : Nat) : ℚ :=
  normalizedMoment gapNats (deviationNats j) (deviationDenominators j) k

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT gap_encoding_before"
  err.flush

theorem gapScale_ne : gapScale ≠ 0 := by decide +kernel

theorem gap_encoding : ∀ i : Fin 9,
    gapQ (vertices i) = (gapNats i : ℚ) / (gapScale : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT deviation_encoding_before"
  err.flush

theorem deviationDenominators_ne : ∀ j : Fin 10, deviationDenominators j ≠ 0 := by
  decide +kernel

theorem deviation_encoding : ∀ (j : Fin 10) (i : Fin 9),
    1 - factorsQ (vertices i) j / topsOf row j =
      (deviationNats j i : ℚ) / (deviationDenominators j : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT encoding_complete"
  err.flush

#print axioms gapScale_ne
#print axioms gap_encoding
#print axioms deviationDenominators_ne
#print axioms deviation_encoding

end ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor
-- END DONOR MomentEncoding

-- BEGIN DONOR MomentFactor00
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row010
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor00_moment1_before"
  err.flush

theorem factor00_moment1 : prefixMoment (0 : Fin 10) 1 = (1642954741628232611 : ℚ) / 17023636140649215000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor00_moment2_before"
  err.flush

theorem factor00_moment2 : prefixMoment (0 : Fin 10) 2 = (22300510622886949753156054509517 : ℚ) / 2083457387344672054775418513000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor00_moment3_before"
  err.flush

theorem factor00_moment3 : prefixMoment (0 : Fin 10) 3 = (31542193552881975145111072696991150964324653 : ℚ) / 23180576427105435756971289282925923990600000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor00_moment4_before"
  err.flush

theorem factor00_moment4 : prefixMoment (0 : Fin 10) 4 = (219718990167995157396278418803287167082591636071537824169 : ℚ) / 1117598828408671371377944084332308172713563527356120000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor00_moment5_before"
  err.flush

theorem factor00_moment5 : prefixMoment (0 : Fin 10) 5 = (1663569166582659383035355294878957623335185550491118143764344844206801 : ℚ) / 52224565714353433652824023403227193973368548475010564028479044800000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor00_moment6_before"
  err.flush

theorem factor00_moment6 : prefixMoment (0 : Fin 10) 6 = (16556827852374216830580699116635823711881275936410619092937802763521471760246825897 : ℚ) / 2905256292418923913192331167741131644885228378000922134128078164847174468800000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor00_first_moment_before"
  err.flush

theorem factor00_first_moment :
    prefixMoment (0 : Fin 10) 1 = 1 - meansOf row (0 : Fin 10) / topsOf row (0 : Fin 10) := by
  rw [factor00_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor00_gap_before"
  err.flush

theorem factor00_gap_value :
    gapEvaluator (prefixMoment (0 : Fin 10)) = (64437744510645612187251633866304508348572783607866354764895707047325404406726655132833260310767423264986371739177857 : ℚ) / 73091908421389841049392598212947714322482265072238622867455810743955425539657443764398348725958546875000000000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor00_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor00_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor00_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor
-- END DONOR MomentFactor00

-- BEGIN DONOR MomentFactor01
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row010
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor01_moment1_before"
  err.flush

theorem factor01_moment1 : prefixMoment (1 : Fin 10) 1 = (155762014150783717 : ℚ) / 1200344061784513800 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor01_moment2_before"
  err.flush

theorem factor01_moment2 : prefixMoment (1 : Fin 10) 2 = (316858427857265176723816388971 : ℚ) / 17263951694388392193221465752000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor01_moment3_before"
  err.flush

theorem factor01_moment3 : prefixMoment (1 : Fin 10) 3 = (574788415096773470803487477148597802112879 : ℚ) / 203153589523001832687154817004290036867520000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor01_moment4_before"
  err.flush

theorem factor01_moment4 : prefixMoment (1 : Fin 10) 4 = (1639677928728411382315386171058124792624591146951589829 : ℚ) / 3453103783130315261626761258664956643054104424085286400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor01_moment5_before"
  err.flush

theorem factor01_moment5 : prefixMoment (1 : Fin 10) 5 = (4920974598640852925357486851148981215157916491955209089645132061767 : ℚ) / 56888168904745442651526856872116447359018939208892751699270054809600000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor01_moment6_before"
  err.flush

theorem factor01_moment6 : prefixMoment (1 : Fin 10) 6 = (6329858702524638521021789889924752924723616187304356570868738156604928966199871 : ℚ) / 371906473705567920777739873729901172462230645698404572536770609032774285086720000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor01_first_moment_before"
  err.flush

theorem factor01_first_moment :
    prefixMoment (1 : Fin 10) 1 = 1 - meansOf row (1 : Fin 10) / topsOf row (1 : Fin 10) := by
  rw [factor01_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor01_gap_before"
  err.flush

theorem factor01_gap_value :
    gapEvaluator (prefixMoment (1 : Fin 10)) = (9270025565912650754435283129497961881492114572880762121439874991657041023683170923453400739714807491968553993 : ℚ) / 8982346868608073740878885562366050099821602534073144058161516577459066336448013120281367540872143552000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor01_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor01_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor01_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor
-- END DONOR MomentFactor01

-- BEGIN DONOR MomentFactor02
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row010
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor02_moment1_before"
  err.flush

theorem factor02_moment1 : prefixMoment (2 : Fin 10) 1 = (796587572604649159 : ℚ) / 6626255681179365000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor02_moment2_before"
  err.flush

theorem factor02_moment2 : prefixMoment (2 : Fin 10) 2 = (1548904331651708644651800790423 : ℚ) / 105219222995818269273565091000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor02_moment3_before"
  err.flush

theorem factor02_moment3 : prefixMoment (2 : Fin 10) 3 = (2504630098952684885536571741983618867451593 : ℚ) / 1367010389971705880986605306073790448600000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor02_moment4_before"
  err.flush

theorem factor02_moment4 : prefixMoment (2 : Fin 10) 4 = (17809053558345472020998219909441494689124203212708025211 : ℚ) / 76960988654906497683248480077807743370437253706760000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor02_moment5_before"
  err.flush

theorem factor02_moment5 : prefixMoment (2 : Fin 10) 5 = (658081338060463368093507150991826933406954975471094311093278920729 : ℚ) / 22219529034143417219309549471197805997017833579752418938708800000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor02_moment6_before"
  err.flush

theorem factor02_moment6 : prefixMoment (2 : Fin 10) 6 = (5538614520948743640829363468140232236117604717824740126001187923852040686496487 : ℚ) / 1443382976281777041747093369056580218649837589224078587188309096883822400000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor02_first_moment_before"
  err.flush

theorem factor02_first_moment :
    prefixMoment (2 : Fin 10) 1 = 1 - meansOf row (2 : Fin 10) / topsOf row (2 : Fin 10) := by
  rw [factor02_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor02_gap_before"
  err.flush

theorem factor02_gap_value :
    gapEvaluator (prefixMoment (2 : Fin 10)) = (6267657684268608751027590972619058751747364674178387654606366618904314496562506253779479017595503405467228644631 : ℚ) / 36313359545825645140215591385321172748469543514632084742578778765232846512644722476814664899703125000000000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor02_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor02_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor02_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor
-- END DONOR MomentFactor02

-- BEGIN DONOR MomentFactor03
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row010
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor03_moment1_before"
  err.flush

theorem factor03_moment1 : prefixMoment (3 : Fin 10) 1 = (1955269334884089979 : ℚ) / 15242717634732772800 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor03_moment2_before"
  err.flush

theorem factor03_moment2 : prefixMoment (3 : Fin 10) 2 = (46379707305526760940454210730139 : ℚ) / 2783899318458384951596020598272000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor03_moment3_before"
  err.flush

theorem factor03_moment3 : prefixMoment (3 : Fin 10) 3 = (909728974803871107212357347687320846307184797 : ℚ) / 416001090483664248765822675770469337886392320000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor03_moment4_before"
  err.flush

theorem factor03_moment4 : prefixMoment (3 : Fin 10) 4 = (78044237790880528339489181969687881097079701159450163053807 : ℚ) / 269375138649361527791690500629221238218079052411363078963200000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor03_moment5_before"
  err.flush

theorem factor03_moment5 : prefixMoment (3 : Fin 10) 5 = (242322956141539106617532326301923011219107024592506358429585609864010083 : ℚ) / 6261580692394046204656730152183083552216837220052734052213142158783283200000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor03_moment6_before"
  err.flush

theorem factor03_moment6 : prefixMoment (3 : Fin 10) 6 = (24362749032672941277160318454976748486755736032256121860288441473933707452746013908397 : ℚ) / 4678373924869220811564307511797278390781362126023098169916366687384459055612255272960000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor03_first_moment_before"
  err.flush

theorem factor03_first_moment :
    prefixMoment (3 : Fin 10) 1 = 1 - meansOf row (3 : Fin 10) / topsOf row (3 : Fin 10) := by
  rw [factor03_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor03_gap_before"
  err.flush

theorem factor03_gap_value :
    gapEvaluator (prefixMoment (3 : Fin 10)) = (5035814712586368334323079860001891536964791721394880588725964002467520150823587703069063962622676087195751829989057 : ℚ) / 37664287793939140465070992937816452730827235314927365003753947068118512656746366720947509786633764666867712000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor03_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor03_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor03_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor
-- END DONOR MomentFactor03

-- BEGIN DONOR MomentFactor04
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row010
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor04_moment1_before"
  err.flush

theorem factor04_moment1 : prefixMoment (4 : Fin 10) 1 = (187478068627493471 : ℚ) / 1325251136235873000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor04_moment2_before"
  err.flush

theorem factor04_moment2 : prefixMoment (4 : Fin 10) 2 = (433592658627034810729598227787 : ℚ) / 21043844599163653854713018200000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor04_moment3_before"
  err.flush

theorem factor04_moment3 : prefixMoment (4 : Fin 10) 3 = (843002989132193125096651175234989316126867 : ℚ) / 273402077994341176197321061214758089720000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor04_moment4_before"
  err.flush

theorem factor04_moment4 : prefixMoment (4 : Fin 10) 4 = (7285332928039090046867228224296888606462147479875938959 : ℚ) / 15392197730981299536649696015561548674087450741352000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor04_moment5_before"
  err.flush

theorem factor04_moment5 : prefixMoment (4 : Fin 10) 5 = (2315170123357292228999263003219932176678177106377595349210946675807 : ℚ) / 31107340647800784107033369259676928395824967011653386514192320000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor04_moment6_before"
  err.flush

theorem factor04_moment6 : prefixMoment (4 : Fin 10) 6 = (24195010996184527940056692697487722811142655768871501119275836345156005885721821 : ℚ) / 2020736166794487858445930716679212306109772624913710022063632735637351360000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor04_first_moment_before"
  err.flush

theorem factor04_first_moment :
    prefixMoment (4 : Fin 10) 1 = 1 - meansOf row (4 : Fin 10) / topsOf row (4 : Fin 10) := by
  rw [factor04_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor04_gap_before"
  err.flush

theorem factor04_gap_value :
    gapEvaluator (prefixMoment (4 : Fin 10)) = (6544877458993237064100071016614889005380359814845517377114987703902378139793783959411217184323304996055604477 : ℚ) / 16268385076529889022816584940623885391314355494555173964675292886824315237664835669612969875067000000000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor04_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor04_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor04_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor
-- END DONOR MomentFactor04

-- BEGIN DONOR MomentFactor05
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row010
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor05_moment1_before"
  err.flush

theorem factor05_moment1 : prefixMoment (5 : Fin 10) 1 = (454189644473580151 : ℚ) / 2982979840540830900 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor05_moment2_before"
  err.flush

theorem factor05_moment2 : prefixMoment (5 : Fin 10) 2 = (2608057035417658530356713547491 : ℚ) / 106617710482387040261966146198000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor05_moment3_before"
  err.flush

theorem factor05_moment3 : prefixMoment (5 : Fin 10) 3 = (12929396643161314837660231869534612186652813 : ℚ) / 3117871486824953369882281750937130875327640000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor05_moment4_before"
  err.flush

theorem factor05_moment4 : prefixMoment (5 : Fin 10) 4 = (12741051386616131811852078745446166241977837474952325001 : ℚ) / 17178345374906563374889442763402303800884796361003170400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor05_moment5_before"
  err.flush

theorem factor05_moment5 : prefixMoment (5 : Fin 10) 5 = (251395129988564022629741200201002784746880594326517718233300973014367 : ℚ) / 1797312316825046739041432386551823612400193096021978468448751791817600000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor05_moment6_before"
  err.flush

theorem factor05_moment6 : prefixMoment (5 : Fin 10) 6 = (7299997125090039058641748109829557826654291288596832683696924334097651938124747573 : ℚ) / 262798216177876048600946468517475612270659314664790625978729263419809705045307840000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor05_first_moment_before"
  err.flush

theorem factor05_first_moment :
    prefixMoment (5 : Fin 10) 1 = 1 - meansOf row (5 : Fin 10) / topsOf row (5 : Fin 10) := by
  rw [factor05_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor05_gap_before"
  err.flush

theorem factor05_gap_value :
    gapEvaluator (prefixMoment (5 : Fin 10)) = (1925613310788672866584885931757337553863531590492579041274336682937474294280652048239358438444538842385119462697 : ℚ) / 2115715375643909855439023604601384109278394723139281821160160100282495572880721206357865206080659287923000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor05_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor05_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor05_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor
-- END DONOR MomentFactor05

-- BEGIN DONOR MomentFactor06
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row010
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor06_moment1_before"
  err.flush

theorem factor06_moment1 : prefixMoment (6 : Fin 10) 1 = (74169185363646599 : ℚ) / 309155144830323000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor06_moment2_before"
  err.flush

theorem factor06_moment2 : prefixMoment (6 : Fin 10) 2 = (8039209439500261512313109478741 : ℚ) / 137481365310026010306380872910000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor06_moment3_before"
  err.flush

theorem factor06_moment3 : prefixMoment (6 : Fin 10) 3 = (118057439916654104026340725345528372561908839 : ℚ) / 8166856521898691796944220781762187713485600000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor06_moment4_before"
  err.flush

theorem factor06_moment4 : prefixMoment (6 : Fin 10) 4 = (6893264620962838612633756612248958403458634243429791683 : ℚ) / 1904228406207435792925501620732880496278968168895204000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor06_moment5_before"
  err.flush

theorem factor06_moment5 : prefixMoment (6 : Fin 10) 5 = (1670729324951527281411111606385221909911845798458947536505530023893111 : ℚ) / 1821193136305738062056233778928357157110622470828886552855155134304000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor06_moment6_before"
  err.flush

theorem factor06_moment6 : prefixMoment (6 : Fin 10) 6 = (1766215060379256491737647015723940573221151158686025591149246602088810421449378741 : ℚ) / 7512847998494338711279184710778325819525098243945796929679095422829961598145600000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor06_first_moment_before"
  err.flush

theorem factor06_first_moment :
    prefixMoment (6 : Fin 10) 1 = 1 - meansOf row (6 : Fin 10) / topsOf row (6 : Fin 10) := by
  rw [factor06_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor06_gap_before"
  err.flush

theorem factor06_gap_value :
    gapEvaluator (prefixMoment (6 : Fin 10)) = (56884452986691319968578071589802122183776495539937982630274696794752673505913556425480012986322623515399431884118999 : ℚ) / 72580620628861884489360426145265661881055676323283623010844785850286280119582465772011006566487798534000000000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor06_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor06_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor06_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor
-- END DONOR MomentFactor06

-- BEGIN DONOR MomentFactor07
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row010
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor07_moment1_before"
  err.flush

theorem factor07_moment1 : prefixMoment (7 : Fin 10) 1 = (33538506436386749 : ℚ) / 254980906260643200 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor07_moment2_before"
  err.flush

theorem factor07_moment2 : prefixMoment (7 : Fin 10) 2 = (1018458259413680924390861268889 : ℚ) / 56112219969808794803254418165760 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor07_moment3_before"
  err.flush

theorem factor07_moment3 : prefixMoment (7 : Fin 10) 3 = (2400852175840908667387735914109425799854629 : ℚ) / 916386046840477725822723431133147463003668480 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor07_moment4_before"
  err.flush

theorem factor07_moment4 : prefixMoment (7 : Fin 10) 4 = (4796641275677045427985174441424188059513842180465168617 : ℚ) / 12159699833259128938171895809127932770515385896418379038720 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor07_moment5_before"
  err.flush

theorem factor07_moment5 : prefixMoment (7 : Fin 10) 5 = (8588370610616428818320388750675372280600958324787892083584626421165 : ℚ) / 139008677376761140965908563184513383387264454199778319515867550205345792 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor07_moment6_before"
  err.flush

theorem factor07_moment6 : prefixMoment (7 : Fin 10) 6 = (71219224226182281664280809925490440668634097085943564863764292433596835138724389 : ℚ) / 7094355539129521236083434588895141404711231908707836819321174783153148261961616588800 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor07_first_moment_before"
  err.flush

theorem factor07_first_moment :
    prefixMoment (7 : Fin 10) 1 = 1 - meansOf row (7 : Fin 10) / topsOf row (7 : Fin 10) := by
  rw [factor07_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor07_gap_before"
  err.flush

theorem factor07_gap_value :
    gapEvaluator (prefixMoment (7 : Fin 10)) = (12987911748487070124190617948640686118564500836618309938311349713787977476221925614413597201553609280657391729844639 : ℚ) / 22845873632964895505278149515511300621782728930424714650358885001191033570923968744667510991121484081004544000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor07_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor07_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor07_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor
-- END DONOR MomentFactor07

-- BEGIN DONOR MomentFactor08
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row010
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor08_moment1_before"
  err.flush

theorem factor08_moment1 : prefixMoment (8 : Fin 10) 1 = (3890112904638288683 : ℚ) / 21864612711850154400 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor08_moment2_before"
  err.flush

theorem factor08_moment2 : prefixMoment (8 : Fin 10) 2 = (7493419977915160208116775394099 : ℚ) / 229124898210052578779955540843520 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor08_moment3_before"
  err.flush

theorem factor08_moment3 : prefixMoment (8 : Fin 10) 3 = (12160897956773783495099926182642892046242109 : ℚ) / 1964502587914274124732463355491684873814114304 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor08_moment4_before"
  err.flush

theorem factor08_moment4 : prefixMoment (8 : Fin 10) 4 = (2195315988536145348190091316873182030675740586847683148959 : ℚ) / 1824714956228448036284420114857260411375465096081283004497920 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor08_moment5_before"
  err.flush

theorem factor08_moment5 : prefixMoment (8 : Fin 10) 5 = (2914342357646593479594483465130728513053030481755269735868984054377959 : ℚ) / 12168327295162627584448048028344356430154967092373303208870759980735660032 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor08_moment6_before"
  err.flush

theorem factor08_moment6 : prefixMoment (8 : Fin 10) 6 = (635521587919923701962233288857708808095434972157113588997360387474193002881963120889 : ℚ) / 13041309919110141310999687436701945173794870669180754593067451438487261560492534844620800 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor08_first_moment_before"
  err.flush

theorem factor08_first_moment :
    prefixMoment (8 : Fin 10) 1 = 1 - meansOf row (8 : Fin 10) / topsOf row (8 : Fin 10) := by
  rw [factor08_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor08_gap_before"
  err.flush

theorem factor08_gap_value :
    gapEvaluator (prefixMoment (8 : Fin 10)) = (254695353254434285466103761247009754574435636197246866645570704313113054161117875365067876483688290464331309615252833 : ℚ) / 328099876348228392492733033734178345563002475089787262438973689148574695872269775249192871166314878008557568000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor08_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor08_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor08_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor
-- END DONOR MomentFactor08

-- BEGIN DONOR MomentFactor09
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row010
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor09_moment1_before"
  err.flush

theorem factor09_moment1 : prefixMoment (9 : Fin 10) 1 = (330447475883021173 : ℚ) / 1457615969791803360 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor09_moment2_before"
  err.flush

theorem factor09_moment2 : prefixMoment (9 : Fin 10) 2 = (796273119142057644603947680861 : ℚ) / 15274471819559886579717534532608 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor09_moment3_before"
  err.flush

theorem factor09_moment3 : prefixMoment (9 : Fin 10) 3 = (883054715489849927831502351601177527049631 : ℚ) / 72755629803523864318343550999387689201467392 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor09_moment4_before"
  err.flush

theorem factor09_moment4 : prefixMoment (9 : Fin 10) 4 = (347886311993368385107183277573112098885935303992283495 : ℚ) / 121761120402629909956241461157855731160527404621697646592 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor09_moment5_before"
  err.flush

theorem factor09_moment5 : prefixMoment (9 : Fin 10) 5 = (4436311383870896623412861980463199430103514002817692135869344571729 : ℚ) / 6531019292467409032345940584149994783226528991349551166597141012414464 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor09_moment6_before"
  err.flush

theorem factor09_moment6 : prefixMoment (9 : Fin 10) 6 = (582977875138230346222733998771825861572872535084464979780683556323588030844138413 : ℚ) / 3577496437323885696205485791089096251104100193751900014243727049095710632468692336640 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor09_first_moment_before"
  err.flush

theorem factor09_first_moment :
    prefixMoment (9 : Fin 10) 1 = 1 - meansOf row (9 : Fin 10) / topsOf row (9 : Fin 10) := by
  rw [factor09_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor09_gap_before"
  err.flush

theorem factor09_gap_value :
    gapEvaluator (prefixMoment (9 : Fin 10)) = (3482821102556734598993624196139110678597773153898557152614016483784520906479404754929748005805749672473401341 : ℚ) / 5760285841235976742505891740147763378728154803956547171581605079576197962653925085782866691267456518429081600000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor09_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor09_saved_Q80_before"
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
  err.putStrLn "P26_CELL01_ROW010_MOMENT factor09_complete"
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

end ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor
-- END DONOR MomentFactor09

-- BEGIN DONOR PrefixFloorChecks
/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! All five original floor obligations for the actual cell01 row10, expressed
through the existing finite prefix evaluator. The old two equalities are
reused. Both Q80 bounds remain explicit, and the saved new field is the
maximum of the exact old and new Q96 evaluations. The separate bridge to
the original rationalMoment still requires its own acceptance. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row010
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_FLOOR first_moments_before"
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
  err.putStrLn "P26_CELL01_ROW010_FLOOR total_Q80_before"
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
    totalLowerQ80 prefixMoment = (7574555348555475970729 : ℚ) / (2 : ℚ)^80 := by
  have h : (∑ j : Fin 10, momentRow.factorFloorsQ80[j.val]! : ℤ) = 7574555348555475970729 := by
    decide +kernel
  rw [total_Q80_eq_saved, h]
  norm_num

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW010_FLOOR new_Q96_before"
  err.flush

theorem new_Q96_value :
    newFloorQ96 (massOf row) (meansOf row) prefixMoment = 3741572189521011558 := by
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
  err.putStrLn "P26_CELL01_ROW010_FLOOR complete"
  err.flush

#print axioms all_first_moments
#print axioms all_saved_Q80
#print axioms all_Q80_bounds
#print axioms total_Q80_eq_saved
#print axioms total_Q80_value
#print axioms new_Q96_value
#print axioms saved_new_Q96_max
#print axioms prefix_floor_checks

end ImbalancedChen.P2OriginalSaving19Cell01Row010MomentFloor
-- END DONOR PrefixFloorChecks
