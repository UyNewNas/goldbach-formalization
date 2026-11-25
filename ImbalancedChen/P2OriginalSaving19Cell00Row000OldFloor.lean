import ImbalancedChen.P2OriginalSaving19Cell00Row000Arithmetic
import ImbalancedChen.P2OriginalSaving19Moment00Shape

/-! The actual moment row0 old floor is the actual geometry row0 Jensen
floor and the same original exact Q96 arithmetic. The ten Q80 fields and
the new Q96 field are not certified by these old-floor equalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell00Row000

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open P2OriginalSaving19Archive
open P2OriginalSaving19Moment00Decoding
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

noncomputable def momentRow : MomentRecord :=
  momentConcrete00.rows[(0 : Fin 56).val]'(P2OriginalSaving19Moment00Shape.row_bound 0)

theorem raw_moment_row_eq : momentConcrete00.rows[0]! = momentRow :=
  P2OriginalSaving19Moment00Shape.row_lookup_no_fallback (0 : Fin 56)

theorem moment_row_eq : momentRow = momentTypedRecord000 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_ROW000_OLD_FLOOR before_original_moment_geometry_binding"
  err.flush

theorem moment_old_matches_geometry : momentRow.oldFloorQ96 = row.jensenFloorQ96 := by
  decide +kernel

theorem moment_old_eq_evaluator :
    momentRow.oldFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) :=
  moment_old_matches_geometry.trans old_floor_eq

theorem actual_moment_old_eq_bounded_evaluator :
    (momentConcrete00.rows[0]!).oldFloorQ96 =
      oldFloorQ96
        (massOf (P2OriginalSaving19Geometry00BoundedAccess.boundedRow (0 : Fin 56)))
        (meansOf (P2OriginalSaving19Geometry00BoundedAccess.boundedRow (0 : Fin 56))) := by
  rw [raw_moment_row_eq, boundedRow_eq]
  exact moment_old_eq_evaluator

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_ROW000_OLD_FLOOR complete"
  err.flush

#print axioms raw_moment_row_eq
#print axioms moment_row_eq
#print axioms moment_old_matches_geometry
#print axioms moment_old_eq_evaluator
#print axioms actual_moment_old_eq_bounded_evaluator

end ImbalancedChen.P2OriginalSaving19Cell00Row000
