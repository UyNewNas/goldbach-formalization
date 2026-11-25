import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01200

/-! Exact compact prefix group 35, bytes [181921,188334).
The original parser certificates remain frozen; this owner only relates input
representations through exact complete character spans. -/
namespace ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_180_before_prefix"
  err.flush

theorem compactSpan180_prefix :
    (compactRest00 181921).take 6413 = simplicesBlock012Chars00 := by rfl

theorem compactSpan180_split :
    compactRest00 181921 = simplicesBlock012Chars00 ++ compactRest00 188334 := by
  calc
    compactRest00 181921 =
        (compactRest00 181921).take 6413 ++ (compactRest00 181921).drop 6413 :=
      (List.take_append_drop 6413 (compactRest00 181921)).symm
    _ = simplicesBlock012Chars00 ++ (compactRest00 181921).drop 6413 :=
      congrArg (fun part => part ++ (compactRest00 181921).drop 6413) compactSpan180_prefix
    _ = simplicesBlock012Chars00 ++ compactRest00 188334 :=
      congrArg (fun tail => simplicesBlock012Chars00 ++ tail) (compactRest00_drop 181921 6413)

theorem compactSpan180_rest_eq (htail : geometryChars00.drop 188334 = compactRest00 188334) :
    geometryChars00.drop 181921 = compactRest00 181921 := by
  have hp : (geometryChars00.drop 181921).take 6413 = simplicesBlock012Chars00 :=
    geometryChars00_simplices_block_012_prefix
  exact (list_drop_split_of_prefix geometryChars00 181921 6413 simplicesBlock012Chars00 hp).trans
    ((congrArg (fun tail => simplicesBlock012Chars00 ++ tail) htail).trans compactSpan180_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_180_complete"
  err.flush

theorem group035_rest_eq
    (htail : geometryChars00.drop 188334 = compactRest00 188334) :
    geometryChars00.drop 181921 = compactRest00 181921 := by
  have h180 := compactSpan180_rest_eq htail
  exact h180

#print axioms compactSpan180_prefix
#print axioms compactSpan180_split
#print axioms compactSpan180_rest_eq
#print axioms group035_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
