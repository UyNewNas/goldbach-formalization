import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00900

/-! Exact compact prefix group 32, bytes [161921,168314).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_177_before_prefix"
  err.flush

theorem compactSpan177_prefix :
    (compactRest00 161921).take 6393 = simplicesBlock009Chars00 := by rfl

theorem compactSpan177_split :
    compactRest00 161921 = simplicesBlock009Chars00 ++ compactRest00 168314 := by
  calc
    compactRest00 161921 =
        (compactRest00 161921).take 6393 ++ (compactRest00 161921).drop 6393 :=
      (List.take_append_drop 6393 (compactRest00 161921)).symm
    _ = simplicesBlock009Chars00 ++ (compactRest00 161921).drop 6393 :=
      congrArg (fun part => part ++ (compactRest00 161921).drop 6393) compactSpan177_prefix
    _ = simplicesBlock009Chars00 ++ compactRest00 168314 :=
      congrArg (fun tail => simplicesBlock009Chars00 ++ tail) (compactRest00_drop 161921 6393)

theorem compactSpan177_rest_eq (htail : geometryChars00.drop 168314 = compactRest00 168314) :
    geometryChars00.drop 161921 = compactRest00 161921 := by
  have hp : (geometryChars00.drop 161921).take 6393 = simplicesBlock009Chars00 :=
    geometryChars00_simplices_block_009_prefix
  exact (list_drop_split_of_prefix geometryChars00 161921 6393 simplicesBlock009Chars00 hp).trans
    ((congrArg (fun tail => simplicesBlock009Chars00 ++ tail) htail).trans compactSpan177_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_177_complete"
  err.flush

theorem group032_rest_eq
    (htail : geometryChars00.drop 168314 = compactRest00 168314) :
    geometryChars00.drop 161921 = compactRest00 161921 := by
  have h177 := compactSpan177_rest_eq htail
  exact h177

#print axioms compactSpan177_prefix
#print axioms compactSpan177_split
#print axioms compactSpan177_rest_eq
#print axioms group032_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
