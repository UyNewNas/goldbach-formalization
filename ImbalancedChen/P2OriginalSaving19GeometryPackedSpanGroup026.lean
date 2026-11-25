import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00300

/-! Exact compact prefix group 26, bytes [120670,127502).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_171_before_prefix"
  err.flush

theorem compactSpan171_prefix :
    (compactRest00 120670).take 6832 = simplicesBlock003Chars00 := by rfl

theorem compactSpan171_split :
    compactRest00 120670 = simplicesBlock003Chars00 ++ compactRest00 127502 := by
  calc
    compactRest00 120670 =
        (compactRest00 120670).take 6832 ++ (compactRest00 120670).drop 6832 :=
      (List.take_append_drop 6832 (compactRest00 120670)).symm
    _ = simplicesBlock003Chars00 ++ (compactRest00 120670).drop 6832 :=
      congrArg (fun part => part ++ (compactRest00 120670).drop 6832) compactSpan171_prefix
    _ = simplicesBlock003Chars00 ++ compactRest00 127502 :=
      congrArg (fun tail => simplicesBlock003Chars00 ++ tail) (compactRest00_drop 120670 6832)

theorem compactSpan171_rest_eq (htail : geometryChars00.drop 127502 = compactRest00 127502) :
    geometryChars00.drop 120670 = compactRest00 120670 := by
  have hp : (geometryChars00.drop 120670).take 6832 = simplicesBlock003Chars00 :=
    geometryChars00_simplices_block_003_prefix
  exact (list_drop_split_of_prefix geometryChars00 120670 6832 simplicesBlock003Chars00 hp).trans
    ((congrArg (fun tail => simplicesBlock003Chars00 ++ tail) htail).trans compactSpan171_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_171_complete"
  err.flush

theorem group026_rest_eq
    (htail : geometryChars00.drop 127502 = compactRest00 127502) :
    geometryChars00.drop 120670 = compactRest00 120670 := by
  have h171 := compactSpan171_rest_eq htail
  exact h171

#print axioms compactSpan171_prefix
#print axioms compactSpan171_split
#print axioms compactSpan171_rest_eq
#print axioms group026_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
