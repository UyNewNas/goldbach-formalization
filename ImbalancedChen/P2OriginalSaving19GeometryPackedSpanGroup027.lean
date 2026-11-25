import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00400

/-! Exact compact prefix group 27, bytes [127502,134456).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_172_before_prefix"
  err.flush

theorem compactSpan172_prefix :
    (compactRest00 127502).take 6954 = simplicesBlock004Chars00 := by rfl

theorem compactSpan172_split :
    compactRest00 127502 = simplicesBlock004Chars00 ++ compactRest00 134456 := by
  calc
    compactRest00 127502 =
        (compactRest00 127502).take 6954 ++ (compactRest00 127502).drop 6954 :=
      (List.take_append_drop 6954 (compactRest00 127502)).symm
    _ = simplicesBlock004Chars00 ++ (compactRest00 127502).drop 6954 :=
      congrArg (fun part => part ++ (compactRest00 127502).drop 6954) compactSpan172_prefix
    _ = simplicesBlock004Chars00 ++ compactRest00 134456 :=
      congrArg (fun tail => simplicesBlock004Chars00 ++ tail) (compactRest00_drop 127502 6954)

theorem compactSpan172_rest_eq (htail : geometryChars00.drop 134456 = compactRest00 134456) :
    geometryChars00.drop 127502 = compactRest00 127502 := by
  have hp : (geometryChars00.drop 127502).take 6954 = simplicesBlock004Chars00 :=
    geometryChars00_simplices_block_004_prefix
  exact (list_drop_split_of_prefix geometryChars00 127502 6954 simplicesBlock004Chars00 hp).trans
    ((congrArg (fun tail => simplicesBlock004Chars00 ++ tail) htail).trans compactSpan172_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_172_complete"
  err.flush

theorem group027_rest_eq
    (htail : geometryChars00.drop 134456 = compactRest00 134456) :
    geometryChars00.drop 127502 = compactRest00 127502 := by
  have h172 := compactSpan172_rest_eq htail
  exact h172

#print axioms compactSpan172_prefix
#print axioms compactSpan172_split
#print axioms compactSpan172_rest_eq
#print axioms group027_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
