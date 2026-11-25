import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00800

/-! Exact compact prefix group 31, bytes [155393,161921).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_176_before_prefix"
  err.flush

theorem compactSpan176_prefix :
    (compactRest00 155393).take 6528 = simplicesBlock008Chars00 := by rfl

theorem compactSpan176_split :
    compactRest00 155393 = simplicesBlock008Chars00 ++ compactRest00 161921 := by
  calc
    compactRest00 155393 =
        (compactRest00 155393).take 6528 ++ (compactRest00 155393).drop 6528 :=
      (List.take_append_drop 6528 (compactRest00 155393)).symm
    _ = simplicesBlock008Chars00 ++ (compactRest00 155393).drop 6528 :=
      congrArg (fun part => part ++ (compactRest00 155393).drop 6528) compactSpan176_prefix
    _ = simplicesBlock008Chars00 ++ compactRest00 161921 :=
      congrArg (fun tail => simplicesBlock008Chars00 ++ tail) (compactRest00_drop 155393 6528)

theorem compactSpan176_rest_eq (htail : geometryChars00.drop 161921 = compactRest00 161921) :
    geometryChars00.drop 155393 = compactRest00 155393 := by
  have hp : (geometryChars00.drop 155393).take 6528 = simplicesBlock008Chars00 :=
    geometryChars00_simplices_block_008_prefix
  exact (list_drop_split_of_prefix geometryChars00 155393 6528 simplicesBlock008Chars00 hp).trans
    ((congrArg (fun tail => simplicesBlock008Chars00 ++ tail) htail).trans compactSpan176_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_176_complete"
  err.flush

theorem group031_rest_eq
    (htail : geometryChars00.drop 161921 = compactRest00 161921) :
    geometryChars00.drop 155393 = compactRest00 155393 := by
  have h176 := compactSpan176_rest_eq htail
  exact h176

#print axioms compactSpan176_prefix
#print axioms compactSpan176_split
#print axioms compactSpan176_rest_eq
#print axioms group031_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
