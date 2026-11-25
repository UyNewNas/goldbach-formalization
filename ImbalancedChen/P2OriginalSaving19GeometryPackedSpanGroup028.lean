import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00500

/-! Exact compact prefix group 28, bytes [134456,141795).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_173_before_prefix"
  err.flush

theorem compactSpan173_prefix :
    (compactRest00 134456).take 7339 = simplicesBlock005Chars00 := by rfl

theorem compactSpan173_split :
    compactRest00 134456 = simplicesBlock005Chars00 ++ compactRest00 141795 := by
  calc
    compactRest00 134456 =
        (compactRest00 134456).take 7339 ++ (compactRest00 134456).drop 7339 :=
      (List.take_append_drop 7339 (compactRest00 134456)).symm
    _ = simplicesBlock005Chars00 ++ (compactRest00 134456).drop 7339 :=
      congrArg (fun part => part ++ (compactRest00 134456).drop 7339) compactSpan173_prefix
    _ = simplicesBlock005Chars00 ++ compactRest00 141795 :=
      congrArg (fun tail => simplicesBlock005Chars00 ++ tail) (compactRest00_drop 134456 7339)

theorem compactSpan173_rest_eq (htail : geometryChars00.drop 141795 = compactRest00 141795) :
    geometryChars00.drop 134456 = compactRest00 134456 := by
  have hp : (geometryChars00.drop 134456).take 7339 = simplicesBlock005Chars00 :=
    geometryChars00_simplices_block_005_prefix
  exact (list_drop_split_of_prefix geometryChars00 134456 7339 simplicesBlock005Chars00 hp).trans
    ((congrArg (fun tail => simplicesBlock005Chars00 ++ tail) htail).trans compactSpan173_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_173_complete"
  err.flush

theorem group028_rest_eq
    (htail : geometryChars00.drop 141795 = compactRest00 141795) :
    geometryChars00.drop 134456 = compactRest00 134456 := by
  have h173 := compactSpan173_rest_eq htail
  exact h173

#print axioms compactSpan173_prefix
#print axioms compactSpan173_split
#print axioms compactSpan173_rest_eq
#print axioms group028_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
