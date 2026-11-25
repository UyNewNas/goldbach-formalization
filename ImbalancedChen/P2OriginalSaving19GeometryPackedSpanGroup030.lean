import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00700

/-! Exact compact prefix group 30, bytes [148557,155393).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_175_before_prefix"
  err.flush

theorem compactSpan175_prefix :
    (compactRest00 148557).take 6836 = simplicesBlock007Chars00 := by rfl

theorem compactSpan175_split :
    compactRest00 148557 = simplicesBlock007Chars00 ++ compactRest00 155393 := by
  calc
    compactRest00 148557 =
        (compactRest00 148557).take 6836 ++ (compactRest00 148557).drop 6836 :=
      (List.take_append_drop 6836 (compactRest00 148557)).symm
    _ = simplicesBlock007Chars00 ++ (compactRest00 148557).drop 6836 :=
      congrArg (fun part => part ++ (compactRest00 148557).drop 6836) compactSpan175_prefix
    _ = simplicesBlock007Chars00 ++ compactRest00 155393 :=
      congrArg (fun tail => simplicesBlock007Chars00 ++ tail) (compactRest00_drop 148557 6836)

theorem compactSpan175_rest_eq (htail : geometryChars00.drop 155393 = compactRest00 155393) :
    geometryChars00.drop 148557 = compactRest00 148557 := by
  have hp : (geometryChars00.drop 148557).take 6836 = simplicesBlock007Chars00 :=
    geometryChars00_simplices_block_007_prefix
  exact (list_drop_split_of_prefix geometryChars00 148557 6836 simplicesBlock007Chars00 hp).trans
    ((congrArg (fun tail => simplicesBlock007Chars00 ++ tail) htail).trans compactSpan175_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_175_complete"
  err.flush

theorem group030_rest_eq
    (htail : geometryChars00.drop 155393 = compactRest00 155393) :
    geometryChars00.drop 148557 = compactRest00 148557 := by
  have h175 := compactSpan175_rest_eq htail
  exact h175

#print axioms compactSpan175_prefix
#print axioms compactSpan175_split
#print axioms compactSpan175_rest_eq
#print axioms group030_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
