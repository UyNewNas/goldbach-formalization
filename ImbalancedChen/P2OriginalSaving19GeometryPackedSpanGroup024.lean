import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00100

/-! Exact compact prefix group 24, bytes [107368,114185).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_169_before_prefix"
  err.flush

theorem compactSpan169_prefix :
    (compactRest00 107368).take 6817 = simplicesBlock001Chars00 := by rfl

theorem compactSpan169_split :
    compactRest00 107368 = simplicesBlock001Chars00 ++ compactRest00 114185 := by
  calc
    compactRest00 107368 =
        (compactRest00 107368).take 6817 ++ (compactRest00 107368).drop 6817 :=
      (List.take_append_drop 6817 (compactRest00 107368)).symm
    _ = simplicesBlock001Chars00 ++ (compactRest00 107368).drop 6817 :=
      congrArg (fun part => part ++ (compactRest00 107368).drop 6817) compactSpan169_prefix
    _ = simplicesBlock001Chars00 ++ compactRest00 114185 :=
      congrArg (fun tail => simplicesBlock001Chars00 ++ tail) (compactRest00_drop 107368 6817)

theorem compactSpan169_rest_eq (htail : geometryChars00.drop 114185 = compactRest00 114185) :
    geometryChars00.drop 107368 = compactRest00 107368 := by
  have hp : (geometryChars00.drop 107368).take 6817 = simplicesBlock001Chars00 :=
    geometryChars00_simplices_block_001_prefix
  exact (list_drop_split_of_prefix geometryChars00 107368 6817 simplicesBlock001Chars00 hp).trans
    ((congrArg (fun tail => simplicesBlock001Chars00 ++ tail) htail).trans compactSpan169_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_169_complete"
  err.flush

theorem group024_rest_eq
    (htail : geometryChars00.drop 114185 = compactRest00 114185) :
    geometryChars00.drop 107368 = compactRest00 107368 := by
  have h169 := compactSpan169_rest_eq htail
  exact h169

#print axioms compactSpan169_prefix
#print axioms compactSpan169_split
#print axioms compactSpan169_rest_eq
#print axioms group024_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
