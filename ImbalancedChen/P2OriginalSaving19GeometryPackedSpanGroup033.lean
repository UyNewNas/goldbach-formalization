import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01000

/-! Exact compact prefix group 33, bytes [168314,175280).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_178_before_prefix"
  err.flush

theorem compactSpan178_prefix :
    (compactRest00 168314).take 6966 = simplicesBlock010Chars00 := by rfl

theorem compactSpan178_split :
    compactRest00 168314 = simplicesBlock010Chars00 ++ compactRest00 175280 := by
  calc
    compactRest00 168314 =
        (compactRest00 168314).take 6966 ++ (compactRest00 168314).drop 6966 :=
      (List.take_append_drop 6966 (compactRest00 168314)).symm
    _ = simplicesBlock010Chars00 ++ (compactRest00 168314).drop 6966 :=
      congrArg (fun part => part ++ (compactRest00 168314).drop 6966) compactSpan178_prefix
    _ = simplicesBlock010Chars00 ++ compactRest00 175280 :=
      congrArg (fun tail => simplicesBlock010Chars00 ++ tail) (compactRest00_drop 168314 6966)

theorem compactSpan178_rest_eq (htail : geometryChars00.drop 175280 = compactRest00 175280) :
    geometryChars00.drop 168314 = compactRest00 168314 := by
  have hp : (geometryChars00.drop 168314).take 6966 = simplicesBlock010Chars00 :=
    geometryChars00_simplices_block_010_prefix
  exact (list_drop_split_of_prefix geometryChars00 168314 6966 simplicesBlock010Chars00 hp).trans
    ((congrArg (fun tail => simplicesBlock010Chars00 ++ tail) htail).trans compactSpan178_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_178_complete"
  err.flush

theorem group033_rest_eq
    (htail : geometryChars00.drop 175280 = compactRest00 175280) :
    geometryChars00.drop 168314 = compactRest00 168314 := by
  have h178 := compactSpan178_rest_eq htail
  exact h178

#print axioms compactSpan178_prefix
#print axioms compactSpan178_split
#print axioms compactSpan178_rest_eq
#print axioms group033_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
