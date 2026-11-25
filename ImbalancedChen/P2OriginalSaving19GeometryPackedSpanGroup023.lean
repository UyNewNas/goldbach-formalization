import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00000

/-! Exact compact prefix group 23, bytes [100434,107368).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_168_before_prefix"
  err.flush

theorem compactSpan168_prefix :
    (compactRest00 100434).take 6934 = simplicesBlock000Chars00 := by rfl

theorem compactSpan168_split :
    compactRest00 100434 = simplicesBlock000Chars00 ++ compactRest00 107368 := by
  calc
    compactRest00 100434 =
        (compactRest00 100434).take 6934 ++ (compactRest00 100434).drop 6934 :=
      (List.take_append_drop 6934 (compactRest00 100434)).symm
    _ = simplicesBlock000Chars00 ++ (compactRest00 100434).drop 6934 :=
      congrArg (fun part => part ++ (compactRest00 100434).drop 6934) compactSpan168_prefix
    _ = simplicesBlock000Chars00 ++ compactRest00 107368 :=
      congrArg (fun tail => simplicesBlock000Chars00 ++ tail) (compactRest00_drop 100434 6934)

theorem compactSpan168_rest_eq (htail : geometryChars00.drop 107368 = compactRest00 107368) :
    geometryChars00.drop 100434 = compactRest00 100434 := by
  have hp : (geometryChars00.drop 100434).take 6934 = simplicesBlock000Chars00 :=
    geometryChars00_simplices_block_000_prefix
  exact (list_drop_split_of_prefix geometryChars00 100434 6934 simplicesBlock000Chars00 hp).trans
    ((congrArg (fun tail => simplicesBlock000Chars00 ++ tail) htail).trans compactSpan168_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_168_complete"
  err.flush

theorem group023_rest_eq
    (htail : geometryChars00.drop 107368 = compactRest00 107368) :
    geometryChars00.drop 100434 = compactRest00 100434 := by
  have h168 := compactSpan168_rest_eq htail
  exact h168

#print axioms compactSpan168_prefix
#print axioms compactSpan168_split
#print axioms compactSpan168_rest_eq
#print axioms group023_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
