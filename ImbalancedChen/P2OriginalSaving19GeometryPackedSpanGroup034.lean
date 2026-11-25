import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01100

/-! Exact compact prefix group 34, bytes [175280,181921).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_179_before_prefix"
  err.flush

theorem compactSpan179_prefix :
    (compactRest00 175280).take 6641 = simplicesBlock011Chars00 := by rfl

theorem compactSpan179_split :
    compactRest00 175280 = simplicesBlock011Chars00 ++ compactRest00 181921 := by
  calc
    compactRest00 175280 =
        (compactRest00 175280).take 6641 ++ (compactRest00 175280).drop 6641 :=
      (List.take_append_drop 6641 (compactRest00 175280)).symm
    _ = simplicesBlock011Chars00 ++ (compactRest00 175280).drop 6641 :=
      congrArg (fun part => part ++ (compactRest00 175280).drop 6641) compactSpan179_prefix
    _ = simplicesBlock011Chars00 ++ compactRest00 181921 :=
      congrArg (fun tail => simplicesBlock011Chars00 ++ tail) (compactRest00_drop 175280 6641)

theorem compactSpan179_rest_eq (htail : geometryChars00.drop 181921 = compactRest00 181921) :
    geometryChars00.drop 175280 = compactRest00 175280 := by
  have hp : (geometryChars00.drop 175280).take 6641 = simplicesBlock011Chars00 :=
    geometryChars00_simplices_block_011_prefix
  exact (list_drop_split_of_prefix geometryChars00 175280 6641 simplicesBlock011Chars00 hp).trans
    ((congrArg (fun tail => simplicesBlock011Chars00 ++ tail) htail).trans compactSpan179_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_179_complete"
  err.flush

theorem group034_rest_eq
    (htail : geometryChars00.drop 181921 = compactRest00 181921) :
    geometryChars00.drop 175280 = compactRest00 175280 := by
  have h179 := compactSpan179_rest_eq htail
  exact h179

#print axioms compactSpan179_prefix
#print axioms compactSpan179_split
#print axioms compactSpan179_rest_eq
#print axioms group034_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
