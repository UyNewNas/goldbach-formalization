import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00600

/-! Exact compact prefix group 29, bytes [141795,148557).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_174_before_prefix"
  err.flush

theorem compactSpan174_prefix :
    (compactRest00 141795).take 6762 = simplicesBlock006Chars00 := by rfl

theorem compactSpan174_split :
    compactRest00 141795 = simplicesBlock006Chars00 ++ compactRest00 148557 := by
  calc
    compactRest00 141795 =
        (compactRest00 141795).take 6762 ++ (compactRest00 141795).drop 6762 :=
      (List.take_append_drop 6762 (compactRest00 141795)).symm
    _ = simplicesBlock006Chars00 ++ (compactRest00 141795).drop 6762 :=
      congrArg (fun part => part ++ (compactRest00 141795).drop 6762) compactSpan174_prefix
    _ = simplicesBlock006Chars00 ++ compactRest00 148557 :=
      congrArg (fun tail => simplicesBlock006Chars00 ++ tail) (compactRest00_drop 141795 6762)

theorem compactSpan174_rest_eq (htail : geometryChars00.drop 148557 = compactRest00 148557) :
    geometryChars00.drop 141795 = compactRest00 141795 := by
  have hp : (geometryChars00.drop 141795).take 6762 = simplicesBlock006Chars00 :=
    geometryChars00_simplices_block_006_prefix
  exact (list_drop_split_of_prefix geometryChars00 141795 6762 simplicesBlock006Chars00 hp).trans
    ((congrArg (fun tail => simplicesBlock006Chars00 ++ tail) htail).trans compactSpan174_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_174_complete"
  err.flush

theorem group029_rest_eq
    (htail : geometryChars00.drop 148557 = compactRest00 148557) :
    geometryChars00.drop 141795 = compactRest00 141795 := by
  have h174 := compactSpan174_rest_eq htail
  exact h174

#print axioms compactSpan174_prefix
#print axioms compactSpan174_split
#print axioms compactSpan174_rest_eq
#print axioms group029_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
