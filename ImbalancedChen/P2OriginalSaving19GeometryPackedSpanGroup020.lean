import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00100

/-! Exact compact prefix group 20, bytes [68374,78904).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_157_before_prefix"
  err.flush

theorem compactSpan157_prefix :
    (compactRest00 68374).take 10530 = faceLedgerBlock001Chars00 := by rfl

theorem compactSpan157_split :
    compactRest00 68374 = faceLedgerBlock001Chars00 ++ compactRest00 78904 := by
  calc
    compactRest00 68374 =
        (compactRest00 68374).take 10530 ++ (compactRest00 68374).drop 10530 :=
      (List.take_append_drop 10530 (compactRest00 68374)).symm
    _ = faceLedgerBlock001Chars00 ++ (compactRest00 68374).drop 10530 :=
      congrArg (fun part => part ++ (compactRest00 68374).drop 10530) compactSpan157_prefix
    _ = faceLedgerBlock001Chars00 ++ compactRest00 78904 :=
      congrArg (fun tail => faceLedgerBlock001Chars00 ++ tail) (compactRest00_drop 68374 10530)

theorem compactSpan157_rest_eq (htail : geometryChars00.drop 78904 = compactRest00 78904) :
    geometryChars00.drop 68374 = compactRest00 68374 := by
  have hp : (geometryChars00.drop 68374).take 10530 = faceLedgerBlock001Chars00 :=
    geometryChars00_faceLedger_block_001_prefix
  exact (list_drop_split_of_prefix geometryChars00 68374 10530 faceLedgerBlock001Chars00 hp).trans
    ((congrArg (fun tail => faceLedgerBlock001Chars00 ++ tail) htail).trans compactSpan157_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_157_complete"
  err.flush

theorem group020_rest_eq
    (htail : geometryChars00.drop 78904 = compactRest00 78904) :
    geometryChars00.drop 68374 = compactRest00 68374 := by
  have h157 := compactSpan157_rest_eq htail
  exact h157

#print axioms compactSpan157_prefix
#print axioms compactSpan157_split
#print axioms compactSpan157_rest_eq
#print axioms group020_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
