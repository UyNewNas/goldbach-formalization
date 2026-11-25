import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00200
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00300
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00400

/-! Exact compact prefix group 21, bytes [78904,89436).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_158_before_prefix"
  err.flush

theorem compactSpan158_prefix :
    (compactRest00 78904).take 5970 = faceLedgerBlock002Chars00 := by rfl

theorem compactSpan158_split :
    compactRest00 78904 = faceLedgerBlock002Chars00 ++ compactRest00 84874 := by
  calc
    compactRest00 78904 =
        (compactRest00 78904).take 5970 ++ (compactRest00 78904).drop 5970 :=
      (List.take_append_drop 5970 (compactRest00 78904)).symm
    _ = faceLedgerBlock002Chars00 ++ (compactRest00 78904).drop 5970 :=
      congrArg (fun part => part ++ (compactRest00 78904).drop 5970) compactSpan158_prefix
    _ = faceLedgerBlock002Chars00 ++ compactRest00 84874 :=
      congrArg (fun tail => faceLedgerBlock002Chars00 ++ tail) (compactRest00_drop 78904 5970)

theorem compactSpan158_rest_eq (htail : geometryChars00.drop 84874 = compactRest00 84874) :
    geometryChars00.drop 78904 = compactRest00 78904 := by
  have hp : (geometryChars00.drop 78904).take 5970 = faceLedgerBlock002Chars00 :=
    geometryChars00_faceLedger_block_002_prefix
  exact (list_drop_split_of_prefix geometryChars00 78904 5970 faceLedgerBlock002Chars00 hp).trans
    ((congrArg (fun tail => faceLedgerBlock002Chars00 ++ tail) htail).trans compactSpan158_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_158_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_159_before_prefix"
  err.flush

theorem compactSpan159_prefix :
    (compactRest00 84874).take 2569 = faceLedgerBlock003Chars00 := by rfl

theorem compactSpan159_split :
    compactRest00 84874 = faceLedgerBlock003Chars00 ++ compactRest00 87443 := by
  calc
    compactRest00 84874 =
        (compactRest00 84874).take 2569 ++ (compactRest00 84874).drop 2569 :=
      (List.take_append_drop 2569 (compactRest00 84874)).symm
    _ = faceLedgerBlock003Chars00 ++ (compactRest00 84874).drop 2569 :=
      congrArg (fun part => part ++ (compactRest00 84874).drop 2569) compactSpan159_prefix
    _ = faceLedgerBlock003Chars00 ++ compactRest00 87443 :=
      congrArg (fun tail => faceLedgerBlock003Chars00 ++ tail) (compactRest00_drop 84874 2569)

theorem compactSpan159_rest_eq (htail : geometryChars00.drop 87443 = compactRest00 87443) :
    geometryChars00.drop 84874 = compactRest00 84874 := by
  have hp : (geometryChars00.drop 84874).take 2569 = faceLedgerBlock003Chars00 :=
    geometryChars00_faceLedger_block_003_prefix
  exact (list_drop_split_of_prefix geometryChars00 84874 2569 faceLedgerBlock003Chars00 hp).trans
    ((congrArg (fun tail => faceLedgerBlock003Chars00 ++ tail) htail).trans compactSpan159_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_159_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_160_before_prefix"
  err.flush

theorem compactSpan160_prefix :
    (compactRest00 87443).take 1993 = faceLedgerBlock004Chars00 := by rfl

theorem compactSpan160_split :
    compactRest00 87443 = faceLedgerBlock004Chars00 ++ compactRest00 89436 := by
  calc
    compactRest00 87443 =
        (compactRest00 87443).take 1993 ++ (compactRest00 87443).drop 1993 :=
      (List.take_append_drop 1993 (compactRest00 87443)).symm
    _ = faceLedgerBlock004Chars00 ++ (compactRest00 87443).drop 1993 :=
      congrArg (fun part => part ++ (compactRest00 87443).drop 1993) compactSpan160_prefix
    _ = faceLedgerBlock004Chars00 ++ compactRest00 89436 :=
      congrArg (fun tail => faceLedgerBlock004Chars00 ++ tail) (compactRest00_drop 87443 1993)

theorem compactSpan160_rest_eq (htail : geometryChars00.drop 89436 = compactRest00 89436) :
    geometryChars00.drop 87443 = compactRest00 87443 := by
  have hp : (geometryChars00.drop 87443).take 1993 = faceLedgerBlock004Chars00 :=
    geometryChars00_faceLedger_block_004_prefix
  exact (list_drop_split_of_prefix geometryChars00 87443 1993 faceLedgerBlock004Chars00 hp).trans
    ((congrArg (fun tail => faceLedgerBlock004Chars00 ++ tail) htail).trans compactSpan160_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_160_complete"
  err.flush

theorem group021_rest_eq
    (htail : geometryChars00.drop 89436 = compactRest00 89436) :
    geometryChars00.drop 78904 = compactRest00 78904 := by
  have h160 := compactSpan160_rest_eq htail
  have h159 := compactSpan159_rest_eq h160
  have h158 := compactSpan158_rest_eq h159
  exact h158

#print axioms compactSpan158_prefix
#print axioms compactSpan158_split
#print axioms compactSpan158_rest_eq
#print axioms compactSpan159_prefix
#print axioms compactSpan159_split
#print axioms compactSpan159_rest_eq
#print axioms compactSpan160_prefix
#print axioms compactSpan160_split
#print axioms compactSpan160_rest_eq
#print axioms group021_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
