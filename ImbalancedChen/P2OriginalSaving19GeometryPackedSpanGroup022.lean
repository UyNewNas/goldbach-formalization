import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00500
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00600
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00700
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00800
import ImbalancedChen.P2OriginalSaving19FaceLedgerField00
import ImbalancedChen.P2OriginalSaving19SimplicesField00
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00000

/-! Exact compact prefix group 22, bytes [89436,100434).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_161_before_prefix"
  err.flush

theorem compactSpan161_prefix :
    (compactRest00 89436).take 4834 = faceLedgerBlock005Chars00 := by rfl

theorem compactSpan161_split :
    compactRest00 89436 = faceLedgerBlock005Chars00 ++ compactRest00 94270 := by
  calc
    compactRest00 89436 =
        (compactRest00 89436).take 4834 ++ (compactRest00 89436).drop 4834 :=
      (List.take_append_drop 4834 (compactRest00 89436)).symm
    _ = faceLedgerBlock005Chars00 ++ (compactRest00 89436).drop 4834 :=
      congrArg (fun part => part ++ (compactRest00 89436).drop 4834) compactSpan161_prefix
    _ = faceLedgerBlock005Chars00 ++ compactRest00 94270 :=
      congrArg (fun tail => faceLedgerBlock005Chars00 ++ tail) (compactRest00_drop 89436 4834)

theorem compactSpan161_rest_eq (htail : geometryChars00.drop 94270 = compactRest00 94270) :
    geometryChars00.drop 89436 = compactRest00 89436 := by
  have hp : (geometryChars00.drop 89436).take 4834 = faceLedgerBlock005Chars00 :=
    geometryChars00_faceLedger_block_005_prefix
  exact (list_drop_split_of_prefix geometryChars00 89436 4834 faceLedgerBlock005Chars00 hp).trans
    ((congrArg (fun tail => faceLedgerBlock005Chars00 ++ tail) htail).trans compactSpan161_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_161_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_162_before_prefix"
  err.flush

theorem compactSpan162_prefix :
    (compactRest00 94270).take 3411 = faceLedgerBlock006Chars00 := by rfl

theorem compactSpan162_split :
    compactRest00 94270 = faceLedgerBlock006Chars00 ++ compactRest00 97681 := by
  calc
    compactRest00 94270 =
        (compactRest00 94270).take 3411 ++ (compactRest00 94270).drop 3411 :=
      (List.take_append_drop 3411 (compactRest00 94270)).symm
    _ = faceLedgerBlock006Chars00 ++ (compactRest00 94270).drop 3411 :=
      congrArg (fun part => part ++ (compactRest00 94270).drop 3411) compactSpan162_prefix
    _ = faceLedgerBlock006Chars00 ++ compactRest00 97681 :=
      congrArg (fun tail => faceLedgerBlock006Chars00 ++ tail) (compactRest00_drop 94270 3411)

theorem compactSpan162_rest_eq (htail : geometryChars00.drop 97681 = compactRest00 97681) :
    geometryChars00.drop 94270 = compactRest00 94270 := by
  have hp : (geometryChars00.drop 94270).take 3411 = faceLedgerBlock006Chars00 :=
    geometryChars00_faceLedger_block_006_prefix
  exact (list_drop_split_of_prefix geometryChars00 94270 3411 faceLedgerBlock006Chars00 hp).trans
    ((congrArg (fun tail => faceLedgerBlock006Chars00 ++ tail) htail).trans compactSpan162_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_162_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_163_before_prefix"
  err.flush

theorem compactSpan163_prefix :
    (compactRest00 97681).take 2490 = faceLedgerBlock007Chars00 := by rfl

theorem compactSpan163_split :
    compactRest00 97681 = faceLedgerBlock007Chars00 ++ compactRest00 100171 := by
  calc
    compactRest00 97681 =
        (compactRest00 97681).take 2490 ++ (compactRest00 97681).drop 2490 :=
      (List.take_append_drop 2490 (compactRest00 97681)).symm
    _ = faceLedgerBlock007Chars00 ++ (compactRest00 97681).drop 2490 :=
      congrArg (fun part => part ++ (compactRest00 97681).drop 2490) compactSpan163_prefix
    _ = faceLedgerBlock007Chars00 ++ compactRest00 100171 :=
      congrArg (fun tail => faceLedgerBlock007Chars00 ++ tail) (compactRest00_drop 97681 2490)

theorem compactSpan163_rest_eq (htail : geometryChars00.drop 100171 = compactRest00 100171) :
    geometryChars00.drop 97681 = compactRest00 97681 := by
  have hp : (geometryChars00.drop 97681).take 2490 = faceLedgerBlock007Chars00 :=
    geometryChars00_faceLedger_block_007_prefix
  exact (list_drop_split_of_prefix geometryChars00 97681 2490 faceLedgerBlock007Chars00 hp).trans
    ((congrArg (fun tail => faceLedgerBlock007Chars00 ++ tail) htail).trans compactSpan163_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_163_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_164_before_prefix"
  err.flush

theorem compactSpan164_prefix :
    (compactRest00 100171).take 244 = faceLedgerBlock008Chars00 := by rfl

theorem compactSpan164_split :
    compactRest00 100171 = faceLedgerBlock008Chars00 ++ compactRest00 100415 := by
  calc
    compactRest00 100171 =
        (compactRest00 100171).take 244 ++ (compactRest00 100171).drop 244 :=
      (List.take_append_drop 244 (compactRest00 100171)).symm
    _ = faceLedgerBlock008Chars00 ++ (compactRest00 100171).drop 244 :=
      congrArg (fun part => part ++ (compactRest00 100171).drop 244) compactSpan164_prefix
    _ = faceLedgerBlock008Chars00 ++ compactRest00 100415 :=
      congrArg (fun tail => faceLedgerBlock008Chars00 ++ tail) (compactRest00_drop 100171 244)

theorem compactSpan164_rest_eq (htail : geometryChars00.drop 100415 = compactRest00 100415) :
    geometryChars00.drop 100171 = compactRest00 100171 := by
  have hp : (geometryChars00.drop 100171).take 244 = faceLedgerBlock008Chars00 :=
    geometryChars00_faceLedger_block_008_prefix
  exact (list_drop_split_of_prefix geometryChars00 100171 244 faceLedgerBlock008Chars00 hp).trans
    ((congrArg (fun tail => faceLedgerBlock008Chars00 ++ tail) htail).trans compactSpan164_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_164_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_165_before_prefix"
  err.flush

theorem compactSpan165_prefix :
    (compactRest00 100415).take 1 = faceLedgerSeparatorChars00 := by rfl

theorem compactSpan165_split :
    compactRest00 100415 = faceLedgerSeparatorChars00 ++ compactRest00 100416 := by
  calc
    compactRest00 100415 =
        (compactRest00 100415).take 1 ++ (compactRest00 100415).drop 1 :=
      (List.take_append_drop 1 (compactRest00 100415)).symm
    _ = faceLedgerSeparatorChars00 ++ (compactRest00 100415).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 100415).drop 1) compactSpan165_prefix
    _ = faceLedgerSeparatorChars00 ++ compactRest00 100416 :=
      congrArg (fun tail => faceLedgerSeparatorChars00 ++ tail) (compactRest00_drop 100415 1)

theorem compactSpan165_rest_eq (htail : geometryChars00.drop 100416 = compactRest00 100416) :
    geometryChars00.drop 100415 = compactRest00 100415 := by
  have hp : (geometryChars00.drop 100415).take 1 = faceLedgerSeparatorChars00 :=
    geometryChars00_faceLedger_separator_prefix
  exact (list_drop_split_of_prefix geometryChars00 100415 1 faceLedgerSeparatorChars00 hp).trans
    ((congrArg (fun tail => faceLedgerSeparatorChars00 ++ tail) htail).trans compactSpan165_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_165_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_166_before_prefix"
  err.flush

theorem compactSpan166_prefix :
    (compactRest00 100416).take 17 = simplicesHeaderChars00 := by rfl

theorem compactSpan166_split :
    compactRest00 100416 = simplicesHeaderChars00 ++ compactRest00 100433 := by
  calc
    compactRest00 100416 =
        (compactRest00 100416).take 17 ++ (compactRest00 100416).drop 17 :=
      (List.take_append_drop 17 (compactRest00 100416)).symm
    _ = simplicesHeaderChars00 ++ (compactRest00 100416).drop 17 :=
      congrArg (fun part => part ++ (compactRest00 100416).drop 17) compactSpan166_prefix
    _ = simplicesHeaderChars00 ++ compactRest00 100433 :=
      congrArg (fun tail => simplicesHeaderChars00 ++ tail) (compactRest00_drop 100416 17)

theorem compactSpan166_rest_eq (htail : geometryChars00.drop 100433 = compactRest00 100433) :
    geometryChars00.drop 100416 = compactRest00 100416 := by
  have hp : (geometryChars00.drop 100416).take 17 = simplicesHeaderChars00 :=
    geometryChars00_simplices_header_prefix
  exact (list_drop_split_of_prefix geometryChars00 100416 17 simplicesHeaderChars00 hp).trans
    ((congrArg (fun tail => simplicesHeaderChars00 ++ tail) htail).trans compactSpan166_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_166_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_167_before_prefix"
  err.flush

theorem compactSpan167_prefix :
    (compactRest00 100433).take 1 = simplicesOpenChars00 := by rfl

theorem compactSpan167_split :
    compactRest00 100433 = simplicesOpenChars00 ++ compactRest00 100434 := by
  calc
    compactRest00 100433 =
        (compactRest00 100433).take 1 ++ (compactRest00 100433).drop 1 :=
      (List.take_append_drop 1 (compactRest00 100433)).symm
    _ = simplicesOpenChars00 ++ (compactRest00 100433).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 100433).drop 1) compactSpan167_prefix
    _ = simplicesOpenChars00 ++ compactRest00 100434 :=
      congrArg (fun tail => simplicesOpenChars00 ++ tail) (compactRest00_drop 100433 1)

theorem compactSpan167_rest_eq (htail : geometryChars00.drop 100434 = compactRest00 100434) :
    geometryChars00.drop 100433 = compactRest00 100433 := by
  have hp : (geometryChars00.drop 100433).take 1 = simplicesOpenChars00 :=
    geometryChars00_simplices_open_prefix
  exact (list_drop_split_of_prefix geometryChars00 100433 1 simplicesOpenChars00 hp).trans
    ((congrArg (fun tail => simplicesOpenChars00 ++ tail) htail).trans compactSpan167_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_167_complete"
  err.flush

theorem group022_rest_eq
    (htail : geometryChars00.drop 100434 = compactRest00 100434) :
    geometryChars00.drop 89436 = compactRest00 89436 := by
  have h167 := compactSpan167_rest_eq htail
  have h166 := compactSpan166_rest_eq h167
  have h165 := compactSpan165_rest_eq h166
  have h164 := compactSpan164_rest_eq h165
  have h163 := compactSpan163_rest_eq h164
  have h162 := compactSpan162_rest_eq h163
  have h161 := compactSpan161_rest_eq h162
  exact h161

#print axioms compactSpan161_prefix
#print axioms compactSpan161_split
#print axioms compactSpan161_rest_eq
#print axioms compactSpan162_prefix
#print axioms compactSpan162_split
#print axioms compactSpan162_rest_eq
#print axioms compactSpan163_prefix
#print axioms compactSpan163_split
#print axioms compactSpan163_rest_eq
#print axioms compactSpan164_prefix
#print axioms compactSpan164_split
#print axioms compactSpan164_rest_eq
#print axioms compactSpan165_prefix
#print axioms compactSpan165_split
#print axioms compactSpan165_rest_eq
#print axioms compactSpan166_prefix
#print axioms compactSpan166_split
#print axioms compactSpan166_rest_eq
#print axioms compactSpan167_prefix
#print axioms compactSpan167_split
#print axioms compactSpan167_rest_eq
#print axioms group022_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
