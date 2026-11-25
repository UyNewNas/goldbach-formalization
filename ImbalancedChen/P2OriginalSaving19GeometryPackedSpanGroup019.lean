import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19FacetVerticesArrayBlock00100
import ImbalancedChen.P2OriginalSaving19FacetVerticesField00
import ImbalancedChen.P2OriginalSaving19FaceLedgerField00
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00000

/-! Exact compact prefix group 19, bytes [64408,68374).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_152_before_prefix"
  err.flush

theorem compactSpan152_prefix :
    (compactRest00 64408).take 812 = facetVerticesBlock001Chars00 := by rfl

theorem compactSpan152_split :
    compactRest00 64408 = facetVerticesBlock001Chars00 ++ compactRest00 65220 := by
  calc
    compactRest00 64408 =
        (compactRest00 64408).take 812 ++ (compactRest00 64408).drop 812 :=
      (List.take_append_drop 812 (compactRest00 64408)).symm
    _ = facetVerticesBlock001Chars00 ++ (compactRest00 64408).drop 812 :=
      congrArg (fun part => part ++ (compactRest00 64408).drop 812) compactSpan152_prefix
    _ = facetVerticesBlock001Chars00 ++ compactRest00 65220 :=
      congrArg (fun tail => facetVerticesBlock001Chars00 ++ tail) (compactRest00_drop 64408 812)

theorem compactSpan152_rest_eq (htail : geometryChars00.drop 65220 = compactRest00 65220) :
    geometryChars00.drop 64408 = compactRest00 64408 := by
  have hp : (geometryChars00.drop 64408).take 812 = facetVerticesBlock001Chars00 :=
    geometryChars00_facetVertices_block_001_prefix
  exact (list_drop_split_of_prefix geometryChars00 64408 812 facetVerticesBlock001Chars00 hp).trans
    ((congrArg (fun tail => facetVerticesBlock001Chars00 ++ tail) htail).trans compactSpan152_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_152_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_153_before_prefix"
  err.flush

theorem compactSpan153_prefix :
    (compactRest00 65220).take 1 = facetVerticesSeparatorChars00 := by rfl

theorem compactSpan153_split :
    compactRest00 65220 = facetVerticesSeparatorChars00 ++ compactRest00 65221 := by
  calc
    compactRest00 65220 =
        (compactRest00 65220).take 1 ++ (compactRest00 65220).drop 1 :=
      (List.take_append_drop 1 (compactRest00 65220)).symm
    _ = facetVerticesSeparatorChars00 ++ (compactRest00 65220).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 65220).drop 1) compactSpan153_prefix
    _ = facetVerticesSeparatorChars00 ++ compactRest00 65221 :=
      congrArg (fun tail => facetVerticesSeparatorChars00 ++ tail) (compactRest00_drop 65220 1)

theorem compactSpan153_rest_eq (htail : geometryChars00.drop 65221 = compactRest00 65221) :
    geometryChars00.drop 65220 = compactRest00 65220 := by
  have hp : (geometryChars00.drop 65220).take 1 = facetVerticesSeparatorChars00 :=
    geometryChars00_facetVertices_separator_prefix
  exact (list_drop_split_of_prefix geometryChars00 65220 1 facetVerticesSeparatorChars00 hp).trans
    ((congrArg (fun tail => facetVerticesSeparatorChars00 ++ tail) htail).trans compactSpan153_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_153_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_154_before_prefix"
  err.flush

theorem compactSpan154_prefix :
    (compactRest00 65221).take 19 = faceLedgerHeaderChars00 := by rfl

theorem compactSpan154_split :
    compactRest00 65221 = faceLedgerHeaderChars00 ++ compactRest00 65240 := by
  calc
    compactRest00 65221 =
        (compactRest00 65221).take 19 ++ (compactRest00 65221).drop 19 :=
      (List.take_append_drop 19 (compactRest00 65221)).symm
    _ = faceLedgerHeaderChars00 ++ (compactRest00 65221).drop 19 :=
      congrArg (fun part => part ++ (compactRest00 65221).drop 19) compactSpan154_prefix
    _ = faceLedgerHeaderChars00 ++ compactRest00 65240 :=
      congrArg (fun tail => faceLedgerHeaderChars00 ++ tail) (compactRest00_drop 65221 19)

theorem compactSpan154_rest_eq (htail : geometryChars00.drop 65240 = compactRest00 65240) :
    geometryChars00.drop 65221 = compactRest00 65221 := by
  have hp : (geometryChars00.drop 65221).take 19 = faceLedgerHeaderChars00 :=
    geometryChars00_faceLedger_header_prefix
  exact (list_drop_split_of_prefix geometryChars00 65221 19 faceLedgerHeaderChars00 hp).trans
    ((congrArg (fun tail => faceLedgerHeaderChars00 ++ tail) htail).trans compactSpan154_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_154_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_155_before_prefix"
  err.flush

theorem compactSpan155_prefix :
    (compactRest00 65240).take 1 = faceLedgerOpenChars00 := by rfl

theorem compactSpan155_split :
    compactRest00 65240 = faceLedgerOpenChars00 ++ compactRest00 65241 := by
  calc
    compactRest00 65240 =
        (compactRest00 65240).take 1 ++ (compactRest00 65240).drop 1 :=
      (List.take_append_drop 1 (compactRest00 65240)).symm
    _ = faceLedgerOpenChars00 ++ (compactRest00 65240).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 65240).drop 1) compactSpan155_prefix
    _ = faceLedgerOpenChars00 ++ compactRest00 65241 :=
      congrArg (fun tail => faceLedgerOpenChars00 ++ tail) (compactRest00_drop 65240 1)

theorem compactSpan155_rest_eq (htail : geometryChars00.drop 65241 = compactRest00 65241) :
    geometryChars00.drop 65240 = compactRest00 65240 := by
  have hp : (geometryChars00.drop 65240).take 1 = faceLedgerOpenChars00 :=
    geometryChars00_faceLedger_open_prefix
  exact (list_drop_split_of_prefix geometryChars00 65240 1 faceLedgerOpenChars00 hp).trans
    ((congrArg (fun tail => faceLedgerOpenChars00 ++ tail) htail).trans compactSpan155_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_155_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_156_before_prefix"
  err.flush

theorem compactSpan156_prefix :
    (compactRest00 65241).take 3133 = faceLedgerBlock000Chars00 := by rfl

theorem compactSpan156_split :
    compactRest00 65241 = faceLedgerBlock000Chars00 ++ compactRest00 68374 := by
  calc
    compactRest00 65241 =
        (compactRest00 65241).take 3133 ++ (compactRest00 65241).drop 3133 :=
      (List.take_append_drop 3133 (compactRest00 65241)).symm
    _ = faceLedgerBlock000Chars00 ++ (compactRest00 65241).drop 3133 :=
      congrArg (fun part => part ++ (compactRest00 65241).drop 3133) compactSpan156_prefix
    _ = faceLedgerBlock000Chars00 ++ compactRest00 68374 :=
      congrArg (fun tail => faceLedgerBlock000Chars00 ++ tail) (compactRest00_drop 65241 3133)

theorem compactSpan156_rest_eq (htail : geometryChars00.drop 68374 = compactRest00 68374) :
    geometryChars00.drop 65241 = compactRest00 65241 := by
  have hp : (geometryChars00.drop 65241).take 3133 = faceLedgerBlock000Chars00 :=
    geometryChars00_faceLedger_block_000_prefix
  exact (list_drop_split_of_prefix geometryChars00 65241 3133 faceLedgerBlock000Chars00 hp).trans
    ((congrArg (fun tail => faceLedgerBlock000Chars00 ++ tail) htail).trans compactSpan156_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_156_complete"
  err.flush

theorem group019_rest_eq
    (htail : geometryChars00.drop 68374 = compactRest00 68374) :
    geometryChars00.drop 64408 = compactRest00 64408 := by
  have h156 := compactSpan156_rest_eq htail
  have h155 := compactSpan155_rest_eq h156
  have h154 := compactSpan154_rest_eq h155
  have h153 := compactSpan153_rest_eq h154
  have h152 := compactSpan152_rest_eq h153
  exact h152

#print axioms compactSpan152_prefix
#print axioms compactSpan152_split
#print axioms compactSpan152_rest_eq
#print axioms compactSpan153_prefix
#print axioms compactSpan153_split
#print axioms compactSpan153_rest_eq
#print axioms compactSpan154_prefix
#print axioms compactSpan154_split
#print axioms compactSpan154_rest_eq
#print axioms compactSpan155_prefix
#print axioms compactSpan155_split
#print axioms compactSpan155_rest_eq
#print axioms compactSpan156_prefix
#print axioms compactSpan156_split
#print axioms compactSpan156_rest_eq
#print axioms group019_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
