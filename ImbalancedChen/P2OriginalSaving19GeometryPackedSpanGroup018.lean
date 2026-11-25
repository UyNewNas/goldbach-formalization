import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19ConstraintMinimaArrayBlock00000
import ImbalancedChen.P2OriginalSaving19ConstraintMinimaArrayBlock00100
import ImbalancedChen.P2OriginalSaving19ConstraintMinimaField00
import ImbalancedChen.P2OriginalSaving19FacetVerticesField00
import ImbalancedChen.P2OriginalSaving19FacetVerticesArrayBlock00000

/-! Exact compact prefix group 18, bytes [61514,64408).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_144_before_prefix"
  err.flush

theorem compactSpan144_prefix :
    (compactRest00 61514).take 365 = constraintMinimaChunk003Chars00 := by rfl

theorem compactSpan144_split :
    compactRest00 61514 = constraintMinimaChunk003Chars00 ++ compactRest00 61879 := by
  calc
    compactRest00 61514 =
        (compactRest00 61514).take 365 ++ (compactRest00 61514).drop 365 :=
      (List.take_append_drop 365 (compactRest00 61514)).symm
    _ = constraintMinimaChunk003Chars00 ++ (compactRest00 61514).drop 365 :=
      congrArg (fun part => part ++ (compactRest00 61514).drop 365) compactSpan144_prefix
    _ = constraintMinimaChunk003Chars00 ++ compactRest00 61879 :=
      congrArg (fun tail => constraintMinimaChunk003Chars00 ++ tail) (compactRest00_drop 61514 365)

theorem compactSpan144_rest_eq (htail : geometryChars00.drop 61879 = compactRest00 61879) :
    geometryChars00.drop 61514 = compactRest00 61514 := by
  have hp : (geometryChars00.drop 61514).take 365 = constraintMinimaChunk003Chars00 :=
    geometryChars00_constraintMinima_chunk_003_prefix
  exact (list_drop_split_of_prefix geometryChars00 61514 365 constraintMinimaChunk003Chars00 hp).trans
    ((congrArg (fun tail => constraintMinimaChunk003Chars00 ++ tail) htail).trans compactSpan144_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_144_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_145_before_prefix"
  err.flush

theorem compactSpan145_prefix :
    (compactRest00 61879).take 363 = constraintMinimaChunk004Chars00 := by rfl

theorem compactSpan145_split :
    compactRest00 61879 = constraintMinimaChunk004Chars00 ++ compactRest00 62242 := by
  calc
    compactRest00 61879 =
        (compactRest00 61879).take 363 ++ (compactRest00 61879).drop 363 :=
      (List.take_append_drop 363 (compactRest00 61879)).symm
    _ = constraintMinimaChunk004Chars00 ++ (compactRest00 61879).drop 363 :=
      congrArg (fun part => part ++ (compactRest00 61879).drop 363) compactSpan145_prefix
    _ = constraintMinimaChunk004Chars00 ++ compactRest00 62242 :=
      congrArg (fun tail => constraintMinimaChunk004Chars00 ++ tail) (compactRest00_drop 61879 363)

theorem compactSpan145_rest_eq (htail : geometryChars00.drop 62242 = compactRest00 62242) :
    geometryChars00.drop 61879 = compactRest00 61879 := by
  have hp : (geometryChars00.drop 61879).take 363 = constraintMinimaChunk004Chars00 :=
    geometryChars00_constraintMinima_chunk_004_prefix
  exact (list_drop_split_of_prefix geometryChars00 61879 363 constraintMinimaChunk004Chars00 hp).trans
    ((congrArg (fun tail => constraintMinimaChunk004Chars00 ++ tail) htail).trans compactSpan145_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_145_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_146_before_prefix"
  err.flush

theorem compactSpan146_prefix :
    (compactRest00 62242).take 382 = constraintMinimaChunk005Chars00 := by rfl

theorem compactSpan146_split :
    compactRest00 62242 = constraintMinimaChunk005Chars00 ++ compactRest00 62624 := by
  calc
    compactRest00 62242 =
        (compactRest00 62242).take 382 ++ (compactRest00 62242).drop 382 :=
      (List.take_append_drop 382 (compactRest00 62242)).symm
    _ = constraintMinimaChunk005Chars00 ++ (compactRest00 62242).drop 382 :=
      congrArg (fun part => part ++ (compactRest00 62242).drop 382) compactSpan146_prefix
    _ = constraintMinimaChunk005Chars00 ++ compactRest00 62624 :=
      congrArg (fun tail => constraintMinimaChunk005Chars00 ++ tail) (compactRest00_drop 62242 382)

theorem compactSpan146_rest_eq (htail : geometryChars00.drop 62624 = compactRest00 62624) :
    geometryChars00.drop 62242 = compactRest00 62242 := by
  have hp : (geometryChars00.drop 62242).take 382 = constraintMinimaChunk005Chars00 :=
    geometryChars00_constraintMinima_chunk_005_prefix
  exact (list_drop_split_of_prefix geometryChars00 62242 382 constraintMinimaChunk005Chars00 hp).trans
    ((congrArg (fun tail => constraintMinimaChunk005Chars00 ++ tail) htail).trans compactSpan146_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_146_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_147_before_prefix"
  err.flush

theorem compactSpan147_prefix :
    (compactRest00 62624).take 30 = constraintMinimaChunk006Chars00 := by rfl

theorem compactSpan147_split :
    compactRest00 62624 = constraintMinimaChunk006Chars00 ++ compactRest00 62654 := by
  calc
    compactRest00 62624 =
        (compactRest00 62624).take 30 ++ (compactRest00 62624).drop 30 :=
      (List.take_append_drop 30 (compactRest00 62624)).symm
    _ = constraintMinimaChunk006Chars00 ++ (compactRest00 62624).drop 30 :=
      congrArg (fun part => part ++ (compactRest00 62624).drop 30) compactSpan147_prefix
    _ = constraintMinimaChunk006Chars00 ++ compactRest00 62654 :=
      congrArg (fun tail => constraintMinimaChunk006Chars00 ++ tail) (compactRest00_drop 62624 30)

theorem compactSpan147_rest_eq (htail : geometryChars00.drop 62654 = compactRest00 62654) :
    geometryChars00.drop 62624 = compactRest00 62624 := by
  have hp : (geometryChars00.drop 62624).take 30 = constraintMinimaChunk006Chars00 :=
    geometryChars00_constraintMinima_chunk_006_prefix
  exact (list_drop_split_of_prefix geometryChars00 62624 30 constraintMinimaChunk006Chars00 hp).trans
    ((congrArg (fun tail => constraintMinimaChunk006Chars00 ++ tail) htail).trans compactSpan147_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_147_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_148_before_prefix"
  err.flush

theorem compactSpan148_prefix :
    (compactRest00 62654).take 1 = constraintMinimaSeparatorChars00 := by rfl

theorem compactSpan148_split :
    compactRest00 62654 = constraintMinimaSeparatorChars00 ++ compactRest00 62655 := by
  calc
    compactRest00 62654 =
        (compactRest00 62654).take 1 ++ (compactRest00 62654).drop 1 :=
      (List.take_append_drop 1 (compactRest00 62654)).symm
    _ = constraintMinimaSeparatorChars00 ++ (compactRest00 62654).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 62654).drop 1) compactSpan148_prefix
    _ = constraintMinimaSeparatorChars00 ++ compactRest00 62655 :=
      congrArg (fun tail => constraintMinimaSeparatorChars00 ++ tail) (compactRest00_drop 62654 1)

theorem compactSpan148_rest_eq (htail : geometryChars00.drop 62655 = compactRest00 62655) :
    geometryChars00.drop 62654 = compactRest00 62654 := by
  have hp : (geometryChars00.drop 62654).take 1 = constraintMinimaSeparatorChars00 :=
    geometryChars00_constraintMinima_separator_prefix
  exact (list_drop_split_of_prefix geometryChars00 62654 1 constraintMinimaSeparatorChars00 hp).trans
    ((congrArg (fun tail => constraintMinimaSeparatorChars00 ++ tail) htail).trans compactSpan148_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_148_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_149_before_prefix"
  err.flush

theorem compactSpan149_prefix :
    (compactRest00 62655).take 22 = facetVerticesHeaderChars00 := by rfl

theorem compactSpan149_split :
    compactRest00 62655 = facetVerticesHeaderChars00 ++ compactRest00 62677 := by
  calc
    compactRest00 62655 =
        (compactRest00 62655).take 22 ++ (compactRest00 62655).drop 22 :=
      (List.take_append_drop 22 (compactRest00 62655)).symm
    _ = facetVerticesHeaderChars00 ++ (compactRest00 62655).drop 22 :=
      congrArg (fun part => part ++ (compactRest00 62655).drop 22) compactSpan149_prefix
    _ = facetVerticesHeaderChars00 ++ compactRest00 62677 :=
      congrArg (fun tail => facetVerticesHeaderChars00 ++ tail) (compactRest00_drop 62655 22)

theorem compactSpan149_rest_eq (htail : geometryChars00.drop 62677 = compactRest00 62677) :
    geometryChars00.drop 62655 = compactRest00 62655 := by
  have hp : (geometryChars00.drop 62655).take 22 = facetVerticesHeaderChars00 :=
    geometryChars00_facetVertices_header_prefix
  exact (list_drop_split_of_prefix geometryChars00 62655 22 facetVerticesHeaderChars00 hp).trans
    ((congrArg (fun tail => facetVerticesHeaderChars00 ++ tail) htail).trans compactSpan149_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_149_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_150_before_prefix"
  err.flush

theorem compactSpan150_prefix :
    (compactRest00 62677).take 1 = facetVerticesOpenChars00 := by rfl

theorem compactSpan150_split :
    compactRest00 62677 = facetVerticesOpenChars00 ++ compactRest00 62678 := by
  calc
    compactRest00 62677 =
        (compactRest00 62677).take 1 ++ (compactRest00 62677).drop 1 :=
      (List.take_append_drop 1 (compactRest00 62677)).symm
    _ = facetVerticesOpenChars00 ++ (compactRest00 62677).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 62677).drop 1) compactSpan150_prefix
    _ = facetVerticesOpenChars00 ++ compactRest00 62678 :=
      congrArg (fun tail => facetVerticesOpenChars00 ++ tail) (compactRest00_drop 62677 1)

theorem compactSpan150_rest_eq (htail : geometryChars00.drop 62678 = compactRest00 62678) :
    geometryChars00.drop 62677 = compactRest00 62677 := by
  have hp : (geometryChars00.drop 62677).take 1 = facetVerticesOpenChars00 :=
    geometryChars00_facetVertices_open_prefix
  exact (list_drop_split_of_prefix geometryChars00 62677 1 facetVerticesOpenChars00 hp).trans
    ((congrArg (fun tail => facetVerticesOpenChars00 ++ tail) htail).trans compactSpan150_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_150_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_151_before_prefix"
  err.flush

theorem compactSpan151_prefix :
    (compactRest00 62678).take 1730 = facetVerticesBlock000Chars00 := by rfl

theorem compactSpan151_split :
    compactRest00 62678 = facetVerticesBlock000Chars00 ++ compactRest00 64408 := by
  calc
    compactRest00 62678 =
        (compactRest00 62678).take 1730 ++ (compactRest00 62678).drop 1730 :=
      (List.take_append_drop 1730 (compactRest00 62678)).symm
    _ = facetVerticesBlock000Chars00 ++ (compactRest00 62678).drop 1730 :=
      congrArg (fun part => part ++ (compactRest00 62678).drop 1730) compactSpan151_prefix
    _ = facetVerticesBlock000Chars00 ++ compactRest00 64408 :=
      congrArg (fun tail => facetVerticesBlock000Chars00 ++ tail) (compactRest00_drop 62678 1730)

theorem compactSpan151_rest_eq (htail : geometryChars00.drop 64408 = compactRest00 64408) :
    geometryChars00.drop 62678 = compactRest00 62678 := by
  have hp : (geometryChars00.drop 62678).take 1730 = facetVerticesBlock000Chars00 :=
    geometryChars00_facetVertices_block_000_prefix
  exact (list_drop_split_of_prefix geometryChars00 62678 1730 facetVerticesBlock000Chars00 hp).trans
    ((congrArg (fun tail => facetVerticesBlock000Chars00 ++ tail) htail).trans compactSpan151_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_151_complete"
  err.flush

theorem group018_rest_eq
    (htail : geometryChars00.drop 64408 = compactRest00 64408) :
    geometryChars00.drop 61514 = compactRest00 61514 := by
  have h151 := compactSpan151_rest_eq htail
  have h150 := compactSpan150_rest_eq h151
  have h149 := compactSpan149_rest_eq h150
  have h148 := compactSpan148_rest_eq h149
  have h147 := compactSpan147_rest_eq h148
  have h146 := compactSpan146_rest_eq h147
  have h145 := compactSpan145_rest_eq h146
  have h144 := compactSpan144_rest_eq h145
  exact h144

#print axioms compactSpan144_prefix
#print axioms compactSpan144_split
#print axioms compactSpan144_rest_eq
#print axioms compactSpan145_prefix
#print axioms compactSpan145_split
#print axioms compactSpan145_rest_eq
#print axioms compactSpan146_prefix
#print axioms compactSpan146_split
#print axioms compactSpan146_rest_eq
#print axioms compactSpan147_prefix
#print axioms compactSpan147_split
#print axioms compactSpan147_rest_eq
#print axioms compactSpan148_prefix
#print axioms compactSpan148_split
#print axioms compactSpan148_rest_eq
#print axioms compactSpan149_prefix
#print axioms compactSpan149_split
#print axioms compactSpan149_rest_eq
#print axioms compactSpan150_prefix
#print axioms compactSpan150_split
#print axioms compactSpan150_rest_eq
#print axioms compactSpan151_prefix
#print axioms compactSpan151_split
#print axioms compactSpan151_rest_eq
#print axioms group018_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
