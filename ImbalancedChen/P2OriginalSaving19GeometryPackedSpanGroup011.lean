import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock02000
import ImbalancedChen.P2OriginalSaving19Active8Field00
import ImbalancedChen.P2OriginalSaving19VerticesField00
import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00000

/-! Exact compact prefix group 11, bytes [39842,42000).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_088_before_prefix"
  err.flush

theorem compactSpan088_prefix :
    (compactRest00 39842).take 483 = active8Chunk081Chars00 := by rfl

theorem compactSpan088_split :
    compactRest00 39842 = active8Chunk081Chars00 ++ compactRest00 40325 := by
  calc
    compactRest00 39842 =
        (compactRest00 39842).take 483 ++ (compactRest00 39842).drop 483 :=
      (List.take_append_drop 483 (compactRest00 39842)).symm
    _ = active8Chunk081Chars00 ++ (compactRest00 39842).drop 483 :=
      congrArg (fun part => part ++ (compactRest00 39842).drop 483) compactSpan088_prefix
    _ = active8Chunk081Chars00 ++ compactRest00 40325 :=
      congrArg (fun tail => active8Chunk081Chars00 ++ tail) (compactRest00_drop 39842 483)

theorem compactSpan088_rest_eq (htail : geometryChars00.drop 40325 = compactRest00 40325) :
    geometryChars00.drop 39842 = compactRest00 39842 := by
  have hp : (geometryChars00.drop 39842).take 483 = active8Chunk081Chars00 :=
    geometryChars00_active8_chunk_081_prefix
  exact (list_drop_split_of_prefix geometryChars00 39842 483 active8Chunk081Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk081Chars00 ++ tail) htail).trans compactSpan088_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_088_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_089_before_prefix"
  err.flush

theorem compactSpan089_prefix :
    (compactRest00 40325).take 272 = active8Chunk082Chars00 := by rfl

theorem compactSpan089_split :
    compactRest00 40325 = active8Chunk082Chars00 ++ compactRest00 40597 := by
  calc
    compactRest00 40325 =
        (compactRest00 40325).take 272 ++ (compactRest00 40325).drop 272 :=
      (List.take_append_drop 272 (compactRest00 40325)).symm
    _ = active8Chunk082Chars00 ++ (compactRest00 40325).drop 272 :=
      congrArg (fun part => part ++ (compactRest00 40325).drop 272) compactSpan089_prefix
    _ = active8Chunk082Chars00 ++ compactRest00 40597 :=
      congrArg (fun tail => active8Chunk082Chars00 ++ tail) (compactRest00_drop 40325 272)

theorem compactSpan089_rest_eq (htail : geometryChars00.drop 40597 = compactRest00 40597) :
    geometryChars00.drop 40325 = compactRest00 40325 := by
  have hp : (geometryChars00.drop 40325).take 272 = active8Chunk082Chars00 :=
    geometryChars00_active8_chunk_082_prefix
  exact (list_drop_split_of_prefix geometryChars00 40325 272 active8Chunk082Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk082Chars00 ++ tail) htail).trans compactSpan089_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_089_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_090_before_prefix"
  err.flush

theorem compactSpan090_prefix :
    (compactRest00 40597).take 1 = active8SeparatorChars00 := by rfl

theorem compactSpan090_split :
    compactRest00 40597 = active8SeparatorChars00 ++ compactRest00 40598 := by
  calc
    compactRest00 40597 =
        (compactRest00 40597).take 1 ++ (compactRest00 40597).drop 1 :=
      (List.take_append_drop 1 (compactRest00 40597)).symm
    _ = active8SeparatorChars00 ++ (compactRest00 40597).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 40597).drop 1) compactSpan090_prefix
    _ = active8SeparatorChars00 ++ compactRest00 40598 :=
      congrArg (fun tail => active8SeparatorChars00 ++ tail) (compactRest00_drop 40597 1)

theorem compactSpan090_rest_eq (htail : geometryChars00.drop 40598 = compactRest00 40598) :
    geometryChars00.drop 40597 = compactRest00 40597 := by
  have hp : (geometryChars00.drop 40597).take 1 = active8SeparatorChars00 :=
    geometryChars00_active8_separator_prefix
  exact (list_drop_split_of_prefix geometryChars00 40597 1 active8SeparatorChars00 hp).trans
    ((congrArg (fun tail => active8SeparatorChars00 ++ tail) htail).trans compactSpan090_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_090_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_091_before_prefix"
  err.flush

theorem compactSpan091_prefix :
    (compactRest00 40598).take 16 = verticesHeaderChars00 := by rfl

theorem compactSpan091_split :
    compactRest00 40598 = verticesHeaderChars00 ++ compactRest00 40614 := by
  calc
    compactRest00 40598 =
        (compactRest00 40598).take 16 ++ (compactRest00 40598).drop 16 :=
      (List.take_append_drop 16 (compactRest00 40598)).symm
    _ = verticesHeaderChars00 ++ (compactRest00 40598).drop 16 :=
      congrArg (fun part => part ++ (compactRest00 40598).drop 16) compactSpan091_prefix
    _ = verticesHeaderChars00 ++ compactRest00 40614 :=
      congrArg (fun tail => verticesHeaderChars00 ++ tail) (compactRest00_drop 40598 16)

theorem compactSpan091_rest_eq (htail : geometryChars00.drop 40614 = compactRest00 40614) :
    geometryChars00.drop 40598 = compactRest00 40598 := by
  have hp : (geometryChars00.drop 40598).take 16 = verticesHeaderChars00 :=
    geometryChars00_vertices_header_prefix
  exact (list_drop_split_of_prefix geometryChars00 40598 16 verticesHeaderChars00 hp).trans
    ((congrArg (fun tail => verticesHeaderChars00 ++ tail) htail).trans compactSpan091_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_091_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_092_before_prefix"
  err.flush

theorem compactSpan092_prefix :
    (compactRest00 40614).take 1 = verticesOpenChars00 := by rfl

theorem compactSpan092_split :
    compactRest00 40614 = verticesOpenChars00 ++ compactRest00 40615 := by
  calc
    compactRest00 40614 =
        (compactRest00 40614).take 1 ++ (compactRest00 40614).drop 1 :=
      (List.take_append_drop 1 (compactRest00 40614)).symm
    _ = verticesOpenChars00 ++ (compactRest00 40614).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 40614).drop 1) compactSpan092_prefix
    _ = verticesOpenChars00 ++ compactRest00 40615 :=
      congrArg (fun tail => verticesOpenChars00 ++ tail) (compactRest00_drop 40614 1)

theorem compactSpan092_rest_eq (htail : geometryChars00.drop 40615 = compactRest00 40615) :
    geometryChars00.drop 40614 = compactRest00 40614 := by
  have hp : (geometryChars00.drop 40614).take 1 = verticesOpenChars00 :=
    geometryChars00_vertices_open_prefix
  exact (list_drop_split_of_prefix geometryChars00 40614 1 verticesOpenChars00 hp).trans
    ((congrArg (fun tail => verticesOpenChars00 ++ tail) htail).trans compactSpan092_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_092_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_093_before_prefix"
  err.flush

theorem compactSpan093_prefix :
    (compactRest00 40615).take 457 = verticesChunk000Chars00 := by rfl

theorem compactSpan093_split :
    compactRest00 40615 = verticesChunk000Chars00 ++ compactRest00 41072 := by
  calc
    compactRest00 40615 =
        (compactRest00 40615).take 457 ++ (compactRest00 40615).drop 457 :=
      (List.take_append_drop 457 (compactRest00 40615)).symm
    _ = verticesChunk000Chars00 ++ (compactRest00 40615).drop 457 :=
      congrArg (fun part => part ++ (compactRest00 40615).drop 457) compactSpan093_prefix
    _ = verticesChunk000Chars00 ++ compactRest00 41072 :=
      congrArg (fun tail => verticesChunk000Chars00 ++ tail) (compactRest00_drop 40615 457)

theorem compactSpan093_rest_eq (htail : geometryChars00.drop 41072 = compactRest00 41072) :
    geometryChars00.drop 40615 = compactRest00 40615 := by
  have hp : (geometryChars00.drop 40615).take 457 = verticesChunk000Chars00 :=
    geometryChars00_vertices_chunk_000_prefix
  exact (list_drop_split_of_prefix geometryChars00 40615 457 verticesChunk000Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk000Chars00 ++ tail) htail).trans compactSpan093_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_093_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_094_before_prefix"
  err.flush

theorem compactSpan094_prefix :
    (compactRest00 41072).take 472 = verticesChunk001Chars00 := by rfl

theorem compactSpan094_split :
    compactRest00 41072 = verticesChunk001Chars00 ++ compactRest00 41544 := by
  calc
    compactRest00 41072 =
        (compactRest00 41072).take 472 ++ (compactRest00 41072).drop 472 :=
      (List.take_append_drop 472 (compactRest00 41072)).symm
    _ = verticesChunk001Chars00 ++ (compactRest00 41072).drop 472 :=
      congrArg (fun part => part ++ (compactRest00 41072).drop 472) compactSpan094_prefix
    _ = verticesChunk001Chars00 ++ compactRest00 41544 :=
      congrArg (fun tail => verticesChunk001Chars00 ++ tail) (compactRest00_drop 41072 472)

theorem compactSpan094_rest_eq (htail : geometryChars00.drop 41544 = compactRest00 41544) :
    geometryChars00.drop 41072 = compactRest00 41072 := by
  have hp : (geometryChars00.drop 41072).take 472 = verticesChunk001Chars00 :=
    geometryChars00_vertices_chunk_001_prefix
  exact (list_drop_split_of_prefix geometryChars00 41072 472 verticesChunk001Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk001Chars00 ++ tail) htail).trans compactSpan094_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_094_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_095_before_prefix"
  err.flush

theorem compactSpan095_prefix :
    (compactRest00 41544).take 456 = verticesChunk002Chars00 := by rfl

theorem compactSpan095_split :
    compactRest00 41544 = verticesChunk002Chars00 ++ compactRest00 42000 := by
  calc
    compactRest00 41544 =
        (compactRest00 41544).take 456 ++ (compactRest00 41544).drop 456 :=
      (List.take_append_drop 456 (compactRest00 41544)).symm
    _ = verticesChunk002Chars00 ++ (compactRest00 41544).drop 456 :=
      congrArg (fun part => part ++ (compactRest00 41544).drop 456) compactSpan095_prefix
    _ = verticesChunk002Chars00 ++ compactRest00 42000 :=
      congrArg (fun tail => verticesChunk002Chars00 ++ tail) (compactRest00_drop 41544 456)

theorem compactSpan095_rest_eq (htail : geometryChars00.drop 42000 = compactRest00 42000) :
    geometryChars00.drop 41544 = compactRest00 41544 := by
  have hp : (geometryChars00.drop 41544).take 456 = verticesChunk002Chars00 :=
    geometryChars00_vertices_chunk_002_prefix
  exact (list_drop_split_of_prefix geometryChars00 41544 456 verticesChunk002Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk002Chars00 ++ tail) htail).trans compactSpan095_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_095_complete"
  err.flush

theorem group011_rest_eq
    (htail : geometryChars00.drop 42000 = compactRest00 42000) :
    geometryChars00.drop 39842 = compactRest00 39842 := by
  have h095 := compactSpan095_rest_eq htail
  have h094 := compactSpan094_rest_eq h095
  have h093 := compactSpan093_rest_eq h094
  have h092 := compactSpan092_rest_eq h093
  have h091 := compactSpan091_rest_eq h092
  have h090 := compactSpan090_rest_eq h091
  have h089 := compactSpan089_rest_eq h090
  have h088 := compactSpan088_rest_eq h089
  exact h088

#print axioms compactSpan088_prefix
#print axioms compactSpan088_split
#print axioms compactSpan088_rest_eq
#print axioms compactSpan089_prefix
#print axioms compactSpan089_split
#print axioms compactSpan089_rest_eq
#print axioms compactSpan090_prefix
#print axioms compactSpan090_split
#print axioms compactSpan090_rest_eq
#print axioms compactSpan091_prefix
#print axioms compactSpan091_split
#print axioms compactSpan091_rest_eq
#print axioms compactSpan092_prefix
#print axioms compactSpan092_split
#print axioms compactSpan092_rest_eq
#print axioms compactSpan093_prefix
#print axioms compactSpan093_split
#print axioms compactSpan093_rest_eq
#print axioms compactSpan094_prefix
#print axioms compactSpan094_split
#print axioms compactSpan094_rest_eq
#print axioms compactSpan095_prefix
#print axioms compactSpan095_split
#print axioms compactSpan095_rest_eq
#print axioms group011_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
