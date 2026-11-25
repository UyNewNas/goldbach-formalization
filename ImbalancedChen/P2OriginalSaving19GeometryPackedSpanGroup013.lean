import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00200
import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00300
import ImbalancedChen.P2OriginalSaving19VerticesField00
import ImbalancedChen.P2OriginalSaving19VertexValuesField00
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00000

/-! Exact compact prefix group 13, bytes [45608,47955).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_104_before_prefix"
  err.flush

theorem compactSpan104_prefix :
    (compactRest00 45608).take 450 = verticesChunk011Chars00 := by rfl

theorem compactSpan104_split :
    compactRest00 45608 = verticesChunk011Chars00 ++ compactRest00 46058 := by
  calc
    compactRest00 45608 =
        (compactRest00 45608).take 450 ++ (compactRest00 45608).drop 450 :=
      (List.take_append_drop 450 (compactRest00 45608)).symm
    _ = verticesChunk011Chars00 ++ (compactRest00 45608).drop 450 :=
      congrArg (fun part => part ++ (compactRest00 45608).drop 450) compactSpan104_prefix
    _ = verticesChunk011Chars00 ++ compactRest00 46058 :=
      congrArg (fun tail => verticesChunk011Chars00 ++ tail) (compactRest00_drop 45608 450)

theorem compactSpan104_rest_eq (htail : geometryChars00.drop 46058 = compactRest00 46058) :
    geometryChars00.drop 45608 = compactRest00 45608 := by
  have hp : (geometryChars00.drop 45608).take 450 = verticesChunk011Chars00 :=
    geometryChars00_vertices_chunk_011_prefix
  exact (list_drop_split_of_prefix geometryChars00 45608 450 verticesChunk011Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk011Chars00 ++ tail) htail).trans compactSpan104_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_104_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_105_before_prefix"
  err.flush

theorem compactSpan105_prefix :
    (compactRest00 46058).take 457 = verticesChunk012Chars00 := by rfl

theorem compactSpan105_split :
    compactRest00 46058 = verticesChunk012Chars00 ++ compactRest00 46515 := by
  calc
    compactRest00 46058 =
        (compactRest00 46058).take 457 ++ (compactRest00 46058).drop 457 :=
      (List.take_append_drop 457 (compactRest00 46058)).symm
    _ = verticesChunk012Chars00 ++ (compactRest00 46058).drop 457 :=
      congrArg (fun part => part ++ (compactRest00 46058).drop 457) compactSpan105_prefix
    _ = verticesChunk012Chars00 ++ compactRest00 46515 :=
      congrArg (fun tail => verticesChunk012Chars00 ++ tail) (compactRest00_drop 46058 457)

theorem compactSpan105_rest_eq (htail : geometryChars00.drop 46515 = compactRest00 46515) :
    geometryChars00.drop 46058 = compactRest00 46058 := by
  have hp : (geometryChars00.drop 46058).take 457 = verticesChunk012Chars00 :=
    geometryChars00_vertices_chunk_012_prefix
  exact (list_drop_split_of_prefix geometryChars00 46058 457 verticesChunk012Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk012Chars00 ++ tail) htail).trans compactSpan105_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_105_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_106_before_prefix"
  err.flush

theorem compactSpan106_prefix :
    (compactRest00 46515).take 459 = verticesChunk013Chars00 := by rfl

theorem compactSpan106_split :
    compactRest00 46515 = verticesChunk013Chars00 ++ compactRest00 46974 := by
  calc
    compactRest00 46515 =
        (compactRest00 46515).take 459 ++ (compactRest00 46515).drop 459 :=
      (List.take_append_drop 459 (compactRest00 46515)).symm
    _ = verticesChunk013Chars00 ++ (compactRest00 46515).drop 459 :=
      congrArg (fun part => part ++ (compactRest00 46515).drop 459) compactSpan106_prefix
    _ = verticesChunk013Chars00 ++ compactRest00 46974 :=
      congrArg (fun tail => verticesChunk013Chars00 ++ tail) (compactRest00_drop 46515 459)

theorem compactSpan106_rest_eq (htail : geometryChars00.drop 46974 = compactRest00 46974) :
    geometryChars00.drop 46515 = compactRest00 46515 := by
  have hp : (geometryChars00.drop 46515).take 459 = verticesChunk013Chars00 :=
    geometryChars00_vertices_chunk_013_prefix
  exact (list_drop_split_of_prefix geometryChars00 46515 459 verticesChunk013Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk013Chars00 ++ tail) htail).trans compactSpan106_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_106_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_107_before_prefix"
  err.flush

theorem compactSpan107_prefix :
    (compactRest00 46974).take 1 = verticesSeparatorChars00 := by rfl

theorem compactSpan107_split :
    compactRest00 46974 = verticesSeparatorChars00 ++ compactRest00 46975 := by
  calc
    compactRest00 46974 =
        (compactRest00 46974).take 1 ++ (compactRest00 46974).drop 1 :=
      (List.take_append_drop 1 (compactRest00 46974)).symm
    _ = verticesSeparatorChars00 ++ (compactRest00 46974).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 46974).drop 1) compactSpan107_prefix
    _ = verticesSeparatorChars00 ++ compactRest00 46975 :=
      congrArg (fun tail => verticesSeparatorChars00 ++ tail) (compactRest00_drop 46974 1)

theorem compactSpan107_rest_eq (htail : geometryChars00.drop 46975 = compactRest00 46975) :
    geometryChars00.drop 46974 = compactRest00 46974 := by
  have hp : (geometryChars00.drop 46974).take 1 = verticesSeparatorChars00 :=
    geometryChars00_vertices_separator_prefix
  exact (list_drop_split_of_prefix geometryChars00 46974 1 verticesSeparatorChars00 hp).trans
    ((congrArg (fun tail => verticesSeparatorChars00 ++ tail) htail).trans compactSpan107_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_107_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_108_before_prefix"
  err.flush

theorem compactSpan108_prefix :
    (compactRest00 46975).take 21 = vertexValuesHeaderChars00 := by rfl

theorem compactSpan108_split :
    compactRest00 46975 = vertexValuesHeaderChars00 ++ compactRest00 46996 := by
  calc
    compactRest00 46975 =
        (compactRest00 46975).take 21 ++ (compactRest00 46975).drop 21 :=
      (List.take_append_drop 21 (compactRest00 46975)).symm
    _ = vertexValuesHeaderChars00 ++ (compactRest00 46975).drop 21 :=
      congrArg (fun part => part ++ (compactRest00 46975).drop 21) compactSpan108_prefix
    _ = vertexValuesHeaderChars00 ++ compactRest00 46996 :=
      congrArg (fun tail => vertexValuesHeaderChars00 ++ tail) (compactRest00_drop 46975 21)

theorem compactSpan108_rest_eq (htail : geometryChars00.drop 46996 = compactRest00 46996) :
    geometryChars00.drop 46975 = compactRest00 46975 := by
  have hp : (geometryChars00.drop 46975).take 21 = vertexValuesHeaderChars00 :=
    geometryChars00_vertexValues_header_prefix
  exact (list_drop_split_of_prefix geometryChars00 46975 21 vertexValuesHeaderChars00 hp).trans
    ((congrArg (fun tail => vertexValuesHeaderChars00 ++ tail) htail).trans compactSpan108_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_108_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_109_before_prefix"
  err.flush

theorem compactSpan109_prefix :
    (compactRest00 46996).take 1 = vertexValuesOpenChars00 := by rfl

theorem compactSpan109_split :
    compactRest00 46996 = vertexValuesOpenChars00 ++ compactRest00 46997 := by
  calc
    compactRest00 46996 =
        (compactRest00 46996).take 1 ++ (compactRest00 46996).drop 1 :=
      (List.take_append_drop 1 (compactRest00 46996)).symm
    _ = vertexValuesOpenChars00 ++ (compactRest00 46996).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 46996).drop 1) compactSpan109_prefix
    _ = vertexValuesOpenChars00 ++ compactRest00 46997 :=
      congrArg (fun tail => vertexValuesOpenChars00 ++ tail) (compactRest00_drop 46996 1)

theorem compactSpan109_rest_eq (htail : geometryChars00.drop 46997 = compactRest00 46997) :
    geometryChars00.drop 46996 = compactRest00 46996 := by
  have hp : (geometryChars00.drop 46996).take 1 = vertexValuesOpenChars00 :=
    geometryChars00_vertexValues_open_prefix
  exact (list_drop_split_of_prefix geometryChars00 46996 1 vertexValuesOpenChars00 hp).trans
    ((congrArg (fun tail => vertexValuesOpenChars00 ++ tail) htail).trans compactSpan109_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_109_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_110_before_prefix"
  err.flush

theorem compactSpan110_prefix :
    (compactRest00 46997).take 489 = vertexValuesChunk000Chars00 := by rfl

theorem compactSpan110_split :
    compactRest00 46997 = vertexValuesChunk000Chars00 ++ compactRest00 47486 := by
  calc
    compactRest00 46997 =
        (compactRest00 46997).take 489 ++ (compactRest00 46997).drop 489 :=
      (List.take_append_drop 489 (compactRest00 46997)).symm
    _ = vertexValuesChunk000Chars00 ++ (compactRest00 46997).drop 489 :=
      congrArg (fun part => part ++ (compactRest00 46997).drop 489) compactSpan110_prefix
    _ = vertexValuesChunk000Chars00 ++ compactRest00 47486 :=
      congrArg (fun tail => vertexValuesChunk000Chars00 ++ tail) (compactRest00_drop 46997 489)

theorem compactSpan110_rest_eq (htail : geometryChars00.drop 47486 = compactRest00 47486) :
    geometryChars00.drop 46997 = compactRest00 46997 := by
  have hp : (geometryChars00.drop 46997).take 489 = vertexValuesChunk000Chars00 :=
    geometryChars00_vertexValues_chunk_000_prefix
  exact (list_drop_split_of_prefix geometryChars00 46997 489 vertexValuesChunk000Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk000Chars00 ++ tail) htail).trans compactSpan110_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_110_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_111_before_prefix"
  err.flush

theorem compactSpan111_prefix :
    (compactRest00 47486).take 469 = vertexValuesChunk001Chars00 := by rfl

theorem compactSpan111_split :
    compactRest00 47486 = vertexValuesChunk001Chars00 ++ compactRest00 47955 := by
  calc
    compactRest00 47486 =
        (compactRest00 47486).take 469 ++ (compactRest00 47486).drop 469 :=
      (List.take_append_drop 469 (compactRest00 47486)).symm
    _ = vertexValuesChunk001Chars00 ++ (compactRest00 47486).drop 469 :=
      congrArg (fun part => part ++ (compactRest00 47486).drop 469) compactSpan111_prefix
    _ = vertexValuesChunk001Chars00 ++ compactRest00 47955 :=
      congrArg (fun tail => vertexValuesChunk001Chars00 ++ tail) (compactRest00_drop 47486 469)

theorem compactSpan111_rest_eq (htail : geometryChars00.drop 47955 = compactRest00 47955) :
    geometryChars00.drop 47486 = compactRest00 47486 := by
  have hp : (geometryChars00.drop 47486).take 469 = vertexValuesChunk001Chars00 :=
    geometryChars00_vertexValues_chunk_001_prefix
  exact (list_drop_split_of_prefix geometryChars00 47486 469 vertexValuesChunk001Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk001Chars00 ++ tail) htail).trans compactSpan111_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_111_complete"
  err.flush

theorem group013_rest_eq
    (htail : geometryChars00.drop 47955 = compactRest00 47955) :
    geometryChars00.drop 45608 = compactRest00 45608 := by
  have h111 := compactSpan111_rest_eq htail
  have h110 := compactSpan110_rest_eq h111
  have h109 := compactSpan109_rest_eq h110
  have h108 := compactSpan108_rest_eq h109
  have h107 := compactSpan107_rest_eq h108
  have h106 := compactSpan106_rest_eq h107
  have h105 := compactSpan105_rest_eq h106
  have h104 := compactSpan104_rest_eq h105
  exact h104

#print axioms compactSpan104_prefix
#print axioms compactSpan104_split
#print axioms compactSpan104_rest_eq
#print axioms compactSpan105_prefix
#print axioms compactSpan105_split
#print axioms compactSpan105_rest_eq
#print axioms compactSpan106_prefix
#print axioms compactSpan106_split
#print axioms compactSpan106_rest_eq
#print axioms compactSpan107_prefix
#print axioms compactSpan107_split
#print axioms compactSpan107_rest_eq
#print axioms compactSpan108_prefix
#print axioms compactSpan108_split
#print axioms compactSpan108_rest_eq
#print axioms compactSpan109_prefix
#print axioms compactSpan109_split
#print axioms compactSpan109_rest_eq
#print axioms compactSpan110_prefix
#print axioms compactSpan110_split
#print axioms compactSpan110_rest_eq
#print axioms compactSpan111_prefix
#print axioms compactSpan111_split
#print axioms compactSpan111_rest_eq
#print axioms group013_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
