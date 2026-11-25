import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00000
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00100
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00200

/-! Exact compact prefix group 14, bytes [47955,51856).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_112_before_prefix"
  err.flush

theorem compactSpan112_prefix :
    (compactRest00 47955).take 507 = vertexValuesChunk002Chars00 := by rfl

theorem compactSpan112_split :
    compactRest00 47955 = vertexValuesChunk002Chars00 ++ compactRest00 48462 := by
  calc
    compactRest00 47955 =
        (compactRest00 47955).take 507 ++ (compactRest00 47955).drop 507 :=
      (List.take_append_drop 507 (compactRest00 47955)).symm
    _ = vertexValuesChunk002Chars00 ++ (compactRest00 47955).drop 507 :=
      congrArg (fun part => part ++ (compactRest00 47955).drop 507) compactSpan112_prefix
    _ = vertexValuesChunk002Chars00 ++ compactRest00 48462 :=
      congrArg (fun tail => vertexValuesChunk002Chars00 ++ tail) (compactRest00_drop 47955 507)

theorem compactSpan112_rest_eq (htail : geometryChars00.drop 48462 = compactRest00 48462) :
    geometryChars00.drop 47955 = compactRest00 47955 := by
  have hp : (geometryChars00.drop 47955).take 507 = vertexValuesChunk002Chars00 :=
    geometryChars00_vertexValues_chunk_002_prefix
  exact (list_drop_split_of_prefix geometryChars00 47955 507 vertexValuesChunk002Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk002Chars00 ++ tail) htail).trans compactSpan112_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_112_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_113_before_prefix"
  err.flush

theorem compactSpan113_prefix :
    (compactRest00 48462).take 510 = vertexValuesChunk003Chars00 := by rfl

theorem compactSpan113_split :
    compactRest00 48462 = vertexValuesChunk003Chars00 ++ compactRest00 48972 := by
  calc
    compactRest00 48462 =
        (compactRest00 48462).take 510 ++ (compactRest00 48462).drop 510 :=
      (List.take_append_drop 510 (compactRest00 48462)).symm
    _ = vertexValuesChunk003Chars00 ++ (compactRest00 48462).drop 510 :=
      congrArg (fun part => part ++ (compactRest00 48462).drop 510) compactSpan113_prefix
    _ = vertexValuesChunk003Chars00 ++ compactRest00 48972 :=
      congrArg (fun tail => vertexValuesChunk003Chars00 ++ tail) (compactRest00_drop 48462 510)

theorem compactSpan113_rest_eq (htail : geometryChars00.drop 48972 = compactRest00 48972) :
    geometryChars00.drop 48462 = compactRest00 48462 := by
  have hp : (geometryChars00.drop 48462).take 510 = vertexValuesChunk003Chars00 :=
    geometryChars00_vertexValues_chunk_003_prefix
  exact (list_drop_split_of_prefix geometryChars00 48462 510 vertexValuesChunk003Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk003Chars00 ++ tail) htail).trans compactSpan113_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_113_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_114_before_prefix"
  err.flush

theorem compactSpan114_prefix :
    (compactRest00 48972).take 493 = vertexValuesChunk004Chars00 := by rfl

theorem compactSpan114_split :
    compactRest00 48972 = vertexValuesChunk004Chars00 ++ compactRest00 49465 := by
  calc
    compactRest00 48972 =
        (compactRest00 48972).take 493 ++ (compactRest00 48972).drop 493 :=
      (List.take_append_drop 493 (compactRest00 48972)).symm
    _ = vertexValuesChunk004Chars00 ++ (compactRest00 48972).drop 493 :=
      congrArg (fun part => part ++ (compactRest00 48972).drop 493) compactSpan114_prefix
    _ = vertexValuesChunk004Chars00 ++ compactRest00 49465 :=
      congrArg (fun tail => vertexValuesChunk004Chars00 ++ tail) (compactRest00_drop 48972 493)

theorem compactSpan114_rest_eq (htail : geometryChars00.drop 49465 = compactRest00 49465) :
    geometryChars00.drop 48972 = compactRest00 48972 := by
  have hp : (geometryChars00.drop 48972).take 493 = vertexValuesChunk004Chars00 :=
    geometryChars00_vertexValues_chunk_004_prefix
  exact (list_drop_split_of_prefix geometryChars00 48972 493 vertexValuesChunk004Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk004Chars00 ++ tail) htail).trans compactSpan114_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_114_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_115_before_prefix"
  err.flush

theorem compactSpan115_prefix :
    (compactRest00 49465).take 467 = vertexValuesChunk005Chars00 := by rfl

theorem compactSpan115_split :
    compactRest00 49465 = vertexValuesChunk005Chars00 ++ compactRest00 49932 := by
  calc
    compactRest00 49465 =
        (compactRest00 49465).take 467 ++ (compactRest00 49465).drop 467 :=
      (List.take_append_drop 467 (compactRest00 49465)).symm
    _ = vertexValuesChunk005Chars00 ++ (compactRest00 49465).drop 467 :=
      congrArg (fun part => part ++ (compactRest00 49465).drop 467) compactSpan115_prefix
    _ = vertexValuesChunk005Chars00 ++ compactRest00 49932 :=
      congrArg (fun tail => vertexValuesChunk005Chars00 ++ tail) (compactRest00_drop 49465 467)

theorem compactSpan115_rest_eq (htail : geometryChars00.drop 49932 = compactRest00 49932) :
    geometryChars00.drop 49465 = compactRest00 49465 := by
  have hp : (geometryChars00.drop 49465).take 467 = vertexValuesChunk005Chars00 :=
    geometryChars00_vertexValues_chunk_005_prefix
  exact (list_drop_split_of_prefix geometryChars00 49465 467 vertexValuesChunk005Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk005Chars00 ++ tail) htail).trans compactSpan115_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_115_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_116_before_prefix"
  err.flush

theorem compactSpan116_prefix :
    (compactRest00 49932).take 477 = vertexValuesChunk006Chars00 := by rfl

theorem compactSpan116_split :
    compactRest00 49932 = vertexValuesChunk006Chars00 ++ compactRest00 50409 := by
  calc
    compactRest00 49932 =
        (compactRest00 49932).take 477 ++ (compactRest00 49932).drop 477 :=
      (List.take_append_drop 477 (compactRest00 49932)).symm
    _ = vertexValuesChunk006Chars00 ++ (compactRest00 49932).drop 477 :=
      congrArg (fun part => part ++ (compactRest00 49932).drop 477) compactSpan116_prefix
    _ = vertexValuesChunk006Chars00 ++ compactRest00 50409 :=
      congrArg (fun tail => vertexValuesChunk006Chars00 ++ tail) (compactRest00_drop 49932 477)

theorem compactSpan116_rest_eq (htail : geometryChars00.drop 50409 = compactRest00 50409) :
    geometryChars00.drop 49932 = compactRest00 49932 := by
  have hp : (geometryChars00.drop 49932).take 477 = vertexValuesChunk006Chars00 :=
    geometryChars00_vertexValues_chunk_006_prefix
  exact (list_drop_split_of_prefix geometryChars00 49932 477 vertexValuesChunk006Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk006Chars00 ++ tail) htail).trans compactSpan116_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_116_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_117_before_prefix"
  err.flush

theorem compactSpan117_prefix :
    (compactRest00 50409).take 478 = vertexValuesChunk007Chars00 := by rfl

theorem compactSpan117_split :
    compactRest00 50409 = vertexValuesChunk007Chars00 ++ compactRest00 50887 := by
  calc
    compactRest00 50409 =
        (compactRest00 50409).take 478 ++ (compactRest00 50409).drop 478 :=
      (List.take_append_drop 478 (compactRest00 50409)).symm
    _ = vertexValuesChunk007Chars00 ++ (compactRest00 50409).drop 478 :=
      congrArg (fun part => part ++ (compactRest00 50409).drop 478) compactSpan117_prefix
    _ = vertexValuesChunk007Chars00 ++ compactRest00 50887 :=
      congrArg (fun tail => vertexValuesChunk007Chars00 ++ tail) (compactRest00_drop 50409 478)

theorem compactSpan117_rest_eq (htail : geometryChars00.drop 50887 = compactRest00 50887) :
    geometryChars00.drop 50409 = compactRest00 50409 := by
  have hp : (geometryChars00.drop 50409).take 478 = vertexValuesChunk007Chars00 :=
    geometryChars00_vertexValues_chunk_007_prefix
  exact (list_drop_split_of_prefix geometryChars00 50409 478 vertexValuesChunk007Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk007Chars00 ++ tail) htail).trans compactSpan117_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_117_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_118_before_prefix"
  err.flush

theorem compactSpan118_prefix :
    (compactRest00 50887).take 484 = vertexValuesChunk008Chars00 := by rfl

theorem compactSpan118_split :
    compactRest00 50887 = vertexValuesChunk008Chars00 ++ compactRest00 51371 := by
  calc
    compactRest00 50887 =
        (compactRest00 50887).take 484 ++ (compactRest00 50887).drop 484 :=
      (List.take_append_drop 484 (compactRest00 50887)).symm
    _ = vertexValuesChunk008Chars00 ++ (compactRest00 50887).drop 484 :=
      congrArg (fun part => part ++ (compactRest00 50887).drop 484) compactSpan118_prefix
    _ = vertexValuesChunk008Chars00 ++ compactRest00 51371 :=
      congrArg (fun tail => vertexValuesChunk008Chars00 ++ tail) (compactRest00_drop 50887 484)

theorem compactSpan118_rest_eq (htail : geometryChars00.drop 51371 = compactRest00 51371) :
    geometryChars00.drop 50887 = compactRest00 50887 := by
  have hp : (geometryChars00.drop 50887).take 484 = vertexValuesChunk008Chars00 :=
    geometryChars00_vertexValues_chunk_008_prefix
  exact (list_drop_split_of_prefix geometryChars00 50887 484 vertexValuesChunk008Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk008Chars00 ++ tail) htail).trans compactSpan118_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_118_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_119_before_prefix"
  err.flush

theorem compactSpan119_prefix :
    (compactRest00 51371).take 485 = vertexValuesChunk009Chars00 := by rfl

theorem compactSpan119_split :
    compactRest00 51371 = vertexValuesChunk009Chars00 ++ compactRest00 51856 := by
  calc
    compactRest00 51371 =
        (compactRest00 51371).take 485 ++ (compactRest00 51371).drop 485 :=
      (List.take_append_drop 485 (compactRest00 51371)).symm
    _ = vertexValuesChunk009Chars00 ++ (compactRest00 51371).drop 485 :=
      congrArg (fun part => part ++ (compactRest00 51371).drop 485) compactSpan119_prefix
    _ = vertexValuesChunk009Chars00 ++ compactRest00 51856 :=
      congrArg (fun tail => vertexValuesChunk009Chars00 ++ tail) (compactRest00_drop 51371 485)

theorem compactSpan119_rest_eq (htail : geometryChars00.drop 51856 = compactRest00 51856) :
    geometryChars00.drop 51371 = compactRest00 51371 := by
  have hp : (geometryChars00.drop 51371).take 485 = vertexValuesChunk009Chars00 :=
    geometryChars00_vertexValues_chunk_009_prefix
  exact (list_drop_split_of_prefix geometryChars00 51371 485 vertexValuesChunk009Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk009Chars00 ++ tail) htail).trans compactSpan119_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_119_complete"
  err.flush

theorem group014_rest_eq
    (htail : geometryChars00.drop 51856 = compactRest00 51856) :
    geometryChars00.drop 47955 = compactRest00 47955 := by
  have h119 := compactSpan119_rest_eq htail
  have h118 := compactSpan118_rest_eq h119
  have h117 := compactSpan117_rest_eq h118
  have h116 := compactSpan116_rest_eq h117
  have h115 := compactSpan115_rest_eq h116
  have h114 := compactSpan114_rest_eq h115
  have h113 := compactSpan113_rest_eq h114
  have h112 := compactSpan112_rest_eq h113
  exact h112

#print axioms compactSpan112_prefix
#print axioms compactSpan112_split
#print axioms compactSpan112_rest_eq
#print axioms compactSpan113_prefix
#print axioms compactSpan113_split
#print axioms compactSpan113_rest_eq
#print axioms compactSpan114_prefix
#print axioms compactSpan114_split
#print axioms compactSpan114_rest_eq
#print axioms compactSpan115_prefix
#print axioms compactSpan115_split
#print axioms compactSpan115_rest_eq
#print axioms compactSpan116_prefix
#print axioms compactSpan116_split
#print axioms compactSpan116_rest_eq
#print axioms compactSpan117_prefix
#print axioms compactSpan117_split
#print axioms compactSpan117_rest_eq
#print axioms compactSpan118_prefix
#print axioms compactSpan118_split
#print axioms compactSpan118_rest_eq
#print axioms compactSpan119_prefix
#print axioms compactSpan119_split
#print axioms compactSpan119_rest_eq
#print axioms group014_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
