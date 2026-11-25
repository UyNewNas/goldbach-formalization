import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00400
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00500
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00600

/-! Exact compact prefix group 16, bytes [55723,59493).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_128_before_prefix"
  err.flush

theorem compactSpan128_prefix :
    (compactRest00 55723).take 471 = vertexValuesChunk018Chars00 := by rfl

theorem compactSpan128_split :
    compactRest00 55723 = vertexValuesChunk018Chars00 ++ compactRest00 56194 := by
  calc
    compactRest00 55723 =
        (compactRest00 55723).take 471 ++ (compactRest00 55723).drop 471 :=
      (List.take_append_drop 471 (compactRest00 55723)).symm
    _ = vertexValuesChunk018Chars00 ++ (compactRest00 55723).drop 471 :=
      congrArg (fun part => part ++ (compactRest00 55723).drop 471) compactSpan128_prefix
    _ = vertexValuesChunk018Chars00 ++ compactRest00 56194 :=
      congrArg (fun tail => vertexValuesChunk018Chars00 ++ tail) (compactRest00_drop 55723 471)

theorem compactSpan128_rest_eq (htail : geometryChars00.drop 56194 = compactRest00 56194) :
    geometryChars00.drop 55723 = compactRest00 55723 := by
  have hp : (geometryChars00.drop 55723).take 471 = vertexValuesChunk018Chars00 :=
    geometryChars00_vertexValues_chunk_018_prefix
  exact (list_drop_split_of_prefix geometryChars00 55723 471 vertexValuesChunk018Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk018Chars00 ++ tail) htail).trans compactSpan128_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_128_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_129_before_prefix"
  err.flush

theorem compactSpan129_prefix :
    (compactRest00 56194).take 473 = vertexValuesChunk019Chars00 := by rfl

theorem compactSpan129_split :
    compactRest00 56194 = vertexValuesChunk019Chars00 ++ compactRest00 56667 := by
  calc
    compactRest00 56194 =
        (compactRest00 56194).take 473 ++ (compactRest00 56194).drop 473 :=
      (List.take_append_drop 473 (compactRest00 56194)).symm
    _ = vertexValuesChunk019Chars00 ++ (compactRest00 56194).drop 473 :=
      congrArg (fun part => part ++ (compactRest00 56194).drop 473) compactSpan129_prefix
    _ = vertexValuesChunk019Chars00 ++ compactRest00 56667 :=
      congrArg (fun tail => vertexValuesChunk019Chars00 ++ tail) (compactRest00_drop 56194 473)

theorem compactSpan129_rest_eq (htail : geometryChars00.drop 56667 = compactRest00 56667) :
    geometryChars00.drop 56194 = compactRest00 56194 := by
  have hp : (geometryChars00.drop 56194).take 473 = vertexValuesChunk019Chars00 :=
    geometryChars00_vertexValues_chunk_019_prefix
  exact (list_drop_split_of_prefix geometryChars00 56194 473 vertexValuesChunk019Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk019Chars00 ++ tail) htail).trans compactSpan129_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_129_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_130_before_prefix"
  err.flush

theorem compactSpan130_prefix :
    (compactRest00 56667).take 477 = vertexValuesChunk020Chars00 := by rfl

theorem compactSpan130_split :
    compactRest00 56667 = vertexValuesChunk020Chars00 ++ compactRest00 57144 := by
  calc
    compactRest00 56667 =
        (compactRest00 56667).take 477 ++ (compactRest00 56667).drop 477 :=
      (List.take_append_drop 477 (compactRest00 56667)).symm
    _ = vertexValuesChunk020Chars00 ++ (compactRest00 56667).drop 477 :=
      congrArg (fun part => part ++ (compactRest00 56667).drop 477) compactSpan130_prefix
    _ = vertexValuesChunk020Chars00 ++ compactRest00 57144 :=
      congrArg (fun tail => vertexValuesChunk020Chars00 ++ tail) (compactRest00_drop 56667 477)

theorem compactSpan130_rest_eq (htail : geometryChars00.drop 57144 = compactRest00 57144) :
    geometryChars00.drop 56667 = compactRest00 56667 := by
  have hp : (geometryChars00.drop 56667).take 477 = vertexValuesChunk020Chars00 :=
    geometryChars00_vertexValues_chunk_020_prefix
  exact (list_drop_split_of_prefix geometryChars00 56667 477 vertexValuesChunk020Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk020Chars00 ++ tail) htail).trans compactSpan130_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_130_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_131_before_prefix"
  err.flush

theorem compactSpan131_prefix :
    (compactRest00 57144).take 450 = vertexValuesChunk021Chars00 := by rfl

theorem compactSpan131_split :
    compactRest00 57144 = vertexValuesChunk021Chars00 ++ compactRest00 57594 := by
  calc
    compactRest00 57144 =
        (compactRest00 57144).take 450 ++ (compactRest00 57144).drop 450 :=
      (List.take_append_drop 450 (compactRest00 57144)).symm
    _ = vertexValuesChunk021Chars00 ++ (compactRest00 57144).drop 450 :=
      congrArg (fun part => part ++ (compactRest00 57144).drop 450) compactSpan131_prefix
    _ = vertexValuesChunk021Chars00 ++ compactRest00 57594 :=
      congrArg (fun tail => vertexValuesChunk021Chars00 ++ tail) (compactRest00_drop 57144 450)

theorem compactSpan131_rest_eq (htail : geometryChars00.drop 57594 = compactRest00 57594) :
    geometryChars00.drop 57144 = compactRest00 57144 := by
  have hp : (geometryChars00.drop 57144).take 450 = vertexValuesChunk021Chars00 :=
    geometryChars00_vertexValues_chunk_021_prefix
  exact (list_drop_split_of_prefix geometryChars00 57144 450 vertexValuesChunk021Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk021Chars00 ++ tail) htail).trans compactSpan131_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_131_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_132_before_prefix"
  err.flush

theorem compactSpan132_prefix :
    (compactRest00 57594).take 470 = vertexValuesChunk022Chars00 := by rfl

theorem compactSpan132_split :
    compactRest00 57594 = vertexValuesChunk022Chars00 ++ compactRest00 58064 := by
  calc
    compactRest00 57594 =
        (compactRest00 57594).take 470 ++ (compactRest00 57594).drop 470 :=
      (List.take_append_drop 470 (compactRest00 57594)).symm
    _ = vertexValuesChunk022Chars00 ++ (compactRest00 57594).drop 470 :=
      congrArg (fun part => part ++ (compactRest00 57594).drop 470) compactSpan132_prefix
    _ = vertexValuesChunk022Chars00 ++ compactRest00 58064 :=
      congrArg (fun tail => vertexValuesChunk022Chars00 ++ tail) (compactRest00_drop 57594 470)

theorem compactSpan132_rest_eq (htail : geometryChars00.drop 58064 = compactRest00 58064) :
    geometryChars00.drop 57594 = compactRest00 57594 := by
  have hp : (geometryChars00.drop 57594).take 470 = vertexValuesChunk022Chars00 :=
    geometryChars00_vertexValues_chunk_022_prefix
  exact (list_drop_split_of_prefix geometryChars00 57594 470 vertexValuesChunk022Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk022Chars00 ++ tail) htail).trans compactSpan132_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_132_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_133_before_prefix"
  err.flush

theorem compactSpan133_prefix :
    (compactRest00 58064).take 476 = vertexValuesChunk023Chars00 := by rfl

theorem compactSpan133_split :
    compactRest00 58064 = vertexValuesChunk023Chars00 ++ compactRest00 58540 := by
  calc
    compactRest00 58064 =
        (compactRest00 58064).take 476 ++ (compactRest00 58064).drop 476 :=
      (List.take_append_drop 476 (compactRest00 58064)).symm
    _ = vertexValuesChunk023Chars00 ++ (compactRest00 58064).drop 476 :=
      congrArg (fun part => part ++ (compactRest00 58064).drop 476) compactSpan133_prefix
    _ = vertexValuesChunk023Chars00 ++ compactRest00 58540 :=
      congrArg (fun tail => vertexValuesChunk023Chars00 ++ tail) (compactRest00_drop 58064 476)

theorem compactSpan133_rest_eq (htail : geometryChars00.drop 58540 = compactRest00 58540) :
    geometryChars00.drop 58064 = compactRest00 58064 := by
  have hp : (geometryChars00.drop 58064).take 476 = vertexValuesChunk023Chars00 :=
    geometryChars00_vertexValues_chunk_023_prefix
  exact (list_drop_split_of_prefix geometryChars00 58064 476 vertexValuesChunk023Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk023Chars00 ++ tail) htail).trans compactSpan133_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_133_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_134_before_prefix"
  err.flush

theorem compactSpan134_prefix :
    (compactRest00 58540).take 468 = vertexValuesChunk024Chars00 := by rfl

theorem compactSpan134_split :
    compactRest00 58540 = vertexValuesChunk024Chars00 ++ compactRest00 59008 := by
  calc
    compactRest00 58540 =
        (compactRest00 58540).take 468 ++ (compactRest00 58540).drop 468 :=
      (List.take_append_drop 468 (compactRest00 58540)).symm
    _ = vertexValuesChunk024Chars00 ++ (compactRest00 58540).drop 468 :=
      congrArg (fun part => part ++ (compactRest00 58540).drop 468) compactSpan134_prefix
    _ = vertexValuesChunk024Chars00 ++ compactRest00 59008 :=
      congrArg (fun tail => vertexValuesChunk024Chars00 ++ tail) (compactRest00_drop 58540 468)

theorem compactSpan134_rest_eq (htail : geometryChars00.drop 59008 = compactRest00 59008) :
    geometryChars00.drop 58540 = compactRest00 58540 := by
  have hp : (geometryChars00.drop 58540).take 468 = vertexValuesChunk024Chars00 :=
    geometryChars00_vertexValues_chunk_024_prefix
  exact (list_drop_split_of_prefix geometryChars00 58540 468 vertexValuesChunk024Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk024Chars00 ++ tail) htail).trans compactSpan134_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_134_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_135_before_prefix"
  err.flush

theorem compactSpan135_prefix :
    (compactRest00 59008).take 485 = vertexValuesChunk025Chars00 := by rfl

theorem compactSpan135_split :
    compactRest00 59008 = vertexValuesChunk025Chars00 ++ compactRest00 59493 := by
  calc
    compactRest00 59008 =
        (compactRest00 59008).take 485 ++ (compactRest00 59008).drop 485 :=
      (List.take_append_drop 485 (compactRest00 59008)).symm
    _ = vertexValuesChunk025Chars00 ++ (compactRest00 59008).drop 485 :=
      congrArg (fun part => part ++ (compactRest00 59008).drop 485) compactSpan135_prefix
    _ = vertexValuesChunk025Chars00 ++ compactRest00 59493 :=
      congrArg (fun tail => vertexValuesChunk025Chars00 ++ tail) (compactRest00_drop 59008 485)

theorem compactSpan135_rest_eq (htail : geometryChars00.drop 59493 = compactRest00 59493) :
    geometryChars00.drop 59008 = compactRest00 59008 := by
  have hp : (geometryChars00.drop 59008).take 485 = vertexValuesChunk025Chars00 :=
    geometryChars00_vertexValues_chunk_025_prefix
  exact (list_drop_split_of_prefix geometryChars00 59008 485 vertexValuesChunk025Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk025Chars00 ++ tail) htail).trans compactSpan135_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_135_complete"
  err.flush

theorem group016_rest_eq
    (htail : geometryChars00.drop 59493 = compactRest00 59493) :
    geometryChars00.drop 55723 = compactRest00 55723 := by
  have h135 := compactSpan135_rest_eq htail
  have h134 := compactSpan134_rest_eq h135
  have h133 := compactSpan133_rest_eq h134
  have h132 := compactSpan132_rest_eq h133
  have h131 := compactSpan131_rest_eq h132
  have h130 := compactSpan130_rest_eq h131
  have h129 := compactSpan129_rest_eq h130
  have h128 := compactSpan128_rest_eq h129
  exact h128

#print axioms compactSpan128_prefix
#print axioms compactSpan128_split
#print axioms compactSpan128_rest_eq
#print axioms compactSpan129_prefix
#print axioms compactSpan129_split
#print axioms compactSpan129_rest_eq
#print axioms compactSpan130_prefix
#print axioms compactSpan130_split
#print axioms compactSpan130_rest_eq
#print axioms compactSpan131_prefix
#print axioms compactSpan131_split
#print axioms compactSpan131_rest_eq
#print axioms compactSpan132_prefix
#print axioms compactSpan132_split
#print axioms compactSpan132_rest_eq
#print axioms compactSpan133_prefix
#print axioms compactSpan133_split
#print axioms compactSpan133_rest_eq
#print axioms compactSpan134_prefix
#print axioms compactSpan134_split
#print axioms compactSpan134_rest_eq
#print axioms compactSpan135_prefix
#print axioms compactSpan135_split
#print axioms compactSpan135_rest_eq
#print axioms group016_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
