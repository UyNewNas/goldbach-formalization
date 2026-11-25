import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00200
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00300
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00400

/-! Exact compact prefix group 15, bytes [51856,55723).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_120_before_prefix"
  err.flush

theorem compactSpan120_prefix :
    (compactRest00 51856).take 479 = vertexValuesChunk010Chars00 := by rfl

theorem compactSpan120_split :
    compactRest00 51856 = vertexValuesChunk010Chars00 ++ compactRest00 52335 := by
  calc
    compactRest00 51856 =
        (compactRest00 51856).take 479 ++ (compactRest00 51856).drop 479 :=
      (List.take_append_drop 479 (compactRest00 51856)).symm
    _ = vertexValuesChunk010Chars00 ++ (compactRest00 51856).drop 479 :=
      congrArg (fun part => part ++ (compactRest00 51856).drop 479) compactSpan120_prefix
    _ = vertexValuesChunk010Chars00 ++ compactRest00 52335 :=
      congrArg (fun tail => vertexValuesChunk010Chars00 ++ tail) (compactRest00_drop 51856 479)

theorem compactSpan120_rest_eq (htail : geometryChars00.drop 52335 = compactRest00 52335) :
    geometryChars00.drop 51856 = compactRest00 51856 := by
  have hp : (geometryChars00.drop 51856).take 479 = vertexValuesChunk010Chars00 :=
    geometryChars00_vertexValues_chunk_010_prefix
  exact (list_drop_split_of_prefix geometryChars00 51856 479 vertexValuesChunk010Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk010Chars00 ++ tail) htail).trans compactSpan120_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_120_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_121_before_prefix"
  err.flush

theorem compactSpan121_prefix :
    (compactRest00 52335).take 486 = vertexValuesChunk011Chars00 := by rfl

theorem compactSpan121_split :
    compactRest00 52335 = vertexValuesChunk011Chars00 ++ compactRest00 52821 := by
  calc
    compactRest00 52335 =
        (compactRest00 52335).take 486 ++ (compactRest00 52335).drop 486 :=
      (List.take_append_drop 486 (compactRest00 52335)).symm
    _ = vertexValuesChunk011Chars00 ++ (compactRest00 52335).drop 486 :=
      congrArg (fun part => part ++ (compactRest00 52335).drop 486) compactSpan121_prefix
    _ = vertexValuesChunk011Chars00 ++ compactRest00 52821 :=
      congrArg (fun tail => vertexValuesChunk011Chars00 ++ tail) (compactRest00_drop 52335 486)

theorem compactSpan121_rest_eq (htail : geometryChars00.drop 52821 = compactRest00 52821) :
    geometryChars00.drop 52335 = compactRest00 52335 := by
  have hp : (geometryChars00.drop 52335).take 486 = vertexValuesChunk011Chars00 :=
    geometryChars00_vertexValues_chunk_011_prefix
  exact (list_drop_split_of_prefix geometryChars00 52335 486 vertexValuesChunk011Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk011Chars00 ++ tail) htail).trans compactSpan121_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_121_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_122_before_prefix"
  err.flush

theorem compactSpan122_prefix :
    (compactRest00 52821).take 512 = vertexValuesChunk012Chars00 := by rfl

theorem compactSpan122_split :
    compactRest00 52821 = vertexValuesChunk012Chars00 ++ compactRest00 53333 := by
  calc
    compactRest00 52821 =
        (compactRest00 52821).take 512 ++ (compactRest00 52821).drop 512 :=
      (List.take_append_drop 512 (compactRest00 52821)).symm
    _ = vertexValuesChunk012Chars00 ++ (compactRest00 52821).drop 512 :=
      congrArg (fun part => part ++ (compactRest00 52821).drop 512) compactSpan122_prefix
    _ = vertexValuesChunk012Chars00 ++ compactRest00 53333 :=
      congrArg (fun tail => vertexValuesChunk012Chars00 ++ tail) (compactRest00_drop 52821 512)

theorem compactSpan122_rest_eq (htail : geometryChars00.drop 53333 = compactRest00 53333) :
    geometryChars00.drop 52821 = compactRest00 52821 := by
  have hp : (geometryChars00.drop 52821).take 512 = vertexValuesChunk012Chars00 :=
    geometryChars00_vertexValues_chunk_012_prefix
  exact (list_drop_split_of_prefix geometryChars00 52821 512 vertexValuesChunk012Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk012Chars00 ++ tail) htail).trans compactSpan122_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_122_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_123_before_prefix"
  err.flush

theorem compactSpan123_prefix :
    (compactRest00 53333).take 510 = vertexValuesChunk013Chars00 := by rfl

theorem compactSpan123_split :
    compactRest00 53333 = vertexValuesChunk013Chars00 ++ compactRest00 53843 := by
  calc
    compactRest00 53333 =
        (compactRest00 53333).take 510 ++ (compactRest00 53333).drop 510 :=
      (List.take_append_drop 510 (compactRest00 53333)).symm
    _ = vertexValuesChunk013Chars00 ++ (compactRest00 53333).drop 510 :=
      congrArg (fun part => part ++ (compactRest00 53333).drop 510) compactSpan123_prefix
    _ = vertexValuesChunk013Chars00 ++ compactRest00 53843 :=
      congrArg (fun tail => vertexValuesChunk013Chars00 ++ tail) (compactRest00_drop 53333 510)

theorem compactSpan123_rest_eq (htail : geometryChars00.drop 53843 = compactRest00 53843) :
    geometryChars00.drop 53333 = compactRest00 53333 := by
  have hp : (geometryChars00.drop 53333).take 510 = vertexValuesChunk013Chars00 :=
    geometryChars00_vertexValues_chunk_013_prefix
  exact (list_drop_split_of_prefix geometryChars00 53333 510 vertexValuesChunk013Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk013Chars00 ++ tail) htail).trans compactSpan123_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_123_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_124_before_prefix"
  err.flush

theorem compactSpan124_prefix :
    (compactRest00 53843).take 467 = vertexValuesChunk014Chars00 := by rfl

theorem compactSpan124_split :
    compactRest00 53843 = vertexValuesChunk014Chars00 ++ compactRest00 54310 := by
  calc
    compactRest00 53843 =
        (compactRest00 53843).take 467 ++ (compactRest00 53843).drop 467 :=
      (List.take_append_drop 467 (compactRest00 53843)).symm
    _ = vertexValuesChunk014Chars00 ++ (compactRest00 53843).drop 467 :=
      congrArg (fun part => part ++ (compactRest00 53843).drop 467) compactSpan124_prefix
    _ = vertexValuesChunk014Chars00 ++ compactRest00 54310 :=
      congrArg (fun tail => vertexValuesChunk014Chars00 ++ tail) (compactRest00_drop 53843 467)

theorem compactSpan124_rest_eq (htail : geometryChars00.drop 54310 = compactRest00 54310) :
    geometryChars00.drop 53843 = compactRest00 53843 := by
  have hp : (geometryChars00.drop 53843).take 467 = vertexValuesChunk014Chars00 :=
    geometryChars00_vertexValues_chunk_014_prefix
  exact (list_drop_split_of_prefix geometryChars00 53843 467 vertexValuesChunk014Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk014Chars00 ++ tail) htail).trans compactSpan124_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_124_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_125_before_prefix"
  err.flush

theorem compactSpan125_prefix :
    (compactRest00 54310).take 478 = vertexValuesChunk015Chars00 := by rfl

theorem compactSpan125_split :
    compactRest00 54310 = vertexValuesChunk015Chars00 ++ compactRest00 54788 := by
  calc
    compactRest00 54310 =
        (compactRest00 54310).take 478 ++ (compactRest00 54310).drop 478 :=
      (List.take_append_drop 478 (compactRest00 54310)).symm
    _ = vertexValuesChunk015Chars00 ++ (compactRest00 54310).drop 478 :=
      congrArg (fun part => part ++ (compactRest00 54310).drop 478) compactSpan125_prefix
    _ = vertexValuesChunk015Chars00 ++ compactRest00 54788 :=
      congrArg (fun tail => vertexValuesChunk015Chars00 ++ tail) (compactRest00_drop 54310 478)

theorem compactSpan125_rest_eq (htail : geometryChars00.drop 54788 = compactRest00 54788) :
    geometryChars00.drop 54310 = compactRest00 54310 := by
  have hp : (geometryChars00.drop 54310).take 478 = vertexValuesChunk015Chars00 :=
    geometryChars00_vertexValues_chunk_015_prefix
  exact (list_drop_split_of_prefix geometryChars00 54310 478 vertexValuesChunk015Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk015Chars00 ++ tail) htail).trans compactSpan125_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_125_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_126_before_prefix"
  err.flush

theorem compactSpan126_prefix :
    (compactRest00 54788).take 458 = vertexValuesChunk016Chars00 := by rfl

theorem compactSpan126_split :
    compactRest00 54788 = vertexValuesChunk016Chars00 ++ compactRest00 55246 := by
  calc
    compactRest00 54788 =
        (compactRest00 54788).take 458 ++ (compactRest00 54788).drop 458 :=
      (List.take_append_drop 458 (compactRest00 54788)).symm
    _ = vertexValuesChunk016Chars00 ++ (compactRest00 54788).drop 458 :=
      congrArg (fun part => part ++ (compactRest00 54788).drop 458) compactSpan126_prefix
    _ = vertexValuesChunk016Chars00 ++ compactRest00 55246 :=
      congrArg (fun tail => vertexValuesChunk016Chars00 ++ tail) (compactRest00_drop 54788 458)

theorem compactSpan126_rest_eq (htail : geometryChars00.drop 55246 = compactRest00 55246) :
    geometryChars00.drop 54788 = compactRest00 54788 := by
  have hp : (geometryChars00.drop 54788).take 458 = vertexValuesChunk016Chars00 :=
    geometryChars00_vertexValues_chunk_016_prefix
  exact (list_drop_split_of_prefix geometryChars00 54788 458 vertexValuesChunk016Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk016Chars00 ++ tail) htail).trans compactSpan126_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_126_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_127_before_prefix"
  err.flush

theorem compactSpan127_prefix :
    (compactRest00 55246).take 477 = vertexValuesChunk017Chars00 := by rfl

theorem compactSpan127_split :
    compactRest00 55246 = vertexValuesChunk017Chars00 ++ compactRest00 55723 := by
  calc
    compactRest00 55246 =
        (compactRest00 55246).take 477 ++ (compactRest00 55246).drop 477 :=
      (List.take_append_drop 477 (compactRest00 55246)).symm
    _ = vertexValuesChunk017Chars00 ++ (compactRest00 55246).drop 477 :=
      congrArg (fun part => part ++ (compactRest00 55246).drop 477) compactSpan127_prefix
    _ = vertexValuesChunk017Chars00 ++ compactRest00 55723 :=
      congrArg (fun tail => vertexValuesChunk017Chars00 ++ tail) (compactRest00_drop 55246 477)

theorem compactSpan127_rest_eq (htail : geometryChars00.drop 55723 = compactRest00 55723) :
    geometryChars00.drop 55246 = compactRest00 55246 := by
  have hp : (geometryChars00.drop 55246).take 477 = vertexValuesChunk017Chars00 :=
    geometryChars00_vertexValues_chunk_017_prefix
  exact (list_drop_split_of_prefix geometryChars00 55246 477 vertexValuesChunk017Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk017Chars00 ++ tail) htail).trans compactSpan127_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_127_complete"
  err.flush

theorem group015_rest_eq
    (htail : geometryChars00.drop 55723 = compactRest00 55723) :
    geometryChars00.drop 51856 = compactRest00 51856 := by
  have h127 := compactSpan127_rest_eq htail
  have h126 := compactSpan126_rest_eq h127
  have h125 := compactSpan125_rest_eq h126
  have h124 := compactSpan124_rest_eq h125
  have h123 := compactSpan123_rest_eq h124
  have h122 := compactSpan122_rest_eq h123
  have h121 := compactSpan121_rest_eq h122
  have h120 := compactSpan120_rest_eq h121
  exact h120

#print axioms compactSpan120_prefix
#print axioms compactSpan120_split
#print axioms compactSpan120_rest_eq
#print axioms compactSpan121_prefix
#print axioms compactSpan121_split
#print axioms compactSpan121_rest_eq
#print axioms compactSpan122_prefix
#print axioms compactSpan122_split
#print axioms compactSpan122_rest_eq
#print axioms compactSpan123_prefix
#print axioms compactSpan123_split
#print axioms compactSpan123_rest_eq
#print axioms compactSpan124_prefix
#print axioms compactSpan124_split
#print axioms compactSpan124_rest_eq
#print axioms compactSpan125_prefix
#print axioms compactSpan125_split
#print axioms compactSpan125_rest_eq
#print axioms compactSpan126_prefix
#print axioms compactSpan126_split
#print axioms compactSpan126_rest_eq
#print axioms compactSpan127_prefix
#print axioms compactSpan127_split
#print axioms compactSpan127_rest_eq
#print axioms group015_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
