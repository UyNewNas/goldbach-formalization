import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00600
import ImbalancedChen.P2OriginalSaving19VertexValuesField00
import ImbalancedChen.P2OriginalSaving19ConstraintMinimaField00
import ImbalancedChen.P2OriginalSaving19ConstraintMinimaArrayBlock00000

/-! Exact compact prefix group 17, bytes [59493,61514).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_136_before_prefix"
  err.flush

theorem compactSpan136_prefix :
    (compactRest00 59493).take 472 = vertexValuesChunk026Chars00 := by rfl

theorem compactSpan136_split :
    compactRest00 59493 = vertexValuesChunk026Chars00 ++ compactRest00 59965 := by
  calc
    compactRest00 59493 =
        (compactRest00 59493).take 472 ++ (compactRest00 59493).drop 472 :=
      (List.take_append_drop 472 (compactRest00 59493)).symm
    _ = vertexValuesChunk026Chars00 ++ (compactRest00 59493).drop 472 :=
      congrArg (fun part => part ++ (compactRest00 59493).drop 472) compactSpan136_prefix
    _ = vertexValuesChunk026Chars00 ++ compactRest00 59965 :=
      congrArg (fun tail => vertexValuesChunk026Chars00 ++ tail) (compactRest00_drop 59493 472)

theorem compactSpan136_rest_eq (htail : geometryChars00.drop 59965 = compactRest00 59965) :
    geometryChars00.drop 59493 = compactRest00 59493 := by
  have hp : (geometryChars00.drop 59493).take 472 = vertexValuesChunk026Chars00 :=
    geometryChars00_vertexValues_chunk_026_prefix
  exact (list_drop_split_of_prefix geometryChars00 59493 472 vertexValuesChunk026Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk026Chars00 ++ tail) htail).trans compactSpan136_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_136_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_137_before_prefix"
  err.flush

theorem compactSpan137_prefix :
    (compactRest00 59965).take 483 = vertexValuesChunk027Chars00 := by rfl

theorem compactSpan137_split :
    compactRest00 59965 = vertexValuesChunk027Chars00 ++ compactRest00 60448 := by
  calc
    compactRest00 59965 =
        (compactRest00 59965).take 483 ++ (compactRest00 59965).drop 483 :=
      (List.take_append_drop 483 (compactRest00 59965)).symm
    _ = vertexValuesChunk027Chars00 ++ (compactRest00 59965).drop 483 :=
      congrArg (fun part => part ++ (compactRest00 59965).drop 483) compactSpan137_prefix
    _ = vertexValuesChunk027Chars00 ++ compactRest00 60448 :=
      congrArg (fun tail => vertexValuesChunk027Chars00 ++ tail) (compactRest00_drop 59965 483)

theorem compactSpan137_rest_eq (htail : geometryChars00.drop 60448 = compactRest00 60448) :
    geometryChars00.drop 59965 = compactRest00 59965 := by
  have hp : (geometryChars00.drop 59965).take 483 = vertexValuesChunk027Chars00 :=
    geometryChars00_vertexValues_chunk_027_prefix
  exact (list_drop_split_of_prefix geometryChars00 59965 483 vertexValuesChunk027Chars00 hp).trans
    ((congrArg (fun tail => vertexValuesChunk027Chars00 ++ tail) htail).trans compactSpan137_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_137_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_138_before_prefix"
  err.flush

theorem compactSpan138_prefix :
    (compactRest00 60448).take 1 = vertexValuesSeparatorChars00 := by rfl

theorem compactSpan138_split :
    compactRest00 60448 = vertexValuesSeparatorChars00 ++ compactRest00 60449 := by
  calc
    compactRest00 60448 =
        (compactRest00 60448).take 1 ++ (compactRest00 60448).drop 1 :=
      (List.take_append_drop 1 (compactRest00 60448)).symm
    _ = vertexValuesSeparatorChars00 ++ (compactRest00 60448).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 60448).drop 1) compactSpan138_prefix
    _ = vertexValuesSeparatorChars00 ++ compactRest00 60449 :=
      congrArg (fun tail => vertexValuesSeparatorChars00 ++ tail) (compactRest00_drop 60448 1)

theorem compactSpan138_rest_eq (htail : geometryChars00.drop 60449 = compactRest00 60449) :
    geometryChars00.drop 60448 = compactRest00 60448 := by
  have hp : (geometryChars00.drop 60448).take 1 = vertexValuesSeparatorChars00 :=
    geometryChars00_vertexValues_separator_prefix
  exact (list_drop_split_of_prefix geometryChars00 60448 1 vertexValuesSeparatorChars00 hp).trans
    ((congrArg (fun tail => vertexValuesSeparatorChars00 ++ tail) htail).trans compactSpan138_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_138_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_139_before_prefix"
  err.flush

theorem compactSpan139_prefix :
    (compactRest00 60449).take 38 = constraintMinimaHeaderChars00 := by rfl

theorem compactSpan139_split :
    compactRest00 60449 = constraintMinimaHeaderChars00 ++ compactRest00 60487 := by
  calc
    compactRest00 60449 =
        (compactRest00 60449).take 38 ++ (compactRest00 60449).drop 38 :=
      (List.take_append_drop 38 (compactRest00 60449)).symm
    _ = constraintMinimaHeaderChars00 ++ (compactRest00 60449).drop 38 :=
      congrArg (fun part => part ++ (compactRest00 60449).drop 38) compactSpan139_prefix
    _ = constraintMinimaHeaderChars00 ++ compactRest00 60487 :=
      congrArg (fun tail => constraintMinimaHeaderChars00 ++ tail) (compactRest00_drop 60449 38)

theorem compactSpan139_rest_eq (htail : geometryChars00.drop 60487 = compactRest00 60487) :
    geometryChars00.drop 60449 = compactRest00 60449 := by
  have hp : (geometryChars00.drop 60449).take 38 = constraintMinimaHeaderChars00 :=
    geometryChars00_constraintMinima_header_prefix
  exact (list_drop_split_of_prefix geometryChars00 60449 38 constraintMinimaHeaderChars00 hp).trans
    ((congrArg (fun tail => constraintMinimaHeaderChars00 ++ tail) htail).trans compactSpan139_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_139_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_140_before_prefix"
  err.flush

theorem compactSpan140_prefix :
    (compactRest00 60487).take 1 = constraintMinimaOpenChars00 := by rfl

theorem compactSpan140_split :
    compactRest00 60487 = constraintMinimaOpenChars00 ++ compactRest00 60488 := by
  calc
    compactRest00 60487 =
        (compactRest00 60487).take 1 ++ (compactRest00 60487).drop 1 :=
      (List.take_append_drop 1 (compactRest00 60487)).symm
    _ = constraintMinimaOpenChars00 ++ (compactRest00 60487).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 60487).drop 1) compactSpan140_prefix
    _ = constraintMinimaOpenChars00 ++ compactRest00 60488 :=
      congrArg (fun tail => constraintMinimaOpenChars00 ++ tail) (compactRest00_drop 60487 1)

theorem compactSpan140_rest_eq (htail : geometryChars00.drop 60488 = compactRest00 60488) :
    geometryChars00.drop 60487 = compactRest00 60487 := by
  have hp : (geometryChars00.drop 60487).take 1 = constraintMinimaOpenChars00 :=
    geometryChars00_constraintMinima_open_prefix
  exact (list_drop_split_of_prefix geometryChars00 60487 1 constraintMinimaOpenChars00 hp).trans
    ((congrArg (fun tail => constraintMinimaOpenChars00 ++ tail) htail).trans compactSpan140_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_140_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_141_before_prefix"
  err.flush

theorem compactSpan141_prefix :
    (compactRest00 60488).take 318 = constraintMinimaChunk000Chars00 := by rfl

theorem compactSpan141_split :
    compactRest00 60488 = constraintMinimaChunk000Chars00 ++ compactRest00 60806 := by
  calc
    compactRest00 60488 =
        (compactRest00 60488).take 318 ++ (compactRest00 60488).drop 318 :=
      (List.take_append_drop 318 (compactRest00 60488)).symm
    _ = constraintMinimaChunk000Chars00 ++ (compactRest00 60488).drop 318 :=
      congrArg (fun part => part ++ (compactRest00 60488).drop 318) compactSpan141_prefix
    _ = constraintMinimaChunk000Chars00 ++ compactRest00 60806 :=
      congrArg (fun tail => constraintMinimaChunk000Chars00 ++ tail) (compactRest00_drop 60488 318)

theorem compactSpan141_rest_eq (htail : geometryChars00.drop 60806 = compactRest00 60806) :
    geometryChars00.drop 60488 = compactRest00 60488 := by
  have hp : (geometryChars00.drop 60488).take 318 = constraintMinimaChunk000Chars00 :=
    geometryChars00_constraintMinima_chunk_000_prefix
  exact (list_drop_split_of_prefix geometryChars00 60488 318 constraintMinimaChunk000Chars00 hp).trans
    ((congrArg (fun tail => constraintMinimaChunk000Chars00 ++ tail) htail).trans compactSpan141_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_141_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_142_before_prefix"
  err.flush

theorem compactSpan142_prefix :
    (compactRest00 60806).take 359 = constraintMinimaChunk001Chars00 := by rfl

theorem compactSpan142_split :
    compactRest00 60806 = constraintMinimaChunk001Chars00 ++ compactRest00 61165 := by
  calc
    compactRest00 60806 =
        (compactRest00 60806).take 359 ++ (compactRest00 60806).drop 359 :=
      (List.take_append_drop 359 (compactRest00 60806)).symm
    _ = constraintMinimaChunk001Chars00 ++ (compactRest00 60806).drop 359 :=
      congrArg (fun part => part ++ (compactRest00 60806).drop 359) compactSpan142_prefix
    _ = constraintMinimaChunk001Chars00 ++ compactRest00 61165 :=
      congrArg (fun tail => constraintMinimaChunk001Chars00 ++ tail) (compactRest00_drop 60806 359)

theorem compactSpan142_rest_eq (htail : geometryChars00.drop 61165 = compactRest00 61165) :
    geometryChars00.drop 60806 = compactRest00 60806 := by
  have hp : (geometryChars00.drop 60806).take 359 = constraintMinimaChunk001Chars00 :=
    geometryChars00_constraintMinima_chunk_001_prefix
  exact (list_drop_split_of_prefix geometryChars00 60806 359 constraintMinimaChunk001Chars00 hp).trans
    ((congrArg (fun tail => constraintMinimaChunk001Chars00 ++ tail) htail).trans compactSpan142_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_142_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_143_before_prefix"
  err.flush

theorem compactSpan143_prefix :
    (compactRest00 61165).take 349 = constraintMinimaChunk002Chars00 := by rfl

theorem compactSpan143_split :
    compactRest00 61165 = constraintMinimaChunk002Chars00 ++ compactRest00 61514 := by
  calc
    compactRest00 61165 =
        (compactRest00 61165).take 349 ++ (compactRest00 61165).drop 349 :=
      (List.take_append_drop 349 (compactRest00 61165)).symm
    _ = constraintMinimaChunk002Chars00 ++ (compactRest00 61165).drop 349 :=
      congrArg (fun part => part ++ (compactRest00 61165).drop 349) compactSpan143_prefix
    _ = constraintMinimaChunk002Chars00 ++ compactRest00 61514 :=
      congrArg (fun tail => constraintMinimaChunk002Chars00 ++ tail) (compactRest00_drop 61165 349)

theorem compactSpan143_rest_eq (htail : geometryChars00.drop 61514 = compactRest00 61514) :
    geometryChars00.drop 61165 = compactRest00 61165 := by
  have hp : (geometryChars00.drop 61165).take 349 = constraintMinimaChunk002Chars00 :=
    geometryChars00_constraintMinima_chunk_002_prefix
  exact (list_drop_split_of_prefix geometryChars00 61165 349 constraintMinimaChunk002Chars00 hp).trans
    ((congrArg (fun tail => constraintMinimaChunk002Chars00 ++ tail) htail).trans compactSpan143_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_143_complete"
  err.flush

theorem group017_rest_eq
    (htail : geometryChars00.drop 61514 = compactRest00 61514) :
    geometryChars00.drop 59493 = compactRest00 59493 := by
  have h143 := compactSpan143_rest_eq htail
  have h142 := compactSpan142_rest_eq h143
  have h141 := compactSpan141_rest_eq h142
  have h140 := compactSpan140_rest_eq h141
  have h139 := compactSpan139_rest_eq h140
  have h138 := compactSpan138_rest_eq h139
  have h137 := compactSpan137_rest_eq h138
  have h136 := compactSpan136_rest_eq h137
  exact h136

#print axioms compactSpan136_prefix
#print axioms compactSpan136_split
#print axioms compactSpan136_rest_eq
#print axioms compactSpan137_prefix
#print axioms compactSpan137_split
#print axioms compactSpan137_rest_eq
#print axioms compactSpan138_prefix
#print axioms compactSpan138_split
#print axioms compactSpan138_rest_eq
#print axioms compactSpan139_prefix
#print axioms compactSpan139_split
#print axioms compactSpan139_rest_eq
#print axioms compactSpan140_prefix
#print axioms compactSpan140_split
#print axioms compactSpan140_rest_eq
#print axioms compactSpan141_prefix
#print axioms compactSpan141_split
#print axioms compactSpan141_rest_eq
#print axioms compactSpan142_prefix
#print axioms compactSpan142_split
#print axioms compactSpan142_rest_eq
#print axioms compactSpan143_prefix
#print axioms compactSpan143_split
#print axioms compactSpan143_rest_eq
#print axioms group017_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
