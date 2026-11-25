import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01800
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01900
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock02000

/-! Exact compact prefix group 10, bytes [35738,39842).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_080_before_prefix"
  err.flush

theorem compactSpan080_prefix :
    (compactRest00 35738).take 520 = active8Chunk073Chars00 := by rfl

theorem compactSpan080_split :
    compactRest00 35738 = active8Chunk073Chars00 ++ compactRest00 36258 := by
  calc
    compactRest00 35738 =
        (compactRest00 35738).take 520 ++ (compactRest00 35738).drop 520 :=
      (List.take_append_drop 520 (compactRest00 35738)).symm
    _ = active8Chunk073Chars00 ++ (compactRest00 35738).drop 520 :=
      congrArg (fun part => part ++ (compactRest00 35738).drop 520) compactSpan080_prefix
    _ = active8Chunk073Chars00 ++ compactRest00 36258 :=
      congrArg (fun tail => active8Chunk073Chars00 ++ tail) (compactRest00_drop 35738 520)

theorem compactSpan080_rest_eq (htail : geometryChars00.drop 36258 = compactRest00 36258) :
    geometryChars00.drop 35738 = compactRest00 35738 := by
  have hp : (geometryChars00.drop 35738).take 520 = active8Chunk073Chars00 :=
    geometryChars00_active8_chunk_073_prefix
  exact (list_drop_split_of_prefix geometryChars00 35738 520 active8Chunk073Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk073Chars00 ++ tail) htail).trans compactSpan080_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_080_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_081_before_prefix"
  err.flush

theorem compactSpan081_prefix :
    (compactRest00 36258).take 535 = active8Chunk074Chars00 := by rfl

theorem compactSpan081_split :
    compactRest00 36258 = active8Chunk074Chars00 ++ compactRest00 36793 := by
  calc
    compactRest00 36258 =
        (compactRest00 36258).take 535 ++ (compactRest00 36258).drop 535 :=
      (List.take_append_drop 535 (compactRest00 36258)).symm
    _ = active8Chunk074Chars00 ++ (compactRest00 36258).drop 535 :=
      congrArg (fun part => part ++ (compactRest00 36258).drop 535) compactSpan081_prefix
    _ = active8Chunk074Chars00 ++ compactRest00 36793 :=
      congrArg (fun tail => active8Chunk074Chars00 ++ tail) (compactRest00_drop 36258 535)

theorem compactSpan081_rest_eq (htail : geometryChars00.drop 36793 = compactRest00 36793) :
    geometryChars00.drop 36258 = compactRest00 36258 := by
  have hp : (geometryChars00.drop 36258).take 535 = active8Chunk074Chars00 :=
    geometryChars00_active8_chunk_074_prefix
  exact (list_drop_split_of_prefix geometryChars00 36258 535 active8Chunk074Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk074Chars00 ++ tail) htail).trans compactSpan081_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_081_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_082_before_prefix"
  err.flush

theorem compactSpan082_prefix :
    (compactRest00 36793).take 483 = active8Chunk075Chars00 := by rfl

theorem compactSpan082_split :
    compactRest00 36793 = active8Chunk075Chars00 ++ compactRest00 37276 := by
  calc
    compactRest00 36793 =
        (compactRest00 36793).take 483 ++ (compactRest00 36793).drop 483 :=
      (List.take_append_drop 483 (compactRest00 36793)).symm
    _ = active8Chunk075Chars00 ++ (compactRest00 36793).drop 483 :=
      congrArg (fun part => part ++ (compactRest00 36793).drop 483) compactSpan082_prefix
    _ = active8Chunk075Chars00 ++ compactRest00 37276 :=
      congrArg (fun tail => active8Chunk075Chars00 ++ tail) (compactRest00_drop 36793 483)

theorem compactSpan082_rest_eq (htail : geometryChars00.drop 37276 = compactRest00 37276) :
    geometryChars00.drop 36793 = compactRest00 36793 := by
  have hp : (geometryChars00.drop 36793).take 483 = active8Chunk075Chars00 :=
    geometryChars00_active8_chunk_075_prefix
  exact (list_drop_split_of_prefix geometryChars00 36793 483 active8Chunk075Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk075Chars00 ++ tail) htail).trans compactSpan082_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_082_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_083_before_prefix"
  err.flush

theorem compactSpan083_prefix :
    (compactRest00 37276).take 535 = active8Chunk076Chars00 := by rfl

theorem compactSpan083_split :
    compactRest00 37276 = active8Chunk076Chars00 ++ compactRest00 37811 := by
  calc
    compactRest00 37276 =
        (compactRest00 37276).take 535 ++ (compactRest00 37276).drop 535 :=
      (List.take_append_drop 535 (compactRest00 37276)).symm
    _ = active8Chunk076Chars00 ++ (compactRest00 37276).drop 535 :=
      congrArg (fun part => part ++ (compactRest00 37276).drop 535) compactSpan083_prefix
    _ = active8Chunk076Chars00 ++ compactRest00 37811 :=
      congrArg (fun tail => active8Chunk076Chars00 ++ tail) (compactRest00_drop 37276 535)

theorem compactSpan083_rest_eq (htail : geometryChars00.drop 37811 = compactRest00 37811) :
    geometryChars00.drop 37276 = compactRest00 37276 := by
  have hp : (geometryChars00.drop 37276).take 535 = active8Chunk076Chars00 :=
    geometryChars00_active8_chunk_076_prefix
  exact (list_drop_split_of_prefix geometryChars00 37276 535 active8Chunk076Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk076Chars00 ++ tail) htail).trans compactSpan083_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_083_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_084_before_prefix"
  err.flush

theorem compactSpan084_prefix :
    (compactRest00 37811).take 483 = active8Chunk077Chars00 := by rfl

theorem compactSpan084_split :
    compactRest00 37811 = active8Chunk077Chars00 ++ compactRest00 38294 := by
  calc
    compactRest00 37811 =
        (compactRest00 37811).take 483 ++ (compactRest00 37811).drop 483 :=
      (List.take_append_drop 483 (compactRest00 37811)).symm
    _ = active8Chunk077Chars00 ++ (compactRest00 37811).drop 483 :=
      congrArg (fun part => part ++ (compactRest00 37811).drop 483) compactSpan084_prefix
    _ = active8Chunk077Chars00 ++ compactRest00 38294 :=
      congrArg (fun tail => active8Chunk077Chars00 ++ tail) (compactRest00_drop 37811 483)

theorem compactSpan084_rest_eq (htail : geometryChars00.drop 38294 = compactRest00 38294) :
    geometryChars00.drop 37811 = compactRest00 37811 := by
  have hp : (geometryChars00.drop 37811).take 483 = active8Chunk077Chars00 :=
    geometryChars00_active8_chunk_077_prefix
  exact (list_drop_split_of_prefix geometryChars00 37811 483 active8Chunk077Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk077Chars00 ++ tail) htail).trans compactSpan084_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_084_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_085_before_prefix"
  err.flush

theorem compactSpan085_prefix :
    (compactRest00 38294).take 534 = active8Chunk078Chars00 := by rfl

theorem compactSpan085_split :
    compactRest00 38294 = active8Chunk078Chars00 ++ compactRest00 38828 := by
  calc
    compactRest00 38294 =
        (compactRest00 38294).take 534 ++ (compactRest00 38294).drop 534 :=
      (List.take_append_drop 534 (compactRest00 38294)).symm
    _ = active8Chunk078Chars00 ++ (compactRest00 38294).drop 534 :=
      congrArg (fun part => part ++ (compactRest00 38294).drop 534) compactSpan085_prefix
    _ = active8Chunk078Chars00 ++ compactRest00 38828 :=
      congrArg (fun tail => active8Chunk078Chars00 ++ tail) (compactRest00_drop 38294 534)

theorem compactSpan085_rest_eq (htail : geometryChars00.drop 38828 = compactRest00 38828) :
    geometryChars00.drop 38294 = compactRest00 38294 := by
  have hp : (geometryChars00.drop 38294).take 534 = active8Chunk078Chars00 :=
    geometryChars00_active8_chunk_078_prefix
  exact (list_drop_split_of_prefix geometryChars00 38294 534 active8Chunk078Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk078Chars00 ++ tail) htail).trans compactSpan085_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_085_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_086_before_prefix"
  err.flush

theorem compactSpan086_prefix :
    (compactRest00 38828).take 482 = active8Chunk079Chars00 := by rfl

theorem compactSpan086_split :
    compactRest00 38828 = active8Chunk079Chars00 ++ compactRest00 39310 := by
  calc
    compactRest00 38828 =
        (compactRest00 38828).take 482 ++ (compactRest00 38828).drop 482 :=
      (List.take_append_drop 482 (compactRest00 38828)).symm
    _ = active8Chunk079Chars00 ++ (compactRest00 38828).drop 482 :=
      congrArg (fun part => part ++ (compactRest00 38828).drop 482) compactSpan086_prefix
    _ = active8Chunk079Chars00 ++ compactRest00 39310 :=
      congrArg (fun tail => active8Chunk079Chars00 ++ tail) (compactRest00_drop 38828 482)

theorem compactSpan086_rest_eq (htail : geometryChars00.drop 39310 = compactRest00 39310) :
    geometryChars00.drop 38828 = compactRest00 38828 := by
  have hp : (geometryChars00.drop 38828).take 482 = active8Chunk079Chars00 :=
    geometryChars00_active8_chunk_079_prefix
  exact (list_drop_split_of_prefix geometryChars00 38828 482 active8Chunk079Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk079Chars00 ++ tail) htail).trans compactSpan086_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_086_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_087_before_prefix"
  err.flush

theorem compactSpan087_prefix :
    (compactRest00 39310).take 532 = active8Chunk080Chars00 := by rfl

theorem compactSpan087_split :
    compactRest00 39310 = active8Chunk080Chars00 ++ compactRest00 39842 := by
  calc
    compactRest00 39310 =
        (compactRest00 39310).take 532 ++ (compactRest00 39310).drop 532 :=
      (List.take_append_drop 532 (compactRest00 39310)).symm
    _ = active8Chunk080Chars00 ++ (compactRest00 39310).drop 532 :=
      congrArg (fun part => part ++ (compactRest00 39310).drop 532) compactSpan087_prefix
    _ = active8Chunk080Chars00 ++ compactRest00 39842 :=
      congrArg (fun tail => active8Chunk080Chars00 ++ tail) (compactRest00_drop 39310 532)

theorem compactSpan087_rest_eq (htail : geometryChars00.drop 39842 = compactRest00 39842) :
    geometryChars00.drop 39310 = compactRest00 39310 := by
  have hp : (geometryChars00.drop 39310).take 532 = active8Chunk080Chars00 :=
    geometryChars00_active8_chunk_080_prefix
  exact (list_drop_split_of_prefix geometryChars00 39310 532 active8Chunk080Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk080Chars00 ++ tail) htail).trans compactSpan087_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_087_complete"
  err.flush

theorem group010_rest_eq
    (htail : geometryChars00.drop 39842 = compactRest00 39842) :
    geometryChars00.drop 35738 = compactRest00 35738 := by
  have h087 := compactSpan087_rest_eq htail
  have h086 := compactSpan086_rest_eq h087
  have h085 := compactSpan085_rest_eq h086
  have h084 := compactSpan084_rest_eq h085
  have h083 := compactSpan083_rest_eq h084
  have h082 := compactSpan082_rest_eq h083
  have h081 := compactSpan081_rest_eq h082
  have h080 := compactSpan080_rest_eq h081
  exact h080

#print axioms compactSpan080_prefix
#print axioms compactSpan080_split
#print axioms compactSpan080_rest_eq
#print axioms compactSpan081_prefix
#print axioms compactSpan081_split
#print axioms compactSpan081_rest_eq
#print axioms compactSpan082_prefix
#print axioms compactSpan082_split
#print axioms compactSpan082_rest_eq
#print axioms compactSpan083_prefix
#print axioms compactSpan083_split
#print axioms compactSpan083_rest_eq
#print axioms compactSpan084_prefix
#print axioms compactSpan084_split
#print axioms compactSpan084_rest_eq
#print axioms compactSpan085_prefix
#print axioms compactSpan085_split
#print axioms compactSpan085_rest_eq
#print axioms compactSpan086_prefix
#print axioms compactSpan086_split
#print axioms compactSpan086_rest_eq
#print axioms compactSpan087_prefix
#print axioms compactSpan087_split
#print axioms compactSpan087_rest_eq
#print axioms group010_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
