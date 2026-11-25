import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01200
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01300
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01400

/-! Exact compact prefix group 7, bytes [24247,28133).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_056_before_prefix"
  err.flush

theorem compactSpan056_prefix :
    (compactRest00 24247).take 533 = active8Chunk049Chars00 := by rfl

theorem compactSpan056_split :
    compactRest00 24247 = active8Chunk049Chars00 ++ compactRest00 24780 := by
  calc
    compactRest00 24247 =
        (compactRest00 24247).take 533 ++ (compactRest00 24247).drop 533 :=
      (List.take_append_drop 533 (compactRest00 24247)).symm
    _ = active8Chunk049Chars00 ++ (compactRest00 24247).drop 533 :=
      congrArg (fun part => part ++ (compactRest00 24247).drop 533) compactSpan056_prefix
    _ = active8Chunk049Chars00 ++ compactRest00 24780 :=
      congrArg (fun tail => active8Chunk049Chars00 ++ tail) (compactRest00_drop 24247 533)

theorem compactSpan056_rest_eq (htail : geometryChars00.drop 24780 = compactRest00 24780) :
    geometryChars00.drop 24247 = compactRest00 24247 := by
  have hp : (geometryChars00.drop 24247).take 533 = active8Chunk049Chars00 :=
    geometryChars00_active8_chunk_049_prefix
  exact (list_drop_split_of_prefix geometryChars00 24247 533 active8Chunk049Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk049Chars00 ++ tail) htail).trans compactSpan056_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_056_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_057_before_prefix"
  err.flush

theorem compactSpan057_prefix :
    (compactRest00 24780).take 534 = active8Chunk050Chars00 := by rfl

theorem compactSpan057_split :
    compactRest00 24780 = active8Chunk050Chars00 ++ compactRest00 25314 := by
  calc
    compactRest00 24780 =
        (compactRest00 24780).take 534 ++ (compactRest00 24780).drop 534 :=
      (List.take_append_drop 534 (compactRest00 24780)).symm
    _ = active8Chunk050Chars00 ++ (compactRest00 24780).drop 534 :=
      congrArg (fun part => part ++ (compactRest00 24780).drop 534) compactSpan057_prefix
    _ = active8Chunk050Chars00 ++ compactRest00 25314 :=
      congrArg (fun tail => active8Chunk050Chars00 ++ tail) (compactRest00_drop 24780 534)

theorem compactSpan057_rest_eq (htail : geometryChars00.drop 25314 = compactRest00 25314) :
    geometryChars00.drop 24780 = compactRest00 24780 := by
  have hp : (geometryChars00.drop 24780).take 534 = active8Chunk050Chars00 :=
    geometryChars00_active8_chunk_050_prefix
  exact (list_drop_split_of_prefix geometryChars00 24780 534 active8Chunk050Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk050Chars00 ++ tail) htail).trans compactSpan057_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_057_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_058_before_prefix"
  err.flush

theorem compactSpan058_prefix :
    (compactRest00 25314).take 482 = active8Chunk051Chars00 := by rfl

theorem compactSpan058_split :
    compactRest00 25314 = active8Chunk051Chars00 ++ compactRest00 25796 := by
  calc
    compactRest00 25314 =
        (compactRest00 25314).take 482 ++ (compactRest00 25314).drop 482 :=
      (List.take_append_drop 482 (compactRest00 25314)).symm
    _ = active8Chunk051Chars00 ++ (compactRest00 25314).drop 482 :=
      congrArg (fun part => part ++ (compactRest00 25314).drop 482) compactSpan058_prefix
    _ = active8Chunk051Chars00 ++ compactRest00 25796 :=
      congrArg (fun tail => active8Chunk051Chars00 ++ tail) (compactRest00_drop 25314 482)

theorem compactSpan058_rest_eq (htail : geometryChars00.drop 25796 = compactRest00 25796) :
    geometryChars00.drop 25314 = compactRest00 25314 := by
  have hp : (geometryChars00.drop 25314).take 482 = active8Chunk051Chars00 :=
    geometryChars00_active8_chunk_051_prefix
  exact (list_drop_split_of_prefix geometryChars00 25314 482 active8Chunk051Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk051Chars00 ++ tail) htail).trans compactSpan058_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_058_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_059_before_prefix"
  err.flush

theorem compactSpan059_prefix :
    (compactRest00 25796).take 478 = active8Chunk052Chars00 := by rfl

theorem compactSpan059_split :
    compactRest00 25796 = active8Chunk052Chars00 ++ compactRest00 26274 := by
  calc
    compactRest00 25796 =
        (compactRest00 25796).take 478 ++ (compactRest00 25796).drop 478 :=
      (List.take_append_drop 478 (compactRest00 25796)).symm
    _ = active8Chunk052Chars00 ++ (compactRest00 25796).drop 478 :=
      congrArg (fun part => part ++ (compactRest00 25796).drop 478) compactSpan059_prefix
    _ = active8Chunk052Chars00 ++ compactRest00 26274 :=
      congrArg (fun tail => active8Chunk052Chars00 ++ tail) (compactRest00_drop 25796 478)

theorem compactSpan059_rest_eq (htail : geometryChars00.drop 26274 = compactRest00 26274) :
    geometryChars00.drop 25796 = compactRest00 25796 := by
  have hp : (geometryChars00.drop 25796).take 478 = active8Chunk052Chars00 :=
    geometryChars00_active8_chunk_052_prefix
  exact (list_drop_split_of_prefix geometryChars00 25796 478 active8Chunk052Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk052Chars00 ++ tail) htail).trans compactSpan059_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_059_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_060_before_prefix"
  err.flush

theorem compactSpan060_prefix :
    (compactRest00 26274).take 427 = active8Chunk053Chars00 := by rfl

theorem compactSpan060_split :
    compactRest00 26274 = active8Chunk053Chars00 ++ compactRest00 26701 := by
  calc
    compactRest00 26274 =
        (compactRest00 26274).take 427 ++ (compactRest00 26274).drop 427 :=
      (List.take_append_drop 427 (compactRest00 26274)).symm
    _ = active8Chunk053Chars00 ++ (compactRest00 26274).drop 427 :=
      congrArg (fun part => part ++ (compactRest00 26274).drop 427) compactSpan060_prefix
    _ = active8Chunk053Chars00 ++ compactRest00 26701 :=
      congrArg (fun tail => active8Chunk053Chars00 ++ tail) (compactRest00_drop 26274 427)

theorem compactSpan060_rest_eq (htail : geometryChars00.drop 26701 = compactRest00 26701) :
    geometryChars00.drop 26274 = compactRest00 26274 := by
  have hp : (geometryChars00.drop 26274).take 427 = active8Chunk053Chars00 :=
    geometryChars00_active8_chunk_053_prefix
  exact (list_drop_split_of_prefix geometryChars00 26274 427 active8Chunk053Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk053Chars00 ++ tail) htail).trans compactSpan060_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_060_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_061_before_prefix"
  err.flush

theorem compactSpan061_prefix :
    (compactRest00 26701).take 474 = active8Chunk054Chars00 := by rfl

theorem compactSpan061_split :
    compactRest00 26701 = active8Chunk054Chars00 ++ compactRest00 27175 := by
  calc
    compactRest00 26701 =
        (compactRest00 26701).take 474 ++ (compactRest00 26701).drop 474 :=
      (List.take_append_drop 474 (compactRest00 26701)).symm
    _ = active8Chunk054Chars00 ++ (compactRest00 26701).drop 474 :=
      congrArg (fun part => part ++ (compactRest00 26701).drop 474) compactSpan061_prefix
    _ = active8Chunk054Chars00 ++ compactRest00 27175 :=
      congrArg (fun tail => active8Chunk054Chars00 ++ tail) (compactRest00_drop 26701 474)

theorem compactSpan061_rest_eq (htail : geometryChars00.drop 27175 = compactRest00 27175) :
    geometryChars00.drop 26701 = compactRest00 26701 := by
  have hp : (geometryChars00.drop 26701).take 474 = active8Chunk054Chars00 :=
    geometryChars00_active8_chunk_054_prefix
  exact (list_drop_split_of_prefix geometryChars00 26701 474 active8Chunk054Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk054Chars00 ++ tail) htail).trans compactSpan061_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_061_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_062_before_prefix"
  err.flush

theorem compactSpan062_prefix :
    (compactRest00 27175).take 426 = active8Chunk055Chars00 := by rfl

theorem compactSpan062_split :
    compactRest00 27175 = active8Chunk055Chars00 ++ compactRest00 27601 := by
  calc
    compactRest00 27175 =
        (compactRest00 27175).take 426 ++ (compactRest00 27175).drop 426 :=
      (List.take_append_drop 426 (compactRest00 27175)).symm
    _ = active8Chunk055Chars00 ++ (compactRest00 27175).drop 426 :=
      congrArg (fun part => part ++ (compactRest00 27175).drop 426) compactSpan062_prefix
    _ = active8Chunk055Chars00 ++ compactRest00 27601 :=
      congrArg (fun tail => active8Chunk055Chars00 ++ tail) (compactRest00_drop 27175 426)

theorem compactSpan062_rest_eq (htail : geometryChars00.drop 27601 = compactRest00 27601) :
    geometryChars00.drop 27175 = compactRest00 27175 := by
  have hp : (geometryChars00.drop 27175).take 426 = active8Chunk055Chars00 :=
    geometryChars00_active8_chunk_055_prefix
  exact (list_drop_split_of_prefix geometryChars00 27175 426 active8Chunk055Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk055Chars00 ++ tail) htail).trans compactSpan062_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_062_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_063_before_prefix"
  err.flush

theorem compactSpan063_prefix :
    (compactRest00 27601).take 532 = active8Chunk056Chars00 := by rfl

theorem compactSpan063_split :
    compactRest00 27601 = active8Chunk056Chars00 ++ compactRest00 28133 := by
  calc
    compactRest00 27601 =
        (compactRest00 27601).take 532 ++ (compactRest00 27601).drop 532 :=
      (List.take_append_drop 532 (compactRest00 27601)).symm
    _ = active8Chunk056Chars00 ++ (compactRest00 27601).drop 532 :=
      congrArg (fun part => part ++ (compactRest00 27601).drop 532) compactSpan063_prefix
    _ = active8Chunk056Chars00 ++ compactRest00 28133 :=
      congrArg (fun tail => active8Chunk056Chars00 ++ tail) (compactRest00_drop 27601 532)

theorem compactSpan063_rest_eq (htail : geometryChars00.drop 28133 = compactRest00 28133) :
    geometryChars00.drop 27601 = compactRest00 27601 := by
  have hp : (geometryChars00.drop 27601).take 532 = active8Chunk056Chars00 :=
    geometryChars00_active8_chunk_056_prefix
  exact (list_drop_split_of_prefix geometryChars00 27601 532 active8Chunk056Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk056Chars00 ++ tail) htail).trans compactSpan063_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_063_complete"
  err.flush

theorem group007_rest_eq
    (htail : geometryChars00.drop 28133 = compactRest00 28133) :
    geometryChars00.drop 24247 = compactRest00 24247 := by
  have h063 := compactSpan063_rest_eq htail
  have h062 := compactSpan062_rest_eq h063
  have h061 := compactSpan061_rest_eq h062
  have h060 := compactSpan060_rest_eq h061
  have h059 := compactSpan059_rest_eq h060
  have h058 := compactSpan058_rest_eq h059
  have h057 := compactSpan057_rest_eq h058
  have h056 := compactSpan056_rest_eq h057
  exact h056

#print axioms compactSpan056_prefix
#print axioms compactSpan056_split
#print axioms compactSpan056_rest_eq
#print axioms compactSpan057_prefix
#print axioms compactSpan057_split
#print axioms compactSpan057_rest_eq
#print axioms compactSpan058_prefix
#print axioms compactSpan058_split
#print axioms compactSpan058_rest_eq
#print axioms compactSpan059_prefix
#print axioms compactSpan059_split
#print axioms compactSpan059_rest_eq
#print axioms compactSpan060_prefix
#print axioms compactSpan060_split
#print axioms compactSpan060_rest_eq
#print axioms compactSpan061_prefix
#print axioms compactSpan061_split
#print axioms compactSpan061_rest_eq
#print axioms compactSpan062_prefix
#print axioms compactSpan062_split
#print axioms compactSpan062_rest_eq
#print axioms compactSpan063_prefix
#print axioms compactSpan063_split
#print axioms compactSpan063_rest_eq
#print axioms group007_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
