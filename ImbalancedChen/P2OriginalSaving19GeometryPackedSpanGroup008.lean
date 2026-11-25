import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01400
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01500
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01600

/-! Exact compact prefix group 8, bytes [28133,31843).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_064_before_prefix"
  err.flush

theorem compactSpan064_prefix :
    (compactRest00 28133).take 527 = active8Chunk057Chars00 := by rfl

theorem compactSpan064_split :
    compactRest00 28133 = active8Chunk057Chars00 ++ compactRest00 28660 := by
  calc
    compactRest00 28133 =
        (compactRest00 28133).take 527 ++ (compactRest00 28133).drop 527 :=
      (List.take_append_drop 527 (compactRest00 28133)).symm
    _ = active8Chunk057Chars00 ++ (compactRest00 28133).drop 527 :=
      congrArg (fun part => part ++ (compactRest00 28133).drop 527) compactSpan064_prefix
    _ = active8Chunk057Chars00 ++ compactRest00 28660 :=
      congrArg (fun tail => active8Chunk057Chars00 ++ tail) (compactRest00_drop 28133 527)

theorem compactSpan064_rest_eq (htail : geometryChars00.drop 28660 = compactRest00 28660) :
    geometryChars00.drop 28133 = compactRest00 28133 := by
  have hp : (geometryChars00.drop 28133).take 527 = active8Chunk057Chars00 :=
    geometryChars00_active8_chunk_057_prefix
  exact (list_drop_split_of_prefix geometryChars00 28133 527 active8Chunk057Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk057Chars00 ++ tail) htail).trans compactSpan064_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_064_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_065_before_prefix"
  err.flush

theorem compactSpan065_prefix :
    (compactRest00 28660).take 458 = active8Chunk058Chars00 := by rfl

theorem compactSpan065_split :
    compactRest00 28660 = active8Chunk058Chars00 ++ compactRest00 29118 := by
  calc
    compactRest00 28660 =
        (compactRest00 28660).take 458 ++ (compactRest00 28660).drop 458 :=
      (List.take_append_drop 458 (compactRest00 28660)).symm
    _ = active8Chunk058Chars00 ++ (compactRest00 28660).drop 458 :=
      congrArg (fun part => part ++ (compactRest00 28660).drop 458) compactSpan065_prefix
    _ = active8Chunk058Chars00 ++ compactRest00 29118 :=
      congrArg (fun tail => active8Chunk058Chars00 ++ tail) (compactRest00_drop 28660 458)

theorem compactSpan065_rest_eq (htail : geometryChars00.drop 29118 = compactRest00 29118) :
    geometryChars00.drop 28660 = compactRest00 28660 := by
  have hp : (geometryChars00.drop 28660).take 458 = active8Chunk058Chars00 :=
    geometryChars00_active8_chunk_058_prefix
  exact (list_drop_split_of_prefix geometryChars00 28660 458 active8Chunk058Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk058Chars00 ++ tail) htail).trans compactSpan065_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_065_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_066_before_prefix"
  err.flush

theorem compactSpan066_prefix :
    (compactRest00 29118).take 534 = active8Chunk059Chars00 := by rfl

theorem compactSpan066_split :
    compactRest00 29118 = active8Chunk059Chars00 ++ compactRest00 29652 := by
  calc
    compactRest00 29118 =
        (compactRest00 29118).take 534 ++ (compactRest00 29118).drop 534 :=
      (List.take_append_drop 534 (compactRest00 29118)).symm
    _ = active8Chunk059Chars00 ++ (compactRest00 29118).drop 534 :=
      congrArg (fun part => part ++ (compactRest00 29118).drop 534) compactSpan066_prefix
    _ = active8Chunk059Chars00 ++ compactRest00 29652 :=
      congrArg (fun tail => active8Chunk059Chars00 ++ tail) (compactRest00_drop 29118 534)

theorem compactSpan066_rest_eq (htail : geometryChars00.drop 29652 = compactRest00 29652) :
    geometryChars00.drop 29118 = compactRest00 29118 := by
  have hp : (geometryChars00.drop 29118).take 534 = active8Chunk059Chars00 :=
    geometryChars00_active8_chunk_059_prefix
  exact (list_drop_split_of_prefix geometryChars00 29118 534 active8Chunk059Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk059Chars00 ++ tail) htail).trans compactSpan066_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_066_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_067_before_prefix"
  err.flush

theorem compactSpan067_prefix :
    (compactRest00 29652).take 450 = active8Chunk060Chars00 := by rfl

theorem compactSpan067_split :
    compactRest00 29652 = active8Chunk060Chars00 ++ compactRest00 30102 := by
  calc
    compactRest00 29652 =
        (compactRest00 29652).take 450 ++ (compactRest00 29652).drop 450 :=
      (List.take_append_drop 450 (compactRest00 29652)).symm
    _ = active8Chunk060Chars00 ++ (compactRest00 29652).drop 450 :=
      congrArg (fun part => part ++ (compactRest00 29652).drop 450) compactSpan067_prefix
    _ = active8Chunk060Chars00 ++ compactRest00 30102 :=
      congrArg (fun tail => active8Chunk060Chars00 ++ tail) (compactRest00_drop 29652 450)

theorem compactSpan067_rest_eq (htail : geometryChars00.drop 30102 = compactRest00 30102) :
    geometryChars00.drop 29652 = compactRest00 29652 := by
  have hp : (geometryChars00.drop 29652).take 450 = active8Chunk060Chars00 :=
    geometryChars00_active8_chunk_060_prefix
  exact (list_drop_split_of_prefix geometryChars00 29652 450 active8Chunk060Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk060Chars00 ++ tail) htail).trans compactSpan067_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_067_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_068_before_prefix"
  err.flush

theorem compactSpan068_prefix :
    (compactRest00 30102).take 456 = active8Chunk061Chars00 := by rfl

theorem compactSpan068_split :
    compactRest00 30102 = active8Chunk061Chars00 ++ compactRest00 30558 := by
  calc
    compactRest00 30102 =
        (compactRest00 30102).take 456 ++ (compactRest00 30102).drop 456 :=
      (List.take_append_drop 456 (compactRest00 30102)).symm
    _ = active8Chunk061Chars00 ++ (compactRest00 30102).drop 456 :=
      congrArg (fun part => part ++ (compactRest00 30102).drop 456) compactSpan068_prefix
    _ = active8Chunk061Chars00 ++ compactRest00 30558 :=
      congrArg (fun tail => active8Chunk061Chars00 ++ tail) (compactRest00_drop 30102 456)

theorem compactSpan068_rest_eq (htail : geometryChars00.drop 30558 = compactRest00 30558) :
    geometryChars00.drop 30102 = compactRest00 30102 := by
  have hp : (geometryChars00.drop 30102).take 456 = active8Chunk061Chars00 :=
    geometryChars00_active8_chunk_061_prefix
  exact (list_drop_split_of_prefix geometryChars00 30102 456 active8Chunk061Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk061Chars00 ++ tail) htail).trans compactSpan068_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_068_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_069_before_prefix"
  err.flush

theorem compactSpan069_prefix :
    (compactRest00 30558).take 450 = active8Chunk062Chars00 := by rfl

theorem compactSpan069_split :
    compactRest00 30558 = active8Chunk062Chars00 ++ compactRest00 31008 := by
  calc
    compactRest00 30558 =
        (compactRest00 30558).take 450 ++ (compactRest00 30558).drop 450 :=
      (List.take_append_drop 450 (compactRest00 30558)).symm
    _ = active8Chunk062Chars00 ++ (compactRest00 30558).drop 450 :=
      congrArg (fun part => part ++ (compactRest00 30558).drop 450) compactSpan069_prefix
    _ = active8Chunk062Chars00 ++ compactRest00 31008 :=
      congrArg (fun tail => active8Chunk062Chars00 ++ tail) (compactRest00_drop 30558 450)

theorem compactSpan069_rest_eq (htail : geometryChars00.drop 31008 = compactRest00 31008) :
    geometryChars00.drop 30558 = compactRest00 30558 := by
  have hp : (geometryChars00.drop 30558).take 450 = active8Chunk062Chars00 :=
    geometryChars00_active8_chunk_062_prefix
  exact (list_drop_split_of_prefix geometryChars00 30558 450 active8Chunk062Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk062Chars00 ++ tail) htail).trans compactSpan069_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_069_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_070_before_prefix"
  err.flush

theorem compactSpan070_prefix :
    (compactRest00 31008).take 455 = active8Chunk063Chars00 := by rfl

theorem compactSpan070_split :
    compactRest00 31008 = active8Chunk063Chars00 ++ compactRest00 31463 := by
  calc
    compactRest00 31008 =
        (compactRest00 31008).take 455 ++ (compactRest00 31008).drop 455 :=
      (List.take_append_drop 455 (compactRest00 31008)).symm
    _ = active8Chunk063Chars00 ++ (compactRest00 31008).drop 455 :=
      congrArg (fun part => part ++ (compactRest00 31008).drop 455) compactSpan070_prefix
    _ = active8Chunk063Chars00 ++ compactRest00 31463 :=
      congrArg (fun tail => active8Chunk063Chars00 ++ tail) (compactRest00_drop 31008 455)

theorem compactSpan070_rest_eq (htail : geometryChars00.drop 31463 = compactRest00 31463) :
    geometryChars00.drop 31008 = compactRest00 31008 := by
  have hp : (geometryChars00.drop 31008).take 455 = active8Chunk063Chars00 :=
    geometryChars00_active8_chunk_063_prefix
  exact (list_drop_split_of_prefix geometryChars00 31008 455 active8Chunk063Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk063Chars00 ++ tail) htail).trans compactSpan070_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_070_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_071_before_prefix"
  err.flush

theorem compactSpan071_prefix :
    (compactRest00 31463).take 380 = active8Chunk064Chars00 := by rfl

theorem compactSpan071_split :
    compactRest00 31463 = active8Chunk064Chars00 ++ compactRest00 31843 := by
  calc
    compactRest00 31463 =
        (compactRest00 31463).take 380 ++ (compactRest00 31463).drop 380 :=
      (List.take_append_drop 380 (compactRest00 31463)).symm
    _ = active8Chunk064Chars00 ++ (compactRest00 31463).drop 380 :=
      congrArg (fun part => part ++ (compactRest00 31463).drop 380) compactSpan071_prefix
    _ = active8Chunk064Chars00 ++ compactRest00 31843 :=
      congrArg (fun tail => active8Chunk064Chars00 ++ tail) (compactRest00_drop 31463 380)

theorem compactSpan071_rest_eq (htail : geometryChars00.drop 31843 = compactRest00 31843) :
    geometryChars00.drop 31463 = compactRest00 31463 := by
  have hp : (geometryChars00.drop 31463).take 380 = active8Chunk064Chars00 :=
    geometryChars00_active8_chunk_064_prefix
  exact (list_drop_split_of_prefix geometryChars00 31463 380 active8Chunk064Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk064Chars00 ++ tail) htail).trans compactSpan071_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_071_complete"
  err.flush

theorem group008_rest_eq
    (htail : geometryChars00.drop 31843 = compactRest00 31843) :
    geometryChars00.drop 28133 = compactRest00 28133 := by
  have h071 := compactSpan071_rest_eq htail
  have h070 := compactSpan070_rest_eq h071
  have h069 := compactSpan069_rest_eq h070
  have h068 := compactSpan068_rest_eq h069
  have h067 := compactSpan067_rest_eq h068
  have h066 := compactSpan066_rest_eq h067
  have h065 := compactSpan065_rest_eq h066
  have h064 := compactSpan064_rest_eq h065
  exact h064

#print axioms compactSpan064_prefix
#print axioms compactSpan064_split
#print axioms compactSpan064_rest_eq
#print axioms compactSpan065_prefix
#print axioms compactSpan065_split
#print axioms compactSpan065_rest_eq
#print axioms compactSpan066_prefix
#print axioms compactSpan066_split
#print axioms compactSpan066_rest_eq
#print axioms compactSpan067_prefix
#print axioms compactSpan067_split
#print axioms compactSpan067_rest_eq
#print axioms compactSpan068_prefix
#print axioms compactSpan068_split
#print axioms compactSpan068_rest_eq
#print axioms compactSpan069_prefix
#print axioms compactSpan069_split
#print axioms compactSpan069_rest_eq
#print axioms compactSpan070_prefix
#print axioms compactSpan070_split
#print axioms compactSpan070_rest_eq
#print axioms compactSpan071_prefix
#print axioms compactSpan071_split
#print axioms compactSpan071_rest_eq
#print axioms group008_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
