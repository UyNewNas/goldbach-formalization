import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01600
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01700
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01800

/-! Exact compact prefix group 9, bytes [31843,35738).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_072_before_prefix"
  err.flush

theorem compactSpan072_prefix :
    (compactRest00 31843).take 525 = active8Chunk065Chars00 := by rfl

theorem compactSpan072_split :
    compactRest00 31843 = active8Chunk065Chars00 ++ compactRest00 32368 := by
  calc
    compactRest00 31843 =
        (compactRest00 31843).take 525 ++ (compactRest00 31843).drop 525 :=
      (List.take_append_drop 525 (compactRest00 31843)).symm
    _ = active8Chunk065Chars00 ++ (compactRest00 31843).drop 525 :=
      congrArg (fun part => part ++ (compactRest00 31843).drop 525) compactSpan072_prefix
    _ = active8Chunk065Chars00 ++ compactRest00 32368 :=
      congrArg (fun tail => active8Chunk065Chars00 ++ tail) (compactRest00_drop 31843 525)

theorem compactSpan072_rest_eq (htail : geometryChars00.drop 32368 = compactRest00 32368) :
    geometryChars00.drop 31843 = compactRest00 31843 := by
  have hp : (geometryChars00.drop 31843).take 525 = active8Chunk065Chars00 :=
    geometryChars00_active8_chunk_065_prefix
  exact (list_drop_split_of_prefix geometryChars00 31843 525 active8Chunk065Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk065Chars00 ++ tail) htail).trans compactSpan072_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_072_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_073_before_prefix"
  err.flush

theorem compactSpan073_prefix :
    (compactRest00 32368).take 520 = active8Chunk066Chars00 := by rfl

theorem compactSpan073_split :
    compactRest00 32368 = active8Chunk066Chars00 ++ compactRest00 32888 := by
  calc
    compactRest00 32368 =
        (compactRest00 32368).take 520 ++ (compactRest00 32368).drop 520 :=
      (List.take_append_drop 520 (compactRest00 32368)).symm
    _ = active8Chunk066Chars00 ++ (compactRest00 32368).drop 520 :=
      congrArg (fun part => part ++ (compactRest00 32368).drop 520) compactSpan073_prefix
    _ = active8Chunk066Chars00 ++ compactRest00 32888 :=
      congrArg (fun tail => active8Chunk066Chars00 ++ tail) (compactRest00_drop 32368 520)

theorem compactSpan073_rest_eq (htail : geometryChars00.drop 32888 = compactRest00 32888) :
    geometryChars00.drop 32368 = compactRest00 32368 := by
  have hp : (geometryChars00.drop 32368).take 520 = active8Chunk066Chars00 :=
    geometryChars00_active8_chunk_066_prefix
  exact (list_drop_split_of_prefix geometryChars00 32368 520 active8Chunk066Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk066Chars00 ++ tail) htail).trans compactSpan073_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_073_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_074_before_prefix"
  err.flush

theorem compactSpan074_prefix :
    (compactRest00 32888).take 520 = active8Chunk067Chars00 := by rfl

theorem compactSpan074_split :
    compactRest00 32888 = active8Chunk067Chars00 ++ compactRest00 33408 := by
  calc
    compactRest00 32888 =
        (compactRest00 32888).take 520 ++ (compactRest00 32888).drop 520 :=
      (List.take_append_drop 520 (compactRest00 32888)).symm
    _ = active8Chunk067Chars00 ++ (compactRest00 32888).drop 520 :=
      congrArg (fun part => part ++ (compactRest00 32888).drop 520) compactSpan074_prefix
    _ = active8Chunk067Chars00 ++ compactRest00 33408 :=
      congrArg (fun tail => active8Chunk067Chars00 ++ tail) (compactRest00_drop 32888 520)

theorem compactSpan074_rest_eq (htail : geometryChars00.drop 33408 = compactRest00 33408) :
    geometryChars00.drop 32888 = compactRest00 32888 := by
  have hp : (geometryChars00.drop 32888).take 520 = active8Chunk067Chars00 :=
    geometryChars00_active8_chunk_067_prefix
  exact (list_drop_split_of_prefix geometryChars00 32888 520 active8Chunk067Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk067Chars00 ++ tail) htail).trans compactSpan074_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_074_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_075_before_prefix"
  err.flush

theorem compactSpan075_prefix :
    (compactRest00 33408).take 525 = active8Chunk068Chars00 := by rfl

theorem compactSpan075_split :
    compactRest00 33408 = active8Chunk068Chars00 ++ compactRest00 33933 := by
  calc
    compactRest00 33408 =
        (compactRest00 33408).take 525 ++ (compactRest00 33408).drop 525 :=
      (List.take_append_drop 525 (compactRest00 33408)).symm
    _ = active8Chunk068Chars00 ++ (compactRest00 33408).drop 525 :=
      congrArg (fun part => part ++ (compactRest00 33408).drop 525) compactSpan075_prefix
    _ = active8Chunk068Chars00 ++ compactRest00 33933 :=
      congrArg (fun tail => active8Chunk068Chars00 ++ tail) (compactRest00_drop 33408 525)

theorem compactSpan075_rest_eq (htail : geometryChars00.drop 33933 = compactRest00 33933) :
    geometryChars00.drop 33408 = compactRest00 33408 := by
  have hp : (geometryChars00.drop 33408).take 525 = active8Chunk068Chars00 :=
    geometryChars00_active8_chunk_068_prefix
  exact (list_drop_split_of_prefix geometryChars00 33408 525 active8Chunk068Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk068Chars00 ++ tail) htail).trans compactSpan075_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_075_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_076_before_prefix"
  err.flush

theorem compactSpan076_prefix :
    (compactRest00 33933).take 520 = active8Chunk069Chars00 := by rfl

theorem compactSpan076_split :
    compactRest00 33933 = active8Chunk069Chars00 ++ compactRest00 34453 := by
  calc
    compactRest00 33933 =
        (compactRest00 33933).take 520 ++ (compactRest00 33933).drop 520 :=
      (List.take_append_drop 520 (compactRest00 33933)).symm
    _ = active8Chunk069Chars00 ++ (compactRest00 33933).drop 520 :=
      congrArg (fun part => part ++ (compactRest00 33933).drop 520) compactSpan076_prefix
    _ = active8Chunk069Chars00 ++ compactRest00 34453 :=
      congrArg (fun tail => active8Chunk069Chars00 ++ tail) (compactRest00_drop 33933 520)

theorem compactSpan076_rest_eq (htail : geometryChars00.drop 34453 = compactRest00 34453) :
    geometryChars00.drop 33933 = compactRest00 33933 := by
  have hp : (geometryChars00.drop 33933).take 520 = active8Chunk069Chars00 :=
    geometryChars00_active8_chunk_069_prefix
  exact (list_drop_split_of_prefix geometryChars00 33933 520 active8Chunk069Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk069Chars00 ++ tail) htail).trans compactSpan076_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_076_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_077_before_prefix"
  err.flush

theorem compactSpan077_prefix :
    (compactRest00 34453).take 455 = active8Chunk070Chars00 := by rfl

theorem compactSpan077_split :
    compactRest00 34453 = active8Chunk070Chars00 ++ compactRest00 34908 := by
  calc
    compactRest00 34453 =
        (compactRest00 34453).take 455 ++ (compactRest00 34453).drop 455 :=
      (List.take_append_drop 455 (compactRest00 34453)).symm
    _ = active8Chunk070Chars00 ++ (compactRest00 34453).drop 455 :=
      congrArg (fun part => part ++ (compactRest00 34453).drop 455) compactSpan077_prefix
    _ = active8Chunk070Chars00 ++ compactRest00 34908 :=
      congrArg (fun tail => active8Chunk070Chars00 ++ tail) (compactRest00_drop 34453 455)

theorem compactSpan077_rest_eq (htail : geometryChars00.drop 34908 = compactRest00 34908) :
    geometryChars00.drop 34453 = compactRest00 34453 := by
  have hp : (geometryChars00.drop 34453).take 455 = active8Chunk070Chars00 :=
    geometryChars00_active8_chunk_070_prefix
  exact (list_drop_split_of_prefix geometryChars00 34453 455 active8Chunk070Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk070Chars00 ++ tail) htail).trans compactSpan077_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_077_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_078_before_prefix"
  err.flush

theorem compactSpan078_prefix :
    (compactRest00 34908).take 450 = active8Chunk071Chars00 := by rfl

theorem compactSpan078_split :
    compactRest00 34908 = active8Chunk071Chars00 ++ compactRest00 35358 := by
  calc
    compactRest00 34908 =
        (compactRest00 34908).take 450 ++ (compactRest00 34908).drop 450 :=
      (List.take_append_drop 450 (compactRest00 34908)).symm
    _ = active8Chunk071Chars00 ++ (compactRest00 34908).drop 450 :=
      congrArg (fun part => part ++ (compactRest00 34908).drop 450) compactSpan078_prefix
    _ = active8Chunk071Chars00 ++ compactRest00 35358 :=
      congrArg (fun tail => active8Chunk071Chars00 ++ tail) (compactRest00_drop 34908 450)

theorem compactSpan078_rest_eq (htail : geometryChars00.drop 35358 = compactRest00 35358) :
    geometryChars00.drop 34908 = compactRest00 34908 := by
  have hp : (geometryChars00.drop 34908).take 450 = active8Chunk071Chars00 :=
    geometryChars00_active8_chunk_071_prefix
  exact (list_drop_split_of_prefix geometryChars00 34908 450 active8Chunk071Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk071Chars00 ++ tail) htail).trans compactSpan078_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_078_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_079_before_prefix"
  err.flush

theorem compactSpan079_prefix :
    (compactRest00 35358).take 380 = active8Chunk072Chars00 := by rfl

theorem compactSpan079_split :
    compactRest00 35358 = active8Chunk072Chars00 ++ compactRest00 35738 := by
  calc
    compactRest00 35358 =
        (compactRest00 35358).take 380 ++ (compactRest00 35358).drop 380 :=
      (List.take_append_drop 380 (compactRest00 35358)).symm
    _ = active8Chunk072Chars00 ++ (compactRest00 35358).drop 380 :=
      congrArg (fun part => part ++ (compactRest00 35358).drop 380) compactSpan079_prefix
    _ = active8Chunk072Chars00 ++ compactRest00 35738 :=
      congrArg (fun tail => active8Chunk072Chars00 ++ tail) (compactRest00_drop 35358 380)

theorem compactSpan079_rest_eq (htail : geometryChars00.drop 35738 = compactRest00 35738) :
    geometryChars00.drop 35358 = compactRest00 35358 := by
  have hp : (geometryChars00.drop 35358).take 380 = active8Chunk072Chars00 :=
    geometryChars00_active8_chunk_072_prefix
  exact (list_drop_split_of_prefix geometryChars00 35358 380 active8Chunk072Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk072Chars00 ++ tail) htail).trans compactSpan079_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_079_complete"
  err.flush

theorem group009_rest_eq
    (htail : geometryChars00.drop 35738 = compactRest00 35738) :
    geometryChars00.drop 31843 = compactRest00 31843 := by
  have h079 := compactSpan079_rest_eq htail
  have h078 := compactSpan078_rest_eq h079
  have h077 := compactSpan077_rest_eq h078
  have h076 := compactSpan076_rest_eq h077
  have h075 := compactSpan075_rest_eq h076
  have h074 := compactSpan074_rest_eq h075
  have h073 := compactSpan073_rest_eq h074
  have h072 := compactSpan072_rest_eq h073
  exact h072

#print axioms compactSpan072_prefix
#print axioms compactSpan072_split
#print axioms compactSpan072_rest_eq
#print axioms compactSpan073_prefix
#print axioms compactSpan073_split
#print axioms compactSpan073_rest_eq
#print axioms compactSpan074_prefix
#print axioms compactSpan074_split
#print axioms compactSpan074_rest_eq
#print axioms compactSpan075_prefix
#print axioms compactSpan075_split
#print axioms compactSpan075_rest_eq
#print axioms compactSpan076_prefix
#print axioms compactSpan076_split
#print axioms compactSpan076_rest_eq
#print axioms compactSpan077_prefix
#print axioms compactSpan077_split
#print axioms compactSpan077_rest_eq
#print axioms compactSpan078_prefix
#print axioms compactSpan078_split
#print axioms compactSpan078_rest_eq
#print axioms compactSpan079_prefix
#print axioms compactSpan079_split
#print axioms compactSpan079_rest_eq
#print axioms group009_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
