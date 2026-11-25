import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00800
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00900
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01000

/-! Exact compact prefix group 5, bytes [16490,20433).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_040_before_prefix"
  err.flush

theorem compactSpan040_prefix :
    (compactRest00 16490).take 533 = active8Chunk033Chars00 := by rfl

theorem compactSpan040_split :
    compactRest00 16490 = active8Chunk033Chars00 ++ compactRest00 17023 := by
  calc
    compactRest00 16490 =
        (compactRest00 16490).take 533 ++ (compactRest00 16490).drop 533 :=
      (List.take_append_drop 533 (compactRest00 16490)).symm
    _ = active8Chunk033Chars00 ++ (compactRest00 16490).drop 533 :=
      congrArg (fun part => part ++ (compactRest00 16490).drop 533) compactSpan040_prefix
    _ = active8Chunk033Chars00 ++ compactRest00 17023 :=
      congrArg (fun tail => active8Chunk033Chars00 ++ tail) (compactRest00_drop 16490 533)

theorem compactSpan040_rest_eq (htail : geometryChars00.drop 17023 = compactRest00 17023) :
    geometryChars00.drop 16490 = compactRest00 16490 := by
  have hp : (geometryChars00.drop 16490).take 533 = active8Chunk033Chars00 :=
    geometryChars00_active8_chunk_033_prefix
  exact (list_drop_split_of_prefix geometryChars00 16490 533 active8Chunk033Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk033Chars00 ++ tail) htail).trans compactSpan040_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_040_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_041_before_prefix"
  err.flush

theorem compactSpan041_prefix :
    (compactRest00 17023).take 481 = active8Chunk034Chars00 := by rfl

theorem compactSpan041_split :
    compactRest00 17023 = active8Chunk034Chars00 ++ compactRest00 17504 := by
  calc
    compactRest00 17023 =
        (compactRest00 17023).take 481 ++ (compactRest00 17023).drop 481 :=
      (List.take_append_drop 481 (compactRest00 17023)).symm
    _ = active8Chunk034Chars00 ++ (compactRest00 17023).drop 481 :=
      congrArg (fun part => part ++ (compactRest00 17023).drop 481) compactSpan041_prefix
    _ = active8Chunk034Chars00 ++ compactRest00 17504 :=
      congrArg (fun tail => active8Chunk034Chars00 ++ tail) (compactRest00_drop 17023 481)

theorem compactSpan041_rest_eq (htail : geometryChars00.drop 17504 = compactRest00 17504) :
    geometryChars00.drop 17023 = compactRest00 17023 := by
  have hp : (geometryChars00.drop 17023).take 481 = active8Chunk034Chars00 :=
    geometryChars00_active8_chunk_034_prefix
  exact (list_drop_split_of_prefix geometryChars00 17023 481 active8Chunk034Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk034Chars00 ++ tail) htail).trans compactSpan041_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_041_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_042_before_prefix"
  err.flush

theorem compactSpan042_prefix :
    (compactRest00 17504).take 535 = active8Chunk035Chars00 := by rfl

theorem compactSpan042_split :
    compactRest00 17504 = active8Chunk035Chars00 ++ compactRest00 18039 := by
  calc
    compactRest00 17504 =
        (compactRest00 17504).take 535 ++ (compactRest00 17504).drop 535 :=
      (List.take_append_drop 535 (compactRest00 17504)).symm
    _ = active8Chunk035Chars00 ++ (compactRest00 17504).drop 535 :=
      congrArg (fun part => part ++ (compactRest00 17504).drop 535) compactSpan042_prefix
    _ = active8Chunk035Chars00 ++ compactRest00 18039 :=
      congrArg (fun tail => active8Chunk035Chars00 ++ tail) (compactRest00_drop 17504 535)

theorem compactSpan042_rest_eq (htail : geometryChars00.drop 18039 = compactRest00 18039) :
    geometryChars00.drop 17504 = compactRest00 17504 := by
  have hp : (geometryChars00.drop 17504).take 535 = active8Chunk035Chars00 :=
    geometryChars00_active8_chunk_035_prefix
  exact (list_drop_split_of_prefix geometryChars00 17504 535 active8Chunk035Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk035Chars00 ++ tail) htail).trans compactSpan042_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_042_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_043_before_prefix"
  err.flush

theorem compactSpan043_prefix :
    (compactRest00 18039).take 533 = active8Chunk036Chars00 := by rfl

theorem compactSpan043_split :
    compactRest00 18039 = active8Chunk036Chars00 ++ compactRest00 18572 := by
  calc
    compactRest00 18039 =
        (compactRest00 18039).take 533 ++ (compactRest00 18039).drop 533 :=
      (List.take_append_drop 533 (compactRest00 18039)).symm
    _ = active8Chunk036Chars00 ++ (compactRest00 18039).drop 533 :=
      congrArg (fun part => part ++ (compactRest00 18039).drop 533) compactSpan043_prefix
    _ = active8Chunk036Chars00 ++ compactRest00 18572 :=
      congrArg (fun tail => active8Chunk036Chars00 ++ tail) (compactRest00_drop 18039 533)

theorem compactSpan043_rest_eq (htail : geometryChars00.drop 18572 = compactRest00 18572) :
    geometryChars00.drop 18039 = compactRest00 18039 := by
  have hp : (geometryChars00.drop 18039).take 533 = active8Chunk036Chars00 :=
    geometryChars00_active8_chunk_036_prefix
  exact (list_drop_split_of_prefix geometryChars00 18039 533 active8Chunk036Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk036Chars00 ++ tail) htail).trans compactSpan043_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_043_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_044_before_prefix"
  err.flush

theorem compactSpan044_prefix :
    (compactRest00 18572).take 482 = active8Chunk037Chars00 := by rfl

theorem compactSpan044_split :
    compactRest00 18572 = active8Chunk037Chars00 ++ compactRest00 19054 := by
  calc
    compactRest00 18572 =
        (compactRest00 18572).take 482 ++ (compactRest00 18572).drop 482 :=
      (List.take_append_drop 482 (compactRest00 18572)).symm
    _ = active8Chunk037Chars00 ++ (compactRest00 18572).drop 482 :=
      congrArg (fun part => part ++ (compactRest00 18572).drop 482) compactSpan044_prefix
    _ = active8Chunk037Chars00 ++ compactRest00 19054 :=
      congrArg (fun tail => active8Chunk037Chars00 ++ tail) (compactRest00_drop 18572 482)

theorem compactSpan044_rest_eq (htail : geometryChars00.drop 19054 = compactRest00 19054) :
    geometryChars00.drop 18572 = compactRest00 18572 := by
  have hp : (geometryChars00.drop 18572).take 482 = active8Chunk037Chars00 :=
    geometryChars00_active8_chunk_037_prefix
  exact (list_drop_split_of_prefix geometryChars00 18572 482 active8Chunk037Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk037Chars00 ++ tail) htail).trans compactSpan044_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_044_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_045_before_prefix"
  err.flush

theorem compactSpan045_prefix :
    (compactRest00 19054).take 478 = active8Chunk038Chars00 := by rfl

theorem compactSpan045_split :
    compactRest00 19054 = active8Chunk038Chars00 ++ compactRest00 19532 := by
  calc
    compactRest00 19054 =
        (compactRest00 19054).take 478 ++ (compactRest00 19054).drop 478 :=
      (List.take_append_drop 478 (compactRest00 19054)).symm
    _ = active8Chunk038Chars00 ++ (compactRest00 19054).drop 478 :=
      congrArg (fun part => part ++ (compactRest00 19054).drop 478) compactSpan045_prefix
    _ = active8Chunk038Chars00 ++ compactRest00 19532 :=
      congrArg (fun tail => active8Chunk038Chars00 ++ tail) (compactRest00_drop 19054 478)

theorem compactSpan045_rest_eq (htail : geometryChars00.drop 19532 = compactRest00 19532) :
    geometryChars00.drop 19054 = compactRest00 19054 := by
  have hp : (geometryChars00.drop 19054).take 478 = active8Chunk038Chars00 :=
    geometryChars00_active8_chunk_038_prefix
  exact (list_drop_split_of_prefix geometryChars00 19054 478 active8Chunk038Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk038Chars00 ++ tail) htail).trans compactSpan045_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_045_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_046_before_prefix"
  err.flush

theorem compactSpan046_prefix :
    (compactRest00 19532).take 427 = active8Chunk039Chars00 := by rfl

theorem compactSpan046_split :
    compactRest00 19532 = active8Chunk039Chars00 ++ compactRest00 19959 := by
  calc
    compactRest00 19532 =
        (compactRest00 19532).take 427 ++ (compactRest00 19532).drop 427 :=
      (List.take_append_drop 427 (compactRest00 19532)).symm
    _ = active8Chunk039Chars00 ++ (compactRest00 19532).drop 427 :=
      congrArg (fun part => part ++ (compactRest00 19532).drop 427) compactSpan046_prefix
    _ = active8Chunk039Chars00 ++ compactRest00 19959 :=
      congrArg (fun tail => active8Chunk039Chars00 ++ tail) (compactRest00_drop 19532 427)

theorem compactSpan046_rest_eq (htail : geometryChars00.drop 19959 = compactRest00 19959) :
    geometryChars00.drop 19532 = compactRest00 19532 := by
  have hp : (geometryChars00.drop 19532).take 427 = active8Chunk039Chars00 :=
    geometryChars00_active8_chunk_039_prefix
  exact (list_drop_split_of_prefix geometryChars00 19532 427 active8Chunk039Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk039Chars00 ++ tail) htail).trans compactSpan046_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_046_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_047_before_prefix"
  err.flush

theorem compactSpan047_prefix :
    (compactRest00 19959).take 474 = active8Chunk040Chars00 := by rfl

theorem compactSpan047_split :
    compactRest00 19959 = active8Chunk040Chars00 ++ compactRest00 20433 := by
  calc
    compactRest00 19959 =
        (compactRest00 19959).take 474 ++ (compactRest00 19959).drop 474 :=
      (List.take_append_drop 474 (compactRest00 19959)).symm
    _ = active8Chunk040Chars00 ++ (compactRest00 19959).drop 474 :=
      congrArg (fun part => part ++ (compactRest00 19959).drop 474) compactSpan047_prefix
    _ = active8Chunk040Chars00 ++ compactRest00 20433 :=
      congrArg (fun tail => active8Chunk040Chars00 ++ tail) (compactRest00_drop 19959 474)

theorem compactSpan047_rest_eq (htail : geometryChars00.drop 20433 = compactRest00 20433) :
    geometryChars00.drop 19959 = compactRest00 19959 := by
  have hp : (geometryChars00.drop 19959).take 474 = active8Chunk040Chars00 :=
    geometryChars00_active8_chunk_040_prefix
  exact (list_drop_split_of_prefix geometryChars00 19959 474 active8Chunk040Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk040Chars00 ++ tail) htail).trans compactSpan047_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_047_complete"
  err.flush

theorem group005_rest_eq
    (htail : geometryChars00.drop 20433 = compactRest00 20433) :
    geometryChars00.drop 16490 = compactRest00 16490 := by
  have h047 := compactSpan047_rest_eq htail
  have h046 := compactSpan046_rest_eq h047
  have h045 := compactSpan045_rest_eq h046
  have h044 := compactSpan044_rest_eq h045
  have h043 := compactSpan043_rest_eq h044
  have h042 := compactSpan042_rest_eq h043
  have h041 := compactSpan041_rest_eq h042
  have h040 := compactSpan040_rest_eq h041
  exact h040

#print axioms compactSpan040_prefix
#print axioms compactSpan040_split
#print axioms compactSpan040_rest_eq
#print axioms compactSpan041_prefix
#print axioms compactSpan041_split
#print axioms compactSpan041_rest_eq
#print axioms compactSpan042_prefix
#print axioms compactSpan042_split
#print axioms compactSpan042_rest_eq
#print axioms compactSpan043_prefix
#print axioms compactSpan043_split
#print axioms compactSpan043_rest_eq
#print axioms compactSpan044_prefix
#print axioms compactSpan044_split
#print axioms compactSpan044_rest_eq
#print axioms compactSpan045_prefix
#print axioms compactSpan045_split
#print axioms compactSpan045_rest_eq
#print axioms compactSpan046_prefix
#print axioms compactSpan046_split
#print axioms compactSpan046_rest_eq
#print axioms compactSpan047_prefix
#print axioms compactSpan047_split
#print axioms compactSpan047_rest_eq
#print axioms group005_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
