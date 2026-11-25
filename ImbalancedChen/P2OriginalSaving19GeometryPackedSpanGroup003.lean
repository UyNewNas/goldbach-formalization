import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00400
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00500
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00600

/-! Exact compact prefix group 3, bytes [8807,12542).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_024_before_prefix"
  err.flush

theorem compactSpan024_prefix :
    (compactRest00 8807).take 516 = active8Chunk017Chars00 := by rfl

theorem compactSpan024_split :
    compactRest00 8807 = active8Chunk017Chars00 ++ compactRest00 9323 := by
  calc
    compactRest00 8807 =
        (compactRest00 8807).take 516 ++ (compactRest00 8807).drop 516 :=
      (List.take_append_drop 516 (compactRest00 8807)).symm
    _ = active8Chunk017Chars00 ++ (compactRest00 8807).drop 516 :=
      congrArg (fun part => part ++ (compactRest00 8807).drop 516) compactSpan024_prefix
    _ = active8Chunk017Chars00 ++ compactRest00 9323 :=
      congrArg (fun tail => active8Chunk017Chars00 ++ tail) (compactRest00_drop 8807 516)

theorem compactSpan024_rest_eq (htail : geometryChars00.drop 9323 = compactRest00 9323) :
    geometryChars00.drop 8807 = compactRest00 8807 := by
  have hp : (geometryChars00.drop 8807).take 516 = active8Chunk017Chars00 :=
    geometryChars00_active8_chunk_017_prefix
  exact (list_drop_split_of_prefix geometryChars00 8807 516 active8Chunk017Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk017Chars00 ++ tail) htail).trans compactSpan024_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_024_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_025_before_prefix"
  err.flush

theorem compactSpan025_prefix :
    (compactRest00 9323).take 448 = active8Chunk018Chars00 := by rfl

theorem compactSpan025_split :
    compactRest00 9323 = active8Chunk018Chars00 ++ compactRest00 9771 := by
  calc
    compactRest00 9323 =
        (compactRest00 9323).take 448 ++ (compactRest00 9323).drop 448 :=
      (List.take_append_drop 448 (compactRest00 9323)).symm
    _ = active8Chunk018Chars00 ++ (compactRest00 9323).drop 448 :=
      congrArg (fun part => part ++ (compactRest00 9323).drop 448) compactSpan025_prefix
    _ = active8Chunk018Chars00 ++ compactRest00 9771 :=
      congrArg (fun tail => active8Chunk018Chars00 ++ tail) (compactRest00_drop 9323 448)

theorem compactSpan025_rest_eq (htail : geometryChars00.drop 9771 = compactRest00 9771) :
    geometryChars00.drop 9323 = compactRest00 9323 := by
  have hp : (geometryChars00.drop 9323).take 448 = active8Chunk018Chars00 :=
    geometryChars00_active8_chunk_018_prefix
  exact (list_drop_split_of_prefix geometryChars00 9323 448 active8Chunk018Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk018Chars00 ++ tail) htail).trans compactSpan025_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_025_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_026_before_prefix"
  err.flush

theorem compactSpan026_prefix :
    (compactRest00 9771).take 452 = active8Chunk019Chars00 := by rfl

theorem compactSpan026_split :
    compactRest00 9771 = active8Chunk019Chars00 ++ compactRest00 10223 := by
  calc
    compactRest00 9771 =
        (compactRest00 9771).take 452 ++ (compactRest00 9771).drop 452 :=
      (List.take_append_drop 452 (compactRest00 9771)).symm
    _ = active8Chunk019Chars00 ++ (compactRest00 9771).drop 452 :=
      congrArg (fun part => part ++ (compactRest00 9771).drop 452) compactSpan026_prefix
    _ = active8Chunk019Chars00 ++ compactRest00 10223 :=
      congrArg (fun tail => active8Chunk019Chars00 ++ tail) (compactRest00_drop 9771 452)

theorem compactSpan026_rest_eq (htail : geometryChars00.drop 10223 = compactRest00 10223) :
    geometryChars00.drop 9771 = compactRest00 9771 := by
  have hp : (geometryChars00.drop 9771).take 452 = active8Chunk019Chars00 :=
    geometryChars00_active8_chunk_019_prefix
  exact (list_drop_split_of_prefix geometryChars00 9771 452 active8Chunk019Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk019Chars00 ++ tail) htail).trans compactSpan026_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_026_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_027_before_prefix"
  err.flush

theorem compactSpan027_prefix :
    (compactRest00 10223).take 378 = active8Chunk020Chars00 := by rfl

theorem compactSpan027_split :
    compactRest00 10223 = active8Chunk020Chars00 ++ compactRest00 10601 := by
  calc
    compactRest00 10223 =
        (compactRest00 10223).take 378 ++ (compactRest00 10223).drop 378 :=
      (List.take_append_drop 378 (compactRest00 10223)).symm
    _ = active8Chunk020Chars00 ++ (compactRest00 10223).drop 378 :=
      congrArg (fun part => part ++ (compactRest00 10223).drop 378) compactSpan027_prefix
    _ = active8Chunk020Chars00 ++ compactRest00 10601 :=
      congrArg (fun tail => active8Chunk020Chars00 ++ tail) (compactRest00_drop 10223 378)

theorem compactSpan027_rest_eq (htail : geometryChars00.drop 10601 = compactRest00 10601) :
    geometryChars00.drop 10223 = compactRest00 10223 := by
  have hp : (geometryChars00.drop 10223).take 378 = active8Chunk020Chars00 :=
    geometryChars00_active8_chunk_020_prefix
  exact (list_drop_split_of_prefix geometryChars00 10223 378 active8Chunk020Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk020Chars00 ++ tail) htail).trans compactSpan027_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_027_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_028_before_prefix"
  err.flush

theorem compactSpan028_prefix :
    (compactRest00 10601).take 448 = active8Chunk021Chars00 := by rfl

theorem compactSpan028_split :
    compactRest00 10601 = active8Chunk021Chars00 ++ compactRest00 11049 := by
  calc
    compactRest00 10601 =
        (compactRest00 10601).take 448 ++ (compactRest00 10601).drop 448 :=
      (List.take_append_drop 448 (compactRest00 10601)).symm
    _ = active8Chunk021Chars00 ++ (compactRest00 10601).drop 448 :=
      congrArg (fun part => part ++ (compactRest00 10601).drop 448) compactSpan028_prefix
    _ = active8Chunk021Chars00 ++ compactRest00 11049 :=
      congrArg (fun tail => active8Chunk021Chars00 ++ tail) (compactRest00_drop 10601 448)

theorem compactSpan028_rest_eq (htail : geometryChars00.drop 11049 = compactRest00 11049) :
    geometryChars00.drop 10601 = compactRest00 10601 := by
  have hp : (geometryChars00.drop 10601).take 448 = active8Chunk021Chars00 :=
    geometryChars00_active8_chunk_021_prefix
  exact (list_drop_split_of_prefix geometryChars00 10601 448 active8Chunk021Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk021Chars00 ++ tail) htail).trans compactSpan028_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_028_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_029_before_prefix"
  err.flush

theorem compactSpan029_prefix :
    (compactRest00 11049).take 448 = active8Chunk022Chars00 := by rfl

theorem compactSpan029_split :
    compactRest00 11049 = active8Chunk022Chars00 ++ compactRest00 11497 := by
  calc
    compactRest00 11049 =
        (compactRest00 11049).take 448 ++ (compactRest00 11049).drop 448 :=
      (List.take_append_drop 448 (compactRest00 11049)).symm
    _ = active8Chunk022Chars00 ++ (compactRest00 11049).drop 448 :=
      congrArg (fun part => part ++ (compactRest00 11049).drop 448) compactSpan029_prefix
    _ = active8Chunk022Chars00 ++ compactRest00 11497 :=
      congrArg (fun tail => active8Chunk022Chars00 ++ tail) (compactRest00_drop 11049 448)

theorem compactSpan029_rest_eq (htail : geometryChars00.drop 11497 = compactRest00 11497) :
    geometryChars00.drop 11049 = compactRest00 11049 := by
  have hp : (geometryChars00.drop 11049).take 448 = active8Chunk022Chars00 :=
    geometryChars00_active8_chunk_022_prefix
  exact (list_drop_split_of_prefix geometryChars00 11049 448 active8Chunk022Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk022Chars00 ++ tail) htail).trans compactSpan029_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_029_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_030_before_prefix"
  err.flush

theorem compactSpan030_prefix :
    (compactRest00 11497).take 524 = active8Chunk023Chars00 := by rfl

theorem compactSpan030_split :
    compactRest00 11497 = active8Chunk023Chars00 ++ compactRest00 12021 := by
  calc
    compactRest00 11497 =
        (compactRest00 11497).take 524 ++ (compactRest00 11497).drop 524 :=
      (List.take_append_drop 524 (compactRest00 11497)).symm
    _ = active8Chunk023Chars00 ++ (compactRest00 11497).drop 524 :=
      congrArg (fun part => part ++ (compactRest00 11497).drop 524) compactSpan030_prefix
    _ = active8Chunk023Chars00 ++ compactRest00 12021 :=
      congrArg (fun tail => active8Chunk023Chars00 ++ tail) (compactRest00_drop 11497 524)

theorem compactSpan030_rest_eq (htail : geometryChars00.drop 12021 = compactRest00 12021) :
    geometryChars00.drop 11497 = compactRest00 11497 := by
  have hp : (geometryChars00.drop 11497).take 524 = active8Chunk023Chars00 :=
    geometryChars00_active8_chunk_023_prefix
  exact (list_drop_split_of_prefix geometryChars00 11497 524 active8Chunk023Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk023Chars00 ++ tail) htail).trans compactSpan030_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_030_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_031_before_prefix"
  err.flush

theorem compactSpan031_prefix :
    (compactRest00 12021).take 521 = active8Chunk024Chars00 := by rfl

theorem compactSpan031_split :
    compactRest00 12021 = active8Chunk024Chars00 ++ compactRest00 12542 := by
  calc
    compactRest00 12021 =
        (compactRest00 12021).take 521 ++ (compactRest00 12021).drop 521 :=
      (List.take_append_drop 521 (compactRest00 12021)).symm
    _ = active8Chunk024Chars00 ++ (compactRest00 12021).drop 521 :=
      congrArg (fun part => part ++ (compactRest00 12021).drop 521) compactSpan031_prefix
    _ = active8Chunk024Chars00 ++ compactRest00 12542 :=
      congrArg (fun tail => active8Chunk024Chars00 ++ tail) (compactRest00_drop 12021 521)

theorem compactSpan031_rest_eq (htail : geometryChars00.drop 12542 = compactRest00 12542) :
    geometryChars00.drop 12021 = compactRest00 12021 := by
  have hp : (geometryChars00.drop 12021).take 521 = active8Chunk024Chars00 :=
    geometryChars00_active8_chunk_024_prefix
  exact (list_drop_split_of_prefix geometryChars00 12021 521 active8Chunk024Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk024Chars00 ++ tail) htail).trans compactSpan031_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_031_complete"
  err.flush

theorem group003_rest_eq
    (htail : geometryChars00.drop 12542 = compactRest00 12542) :
    geometryChars00.drop 8807 = compactRest00 8807 := by
  have h031 := compactSpan031_rest_eq htail
  have h030 := compactSpan030_rest_eq h031
  have h029 := compactSpan029_rest_eq h030
  have h028 := compactSpan028_rest_eq h029
  have h027 := compactSpan027_rest_eq h028
  have h026 := compactSpan026_rest_eq h027
  have h025 := compactSpan025_rest_eq h026
  have h024 := compactSpan024_rest_eq h025
  exact h024

#print axioms compactSpan024_prefix
#print axioms compactSpan024_split
#print axioms compactSpan024_rest_eq
#print axioms compactSpan025_prefix
#print axioms compactSpan025_split
#print axioms compactSpan025_rest_eq
#print axioms compactSpan026_prefix
#print axioms compactSpan026_split
#print axioms compactSpan026_rest_eq
#print axioms compactSpan027_prefix
#print axioms compactSpan027_split
#print axioms compactSpan027_rest_eq
#print axioms compactSpan028_prefix
#print axioms compactSpan028_split
#print axioms compactSpan028_rest_eq
#print axioms compactSpan029_prefix
#print axioms compactSpan029_split
#print axioms compactSpan029_rest_eq
#print axioms compactSpan030_prefix
#print axioms compactSpan030_split
#print axioms compactSpan030_rest_eq
#print axioms compactSpan031_prefix
#print axioms compactSpan031_split
#print axioms compactSpan031_rest_eq
#print axioms group003_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
