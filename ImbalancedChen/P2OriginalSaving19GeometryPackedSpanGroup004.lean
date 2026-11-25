import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00600
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00700
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00800

/-! Exact compact prefix group 4, bytes [12542,16490).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_032_before_prefix"
  err.flush

theorem compactSpan032_prefix :
    (compactRest00 12542).take 524 = active8Chunk025Chars00 := by rfl

theorem compactSpan032_split :
    compactRest00 12542 = active8Chunk025Chars00 ++ compactRest00 13066 := by
  calc
    compactRest00 12542 =
        (compactRest00 12542).take 524 ++ (compactRest00 12542).drop 524 :=
      (List.take_append_drop 524 (compactRest00 12542)).symm
    _ = active8Chunk025Chars00 ++ (compactRest00 12542).drop 524 :=
      congrArg (fun part => part ++ (compactRest00 12542).drop 524) compactSpan032_prefix
    _ = active8Chunk025Chars00 ++ compactRest00 13066 :=
      congrArg (fun tail => active8Chunk025Chars00 ++ tail) (compactRest00_drop 12542 524)

theorem compactSpan032_rest_eq (htail : geometryChars00.drop 13066 = compactRest00 13066) :
    geometryChars00.drop 12542 = compactRest00 12542 := by
  have hp : (geometryChars00.drop 12542).take 524 = active8Chunk025Chars00 :=
    geometryChars00_active8_chunk_025_prefix
  exact (list_drop_split_of_prefix geometryChars00 12542 524 active8Chunk025Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk025Chars00 ++ tail) htail).trans compactSpan032_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_032_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_033_before_prefix"
  err.flush

theorem compactSpan033_prefix :
    (compactRest00 13066).take 522 = active8Chunk026Chars00 := by rfl

theorem compactSpan033_split :
    compactRest00 13066 = active8Chunk026Chars00 ++ compactRest00 13588 := by
  calc
    compactRest00 13066 =
        (compactRest00 13066).take 522 ++ (compactRest00 13066).drop 522 :=
      (List.take_append_drop 522 (compactRest00 13066)).symm
    _ = active8Chunk026Chars00 ++ (compactRest00 13066).drop 522 :=
      congrArg (fun part => part ++ (compactRest00 13066).drop 522) compactSpan033_prefix
    _ = active8Chunk026Chars00 ++ compactRest00 13588 :=
      congrArg (fun tail => active8Chunk026Chars00 ++ tail) (compactRest00_drop 13066 522)

theorem compactSpan033_rest_eq (htail : geometryChars00.drop 13588 = compactRest00 13588) :
    geometryChars00.drop 13066 = compactRest00 13066 := by
  have hp : (geometryChars00.drop 13066).take 522 = active8Chunk026Chars00 :=
    geometryChars00_active8_chunk_026_prefix
  exact (list_drop_split_of_prefix geometryChars00 13066 522 active8Chunk026Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk026Chars00 ++ tail) htail).trans compactSpan033_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_033_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_034_before_prefix"
  err.flush

theorem compactSpan034_prefix :
    (compactRest00 13588).take 524 = active8Chunk027Chars00 := by rfl

theorem compactSpan034_split :
    compactRest00 13588 = active8Chunk027Chars00 ++ compactRest00 14112 := by
  calc
    compactRest00 13588 =
        (compactRest00 13588).take 524 ++ (compactRest00 13588).drop 524 :=
      (List.take_append_drop 524 (compactRest00 13588)).symm
    _ = active8Chunk027Chars00 ++ (compactRest00 13588).drop 524 :=
      congrArg (fun part => part ++ (compactRest00 13588).drop 524) compactSpan034_prefix
    _ = active8Chunk027Chars00 ++ compactRest00 14112 :=
      congrArg (fun tail => active8Chunk027Chars00 ++ tail) (compactRest00_drop 13588 524)

theorem compactSpan034_rest_eq (htail : geometryChars00.drop 14112 = compactRest00 14112) :
    geometryChars00.drop 13588 = compactRest00 13588 := by
  have hp : (geometryChars00.drop 13588).take 524 = active8Chunk027Chars00 :=
    geometryChars00_active8_chunk_027_prefix
  exact (list_drop_split_of_prefix geometryChars00 13588 524 active8Chunk027Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk027Chars00 ++ tail) htail).trans compactSpan034_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_034_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_035_before_prefix"
  err.flush

theorem compactSpan035_prefix :
    (compactRest00 14112).take 458 = active8Chunk028Chars00 := by rfl

theorem compactSpan035_split :
    compactRest00 14112 = active8Chunk028Chars00 ++ compactRest00 14570 := by
  calc
    compactRest00 14112 =
        (compactRest00 14112).take 458 ++ (compactRest00 14112).drop 458 :=
      (List.take_append_drop 458 (compactRest00 14112)).symm
    _ = active8Chunk028Chars00 ++ (compactRest00 14112).drop 458 :=
      congrArg (fun part => part ++ (compactRest00 14112).drop 458) compactSpan035_prefix
    _ = active8Chunk028Chars00 ++ compactRest00 14570 :=
      congrArg (fun tail => active8Chunk028Chars00 ++ tail) (compactRest00_drop 14112 458)

theorem compactSpan035_rest_eq (htail : geometryChars00.drop 14570 = compactRest00 14570) :
    geometryChars00.drop 14112 = compactRest00 14112 := by
  have hp : (geometryChars00.drop 14112).take 458 = active8Chunk028Chars00 :=
    geometryChars00_active8_chunk_028_prefix
  exact (list_drop_split_of_prefix geometryChars00 14112 458 active8Chunk028Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk028Chars00 ++ tail) htail).trans compactSpan035_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_035_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_036_before_prefix"
  err.flush

theorem compactSpan036_prefix :
    (compactRest00 14570).take 481 = active8Chunk029Chars00 := by rfl

theorem compactSpan036_split :
    compactRest00 14570 = active8Chunk029Chars00 ++ compactRest00 15051 := by
  calc
    compactRest00 14570 =
        (compactRest00 14570).take 481 ++ (compactRest00 14570).drop 481 :=
      (List.take_append_drop 481 (compactRest00 14570)).symm
    _ = active8Chunk029Chars00 ++ (compactRest00 14570).drop 481 :=
      congrArg (fun part => part ++ (compactRest00 14570).drop 481) compactSpan036_prefix
    _ = active8Chunk029Chars00 ++ compactRest00 15051 :=
      congrArg (fun tail => active8Chunk029Chars00 ++ tail) (compactRest00_drop 14570 481)

theorem compactSpan036_rest_eq (htail : geometryChars00.drop 15051 = compactRest00 15051) :
    geometryChars00.drop 14570 = compactRest00 14570 := by
  have hp : (geometryChars00.drop 14570).take 481 = active8Chunk029Chars00 :=
    geometryChars00_active8_chunk_029_prefix
  exact (list_drop_split_of_prefix geometryChars00 14570 481 active8Chunk029Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk029Chars00 ++ tail) htail).trans compactSpan036_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_036_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_037_before_prefix"
  err.flush

theorem compactSpan037_prefix :
    (compactRest00 15051).take 428 = active8Chunk030Chars00 := by rfl

theorem compactSpan037_split :
    compactRest00 15051 = active8Chunk030Chars00 ++ compactRest00 15479 := by
  calc
    compactRest00 15051 =
        (compactRest00 15051).take 428 ++ (compactRest00 15051).drop 428 :=
      (List.take_append_drop 428 (compactRest00 15051)).symm
    _ = active8Chunk030Chars00 ++ (compactRest00 15051).drop 428 :=
      congrArg (fun part => part ++ (compactRest00 15051).drop 428) compactSpan037_prefix
    _ = active8Chunk030Chars00 ++ compactRest00 15479 :=
      congrArg (fun tail => active8Chunk030Chars00 ++ tail) (compactRest00_drop 15051 428)

theorem compactSpan037_rest_eq (htail : geometryChars00.drop 15479 = compactRest00 15479) :
    geometryChars00.drop 15051 = compactRest00 15051 := by
  have hp : (geometryChars00.drop 15051).take 428 = active8Chunk030Chars00 :=
    geometryChars00_active8_chunk_030_prefix
  exact (list_drop_split_of_prefix geometryChars00 15051 428 active8Chunk030Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk030Chars00 ++ tail) htail).trans compactSpan037_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_037_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_038_before_prefix"
  err.flush

theorem compactSpan038_prefix :
    (compactRest00 15479).take 532 = active8Chunk031Chars00 := by rfl

theorem compactSpan038_split :
    compactRest00 15479 = active8Chunk031Chars00 ++ compactRest00 16011 := by
  calc
    compactRest00 15479 =
        (compactRest00 15479).take 532 ++ (compactRest00 15479).drop 532 :=
      (List.take_append_drop 532 (compactRest00 15479)).symm
    _ = active8Chunk031Chars00 ++ (compactRest00 15479).drop 532 :=
      congrArg (fun part => part ++ (compactRest00 15479).drop 532) compactSpan038_prefix
    _ = active8Chunk031Chars00 ++ compactRest00 16011 :=
      congrArg (fun tail => active8Chunk031Chars00 ++ tail) (compactRest00_drop 15479 532)

theorem compactSpan038_rest_eq (htail : geometryChars00.drop 16011 = compactRest00 16011) :
    geometryChars00.drop 15479 = compactRest00 15479 := by
  have hp : (geometryChars00.drop 15479).take 532 = active8Chunk031Chars00 :=
    geometryChars00_active8_chunk_031_prefix
  exact (list_drop_split_of_prefix geometryChars00 15479 532 active8Chunk031Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk031Chars00 ++ tail) htail).trans compactSpan038_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_038_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_039_before_prefix"
  err.flush

theorem compactSpan039_prefix :
    (compactRest00 16011).take 479 = active8Chunk032Chars00 := by rfl

theorem compactSpan039_split :
    compactRest00 16011 = active8Chunk032Chars00 ++ compactRest00 16490 := by
  calc
    compactRest00 16011 =
        (compactRest00 16011).take 479 ++ (compactRest00 16011).drop 479 :=
      (List.take_append_drop 479 (compactRest00 16011)).symm
    _ = active8Chunk032Chars00 ++ (compactRest00 16011).drop 479 :=
      congrArg (fun part => part ++ (compactRest00 16011).drop 479) compactSpan039_prefix
    _ = active8Chunk032Chars00 ++ compactRest00 16490 :=
      congrArg (fun tail => active8Chunk032Chars00 ++ tail) (compactRest00_drop 16011 479)

theorem compactSpan039_rest_eq (htail : geometryChars00.drop 16490 = compactRest00 16490) :
    geometryChars00.drop 16011 = compactRest00 16011 := by
  have hp : (geometryChars00.drop 16011).take 479 = active8Chunk032Chars00 :=
    geometryChars00_active8_chunk_032_prefix
  exact (list_drop_split_of_prefix geometryChars00 16011 479 active8Chunk032Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk032Chars00 ++ tail) htail).trans compactSpan039_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_039_complete"
  err.flush

theorem group004_rest_eq
    (htail : geometryChars00.drop 16490 = compactRest00 16490) :
    geometryChars00.drop 12542 = compactRest00 12542 := by
  have h039 := compactSpan039_rest_eq htail
  have h038 := compactSpan038_rest_eq h039
  have h037 := compactSpan037_rest_eq h038
  have h036 := compactSpan036_rest_eq h037
  have h035 := compactSpan035_rest_eq h036
  have h034 := compactSpan034_rest_eq h035
  have h033 := compactSpan033_rest_eq h034
  have h032 := compactSpan032_rest_eq h033
  exact h032

#print axioms compactSpan032_prefix
#print axioms compactSpan032_split
#print axioms compactSpan032_rest_eq
#print axioms compactSpan033_prefix
#print axioms compactSpan033_split
#print axioms compactSpan033_rest_eq
#print axioms compactSpan034_prefix
#print axioms compactSpan034_split
#print axioms compactSpan034_rest_eq
#print axioms compactSpan035_prefix
#print axioms compactSpan035_split
#print axioms compactSpan035_rest_eq
#print axioms compactSpan036_prefix
#print axioms compactSpan036_split
#print axioms compactSpan036_rest_eq
#print axioms compactSpan037_prefix
#print axioms compactSpan037_split
#print axioms compactSpan037_rest_eq
#print axioms compactSpan038_prefix
#print axioms compactSpan038_split
#print axioms compactSpan038_rest_eq
#print axioms compactSpan039_prefix
#print axioms compactSpan039_split
#print axioms compactSpan039_rest_eq
#print axioms group004_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
