import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00200
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00300
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00400

/-! Exact compact prefix group 2, bytes [4686,8807).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_016_before_prefix"
  err.flush

theorem compactSpan016_prefix :
    (compactRest00 4686).take 518 = active8Chunk009Chars00 := by rfl

theorem compactSpan016_split :
    compactRest00 4686 = active8Chunk009Chars00 ++ compactRest00 5204 := by
  calc
    compactRest00 4686 =
        (compactRest00 4686).take 518 ++ (compactRest00 4686).drop 518 :=
      (List.take_append_drop 518 (compactRest00 4686)).symm
    _ = active8Chunk009Chars00 ++ (compactRest00 4686).drop 518 :=
      congrArg (fun part => part ++ (compactRest00 4686).drop 518) compactSpan016_prefix
    _ = active8Chunk009Chars00 ++ compactRest00 5204 :=
      congrArg (fun tail => active8Chunk009Chars00 ++ tail) (compactRest00_drop 4686 518)

theorem compactSpan016_rest_eq (htail : geometryChars00.drop 5204 = compactRest00 5204) :
    geometryChars00.drop 4686 = compactRest00 4686 := by
  have hp : (geometryChars00.drop 4686).take 518 = active8Chunk009Chars00 :=
    geometryChars00_active8_chunk_009_prefix
  exact (list_drop_split_of_prefix geometryChars00 4686 518 active8Chunk009Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk009Chars00 ++ tail) htail).trans compactSpan016_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_016_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_017_before_prefix"
  err.flush

theorem compactSpan017_prefix :
    (compactRest00 5204).take 456 = active8Chunk010Chars00 := by rfl

theorem compactSpan017_split :
    compactRest00 5204 = active8Chunk010Chars00 ++ compactRest00 5660 := by
  calc
    compactRest00 5204 =
        (compactRest00 5204).take 456 ++ (compactRest00 5204).drop 456 :=
      (List.take_append_drop 456 (compactRest00 5204)).symm
    _ = active8Chunk010Chars00 ++ (compactRest00 5204).drop 456 :=
      congrArg (fun part => part ++ (compactRest00 5204).drop 456) compactSpan017_prefix
    _ = active8Chunk010Chars00 ++ compactRest00 5660 :=
      congrArg (fun tail => active8Chunk010Chars00 ++ tail) (compactRest00_drop 5204 456)

theorem compactSpan017_rest_eq (htail : geometryChars00.drop 5660 = compactRest00 5660) :
    geometryChars00.drop 5204 = compactRest00 5204 := by
  have hp : (geometryChars00.drop 5204).take 456 = active8Chunk010Chars00 :=
    geometryChars00_active8_chunk_010_prefix
  exact (list_drop_split_of_prefix geometryChars00 5204 456 active8Chunk010Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk010Chars00 ++ tail) htail).trans compactSpan017_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_017_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_018_before_prefix"
  err.flush

theorem compactSpan018_prefix :
    (compactRest00 5660).take 524 = active8Chunk011Chars00 := by rfl

theorem compactSpan018_split :
    compactRest00 5660 = active8Chunk011Chars00 ++ compactRest00 6184 := by
  calc
    compactRest00 5660 =
        (compactRest00 5660).take 524 ++ (compactRest00 5660).drop 524 :=
      (List.take_append_drop 524 (compactRest00 5660)).symm
    _ = active8Chunk011Chars00 ++ (compactRest00 5660).drop 524 :=
      congrArg (fun part => part ++ (compactRest00 5660).drop 524) compactSpan018_prefix
    _ = active8Chunk011Chars00 ++ compactRest00 6184 :=
      congrArg (fun tail => active8Chunk011Chars00 ++ tail) (compactRest00_drop 5660 524)

theorem compactSpan018_rest_eq (htail : geometryChars00.drop 6184 = compactRest00 6184) :
    geometryChars00.drop 5660 = compactRest00 5660 := by
  have hp : (geometryChars00.drop 5660).take 524 = active8Chunk011Chars00 :=
    geometryChars00_active8_chunk_011_prefix
  exact (list_drop_split_of_prefix geometryChars00 5660 524 active8Chunk011Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk011Chars00 ++ tail) htail).trans compactSpan018_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_018_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_019_before_prefix"
  err.flush

theorem compactSpan019_prefix :
    (compactRest00 6184).take 523 = active8Chunk012Chars00 := by rfl

theorem compactSpan019_split :
    compactRest00 6184 = active8Chunk012Chars00 ++ compactRest00 6707 := by
  calc
    compactRest00 6184 =
        (compactRest00 6184).take 523 ++ (compactRest00 6184).drop 523 :=
      (List.take_append_drop 523 (compactRest00 6184)).symm
    _ = active8Chunk012Chars00 ++ (compactRest00 6184).drop 523 :=
      congrArg (fun part => part ++ (compactRest00 6184).drop 523) compactSpan019_prefix
    _ = active8Chunk012Chars00 ++ compactRest00 6707 :=
      congrArg (fun tail => active8Chunk012Chars00 ++ tail) (compactRest00_drop 6184 523)

theorem compactSpan019_rest_eq (htail : geometryChars00.drop 6707 = compactRest00 6707) :
    geometryChars00.drop 6184 = compactRest00 6184 := by
  have hp : (geometryChars00.drop 6184).take 523 = active8Chunk012Chars00 :=
    geometryChars00_active8_chunk_012_prefix
  exact (list_drop_split_of_prefix geometryChars00 6184 523 active8Chunk012Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk012Chars00 ++ tail) htail).trans compactSpan019_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_019_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_020_before_prefix"
  err.flush

theorem compactSpan020_prefix :
    (compactRest00 6707).take 524 = active8Chunk013Chars00 := by rfl

theorem compactSpan020_split :
    compactRest00 6707 = active8Chunk013Chars00 ++ compactRest00 7231 := by
  calc
    compactRest00 6707 =
        (compactRest00 6707).take 524 ++ (compactRest00 6707).drop 524 :=
      (List.take_append_drop 524 (compactRest00 6707)).symm
    _ = active8Chunk013Chars00 ++ (compactRest00 6707).drop 524 :=
      congrArg (fun part => part ++ (compactRest00 6707).drop 524) compactSpan020_prefix
    _ = active8Chunk013Chars00 ++ compactRest00 7231 :=
      congrArg (fun tail => active8Chunk013Chars00 ++ tail) (compactRest00_drop 6707 524)

theorem compactSpan020_rest_eq (htail : geometryChars00.drop 7231 = compactRest00 7231) :
    geometryChars00.drop 6707 = compactRest00 6707 := by
  have hp : (geometryChars00.drop 6707).take 524 = active8Chunk013Chars00 :=
    geometryChars00_active8_chunk_013_prefix
  exact (list_drop_split_of_prefix geometryChars00 6707 524 active8Chunk013Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk013Chars00 ++ tail) htail).trans compactSpan020_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_020_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_021_before_prefix"
  err.flush

theorem compactSpan021_prefix :
    (compactRest00 7231).take 518 = active8Chunk014Chars00 := by rfl

theorem compactSpan021_split :
    compactRest00 7231 = active8Chunk014Chars00 ++ compactRest00 7749 := by
  calc
    compactRest00 7231 =
        (compactRest00 7231).take 518 ++ (compactRest00 7231).drop 518 :=
      (List.take_append_drop 518 (compactRest00 7231)).symm
    _ = active8Chunk014Chars00 ++ (compactRest00 7231).drop 518 :=
      congrArg (fun part => part ++ (compactRest00 7231).drop 518) compactSpan021_prefix
    _ = active8Chunk014Chars00 ++ compactRest00 7749 :=
      congrArg (fun tail => active8Chunk014Chars00 ++ tail) (compactRest00_drop 7231 518)

theorem compactSpan021_rest_eq (htail : geometryChars00.drop 7749 = compactRest00 7749) :
    geometryChars00.drop 7231 = compactRest00 7231 := by
  have hp : (geometryChars00.drop 7231).take 518 = active8Chunk014Chars00 :=
    geometryChars00_active8_chunk_014_prefix
  exact (list_drop_split_of_prefix geometryChars00 7231 518 active8Chunk014Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk014Chars00 ++ tail) htail).trans compactSpan021_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_021_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_022_before_prefix"
  err.flush

theorem compactSpan022_prefix :
    (compactRest00 7749).take 530 = active8Chunk015Chars00 := by rfl

theorem compactSpan022_split :
    compactRest00 7749 = active8Chunk015Chars00 ++ compactRest00 8279 := by
  calc
    compactRest00 7749 =
        (compactRest00 7749).take 530 ++ (compactRest00 7749).drop 530 :=
      (List.take_append_drop 530 (compactRest00 7749)).symm
    _ = active8Chunk015Chars00 ++ (compactRest00 7749).drop 530 :=
      congrArg (fun part => part ++ (compactRest00 7749).drop 530) compactSpan022_prefix
    _ = active8Chunk015Chars00 ++ compactRest00 8279 :=
      congrArg (fun tail => active8Chunk015Chars00 ++ tail) (compactRest00_drop 7749 530)

theorem compactSpan022_rest_eq (htail : geometryChars00.drop 8279 = compactRest00 8279) :
    geometryChars00.drop 7749 = compactRest00 7749 := by
  have hp : (geometryChars00.drop 7749).take 530 = active8Chunk015Chars00 :=
    geometryChars00_active8_chunk_015_prefix
  exact (list_drop_split_of_prefix geometryChars00 7749 530 active8Chunk015Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk015Chars00 ++ tail) htail).trans compactSpan022_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_022_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_023_before_prefix"
  err.flush

theorem compactSpan023_prefix :
    (compactRest00 8279).take 528 = active8Chunk016Chars00 := by rfl

theorem compactSpan023_split :
    compactRest00 8279 = active8Chunk016Chars00 ++ compactRest00 8807 := by
  calc
    compactRest00 8279 =
        (compactRest00 8279).take 528 ++ (compactRest00 8279).drop 528 :=
      (List.take_append_drop 528 (compactRest00 8279)).symm
    _ = active8Chunk016Chars00 ++ (compactRest00 8279).drop 528 :=
      congrArg (fun part => part ++ (compactRest00 8279).drop 528) compactSpan023_prefix
    _ = active8Chunk016Chars00 ++ compactRest00 8807 :=
      congrArg (fun tail => active8Chunk016Chars00 ++ tail) (compactRest00_drop 8279 528)

theorem compactSpan023_rest_eq (htail : geometryChars00.drop 8807 = compactRest00 8807) :
    geometryChars00.drop 8279 = compactRest00 8279 := by
  have hp : (geometryChars00.drop 8279).take 528 = active8Chunk016Chars00 :=
    geometryChars00_active8_chunk_016_prefix
  exact (list_drop_split_of_prefix geometryChars00 8279 528 active8Chunk016Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk016Chars00 ++ tail) htail).trans compactSpan023_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_023_complete"
  err.flush

theorem group002_rest_eq
    (htail : geometryChars00.drop 8807 = compactRest00 8807) :
    geometryChars00.drop 4686 = compactRest00 4686 := by
  have h023 := compactSpan023_rest_eq htail
  have h022 := compactSpan022_rest_eq h023
  have h021 := compactSpan021_rest_eq h022
  have h020 := compactSpan020_rest_eq h021
  have h019 := compactSpan019_rest_eq h020
  have h018 := compactSpan018_rest_eq h019
  have h017 := compactSpan017_rest_eq h018
  have h016 := compactSpan016_rest_eq h017
  exact h016

#print axioms compactSpan016_prefix
#print axioms compactSpan016_split
#print axioms compactSpan016_rest_eq
#print axioms compactSpan017_prefix
#print axioms compactSpan017_split
#print axioms compactSpan017_rest_eq
#print axioms compactSpan018_prefix
#print axioms compactSpan018_split
#print axioms compactSpan018_rest_eq
#print axioms compactSpan019_prefix
#print axioms compactSpan019_split
#print axioms compactSpan019_rest_eq
#print axioms compactSpan020_prefix
#print axioms compactSpan020_split
#print axioms compactSpan020_rest_eq
#print axioms compactSpan021_prefix
#print axioms compactSpan021_split
#print axioms compactSpan021_rest_eq
#print axioms compactSpan022_prefix
#print axioms compactSpan022_split
#print axioms compactSpan022_rest_eq
#print axioms compactSpan023_prefix
#print axioms compactSpan023_split
#print axioms compactSpan023_rest_eq
#print axioms group002_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
