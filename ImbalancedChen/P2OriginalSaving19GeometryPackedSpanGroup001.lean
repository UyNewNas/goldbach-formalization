import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00000
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00100
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00200

/-! Exact compact prefix group 1, bytes [856,4686).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_008_before_prefix"
  err.flush

theorem compactSpan008_prefix :
    (compactRest00 856).take 448 = active8Chunk001Chars00 := by rfl

theorem compactSpan008_split :
    compactRest00 856 = active8Chunk001Chars00 ++ compactRest00 1304 := by
  calc
    compactRest00 856 =
        (compactRest00 856).take 448 ++ (compactRest00 856).drop 448 :=
      (List.take_append_drop 448 (compactRest00 856)).symm
    _ = active8Chunk001Chars00 ++ (compactRest00 856).drop 448 :=
      congrArg (fun part => part ++ (compactRest00 856).drop 448) compactSpan008_prefix
    _ = active8Chunk001Chars00 ++ compactRest00 1304 :=
      congrArg (fun tail => active8Chunk001Chars00 ++ tail) (compactRest00_drop 856 448)

theorem compactSpan008_rest_eq (htail : geometryChars00.drop 1304 = compactRest00 1304) :
    geometryChars00.drop 856 = compactRest00 856 := by
  have hp : (geometryChars00.drop 856).take 448 = active8Chunk001Chars00 :=
    geometryChars00_active8_chunk_001_prefix
  exact (list_drop_split_of_prefix geometryChars00 856 448 active8Chunk001Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk001Chars00 ++ tail) htail).trans compactSpan008_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_008_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_009_before_prefix"
  err.flush

theorem compactSpan009_prefix :
    (compactRest00 1304).take 455 = active8Chunk002Chars00 := by rfl

theorem compactSpan009_split :
    compactRest00 1304 = active8Chunk002Chars00 ++ compactRest00 1759 := by
  calc
    compactRest00 1304 =
        (compactRest00 1304).take 455 ++ (compactRest00 1304).drop 455 :=
      (List.take_append_drop 455 (compactRest00 1304)).symm
    _ = active8Chunk002Chars00 ++ (compactRest00 1304).drop 455 :=
      congrArg (fun part => part ++ (compactRest00 1304).drop 455) compactSpan009_prefix
    _ = active8Chunk002Chars00 ++ compactRest00 1759 :=
      congrArg (fun tail => active8Chunk002Chars00 ++ tail) (compactRest00_drop 1304 455)

theorem compactSpan009_rest_eq (htail : geometryChars00.drop 1759 = compactRest00 1759) :
    geometryChars00.drop 1304 = compactRest00 1304 := by
  have hp : (geometryChars00.drop 1304).take 455 = active8Chunk002Chars00 :=
    geometryChars00_active8_chunk_002_prefix
  exact (list_drop_split_of_prefix geometryChars00 1304 455 active8Chunk002Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk002Chars00 ++ tail) htail).trans compactSpan009_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_009_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_010_before_prefix"
  err.flush

theorem compactSpan010_prefix :
    (compactRest00 1759).take 455 = active8Chunk003Chars00 := by rfl

theorem compactSpan010_split :
    compactRest00 1759 = active8Chunk003Chars00 ++ compactRest00 2214 := by
  calc
    compactRest00 1759 =
        (compactRest00 1759).take 455 ++ (compactRest00 1759).drop 455 :=
      (List.take_append_drop 455 (compactRest00 1759)).symm
    _ = active8Chunk003Chars00 ++ (compactRest00 1759).drop 455 :=
      congrArg (fun part => part ++ (compactRest00 1759).drop 455) compactSpan010_prefix
    _ = active8Chunk003Chars00 ++ compactRest00 2214 :=
      congrArg (fun tail => active8Chunk003Chars00 ++ tail) (compactRest00_drop 1759 455)

theorem compactSpan010_rest_eq (htail : geometryChars00.drop 2214 = compactRest00 2214) :
    geometryChars00.drop 1759 = compactRest00 1759 := by
  have hp : (geometryChars00.drop 1759).take 455 = active8Chunk003Chars00 :=
    geometryChars00_active8_chunk_003_prefix
  exact (list_drop_split_of_prefix geometryChars00 1759 455 active8Chunk003Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk003Chars00 ++ tail) htail).trans compactSpan010_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_010_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_011_before_prefix"
  err.flush

theorem compactSpan011_prefix :
    (compactRest00 2214).take 448 = active8Chunk004Chars00 := by rfl

theorem compactSpan011_split :
    compactRest00 2214 = active8Chunk004Chars00 ++ compactRest00 2662 := by
  calc
    compactRest00 2214 =
        (compactRest00 2214).take 448 ++ (compactRest00 2214).drop 448 :=
      (List.take_append_drop 448 (compactRest00 2214)).symm
    _ = active8Chunk004Chars00 ++ (compactRest00 2214).drop 448 :=
      congrArg (fun part => part ++ (compactRest00 2214).drop 448) compactSpan011_prefix
    _ = active8Chunk004Chars00 ++ compactRest00 2662 :=
      congrArg (fun tail => active8Chunk004Chars00 ++ tail) (compactRest00_drop 2214 448)

theorem compactSpan011_rest_eq (htail : geometryChars00.drop 2662 = compactRest00 2662) :
    geometryChars00.drop 2214 = compactRest00 2214 := by
  have hp : (geometryChars00.drop 2214).take 448 = active8Chunk004Chars00 :=
    geometryChars00_active8_chunk_004_prefix
  exact (list_drop_split_of_prefix geometryChars00 2214 448 active8Chunk004Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk004Chars00 ++ tail) htail).trans compactSpan011_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_011_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_012_before_prefix"
  err.flush

theorem compactSpan012_prefix :
    (compactRest00 2662).take 455 = active8Chunk005Chars00 := by rfl

theorem compactSpan012_split :
    compactRest00 2662 = active8Chunk005Chars00 ++ compactRest00 3117 := by
  calc
    compactRest00 2662 =
        (compactRest00 2662).take 455 ++ (compactRest00 2662).drop 455 :=
      (List.take_append_drop 455 (compactRest00 2662)).symm
    _ = active8Chunk005Chars00 ++ (compactRest00 2662).drop 455 :=
      congrArg (fun part => part ++ (compactRest00 2662).drop 455) compactSpan012_prefix
    _ = active8Chunk005Chars00 ++ compactRest00 3117 :=
      congrArg (fun tail => active8Chunk005Chars00 ++ tail) (compactRest00_drop 2662 455)

theorem compactSpan012_rest_eq (htail : geometryChars00.drop 3117 = compactRest00 3117) :
    geometryChars00.drop 2662 = compactRest00 2662 := by
  have hp : (geometryChars00.drop 2662).take 455 = active8Chunk005Chars00 :=
    geometryChars00_active8_chunk_005_prefix
  exact (list_drop_split_of_prefix geometryChars00 2662 455 active8Chunk005Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk005Chars00 ++ tail) htail).trans compactSpan012_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_012_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_013_before_prefix"
  err.flush

theorem compactSpan013_prefix :
    (compactRest00 3117).take 524 = active8Chunk006Chars00 := by rfl

theorem compactSpan013_split :
    compactRest00 3117 = active8Chunk006Chars00 ++ compactRest00 3641 := by
  calc
    compactRest00 3117 =
        (compactRest00 3117).take 524 ++ (compactRest00 3117).drop 524 :=
      (List.take_append_drop 524 (compactRest00 3117)).symm
    _ = active8Chunk006Chars00 ++ (compactRest00 3117).drop 524 :=
      congrArg (fun part => part ++ (compactRest00 3117).drop 524) compactSpan013_prefix
    _ = active8Chunk006Chars00 ++ compactRest00 3641 :=
      congrArg (fun tail => active8Chunk006Chars00 ++ tail) (compactRest00_drop 3117 524)

theorem compactSpan013_rest_eq (htail : geometryChars00.drop 3641 = compactRest00 3641) :
    geometryChars00.drop 3117 = compactRest00 3117 := by
  have hp : (geometryChars00.drop 3117).take 524 = active8Chunk006Chars00 :=
    geometryChars00_active8_chunk_006_prefix
  exact (list_drop_split_of_prefix geometryChars00 3117 524 active8Chunk006Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk006Chars00 ++ tail) htail).trans compactSpan013_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_013_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_014_before_prefix"
  err.flush

theorem compactSpan014_prefix :
    (compactRest00 3641).take 521 = active8Chunk007Chars00 := by rfl

theorem compactSpan014_split :
    compactRest00 3641 = active8Chunk007Chars00 ++ compactRest00 4162 := by
  calc
    compactRest00 3641 =
        (compactRest00 3641).take 521 ++ (compactRest00 3641).drop 521 :=
      (List.take_append_drop 521 (compactRest00 3641)).symm
    _ = active8Chunk007Chars00 ++ (compactRest00 3641).drop 521 :=
      congrArg (fun part => part ++ (compactRest00 3641).drop 521) compactSpan014_prefix
    _ = active8Chunk007Chars00 ++ compactRest00 4162 :=
      congrArg (fun tail => active8Chunk007Chars00 ++ tail) (compactRest00_drop 3641 521)

theorem compactSpan014_rest_eq (htail : geometryChars00.drop 4162 = compactRest00 4162) :
    geometryChars00.drop 3641 = compactRest00 3641 := by
  have hp : (geometryChars00.drop 3641).take 521 = active8Chunk007Chars00 :=
    geometryChars00_active8_chunk_007_prefix
  exact (list_drop_split_of_prefix geometryChars00 3641 521 active8Chunk007Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk007Chars00 ++ tail) htail).trans compactSpan014_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_014_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_015_before_prefix"
  err.flush

theorem compactSpan015_prefix :
    (compactRest00 4162).take 524 = active8Chunk008Chars00 := by rfl

theorem compactSpan015_split :
    compactRest00 4162 = active8Chunk008Chars00 ++ compactRest00 4686 := by
  calc
    compactRest00 4162 =
        (compactRest00 4162).take 524 ++ (compactRest00 4162).drop 524 :=
      (List.take_append_drop 524 (compactRest00 4162)).symm
    _ = active8Chunk008Chars00 ++ (compactRest00 4162).drop 524 :=
      congrArg (fun part => part ++ (compactRest00 4162).drop 524) compactSpan015_prefix
    _ = active8Chunk008Chars00 ++ compactRest00 4686 :=
      congrArg (fun tail => active8Chunk008Chars00 ++ tail) (compactRest00_drop 4162 524)

theorem compactSpan015_rest_eq (htail : geometryChars00.drop 4686 = compactRest00 4686) :
    geometryChars00.drop 4162 = compactRest00 4162 := by
  have hp : (geometryChars00.drop 4162).take 524 = active8Chunk008Chars00 :=
    geometryChars00_active8_chunk_008_prefix
  exact (list_drop_split_of_prefix geometryChars00 4162 524 active8Chunk008Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk008Chars00 ++ tail) htail).trans compactSpan015_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_015_complete"
  err.flush

theorem group001_rest_eq
    (htail : geometryChars00.drop 4686 = compactRest00 4686) :
    geometryChars00.drop 856 = compactRest00 856 := by
  have h015 := compactSpan015_rest_eq htail
  have h014 := compactSpan014_rest_eq h015
  have h013 := compactSpan013_rest_eq h014
  have h012 := compactSpan012_rest_eq h013
  have h011 := compactSpan011_rest_eq h012
  have h010 := compactSpan010_rest_eq h011
  have h009 := compactSpan009_rest_eq h010
  have h008 := compactSpan008_rest_eq h009
  exact h008

#print axioms compactSpan008_prefix
#print axioms compactSpan008_split
#print axioms compactSpan008_rest_eq
#print axioms compactSpan009_prefix
#print axioms compactSpan009_split
#print axioms compactSpan009_rest_eq
#print axioms compactSpan010_prefix
#print axioms compactSpan010_split
#print axioms compactSpan010_rest_eq
#print axioms compactSpan011_prefix
#print axioms compactSpan011_split
#print axioms compactSpan011_rest_eq
#print axioms compactSpan012_prefix
#print axioms compactSpan012_split
#print axioms compactSpan012_rest_eq
#print axioms compactSpan013_prefix
#print axioms compactSpan013_split
#print axioms compactSpan013_rest_eq
#print axioms compactSpan014_prefix
#print axioms compactSpan014_split
#print axioms compactSpan014_rest_eq
#print axioms compactSpan015_prefix
#print axioms compactSpan015_split
#print axioms compactSpan015_rest_eq
#print axioms group001_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
