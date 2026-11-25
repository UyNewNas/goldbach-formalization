import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01000
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01100
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock01200

/-! Exact compact prefix group 6, bytes [20433,24247).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_048_before_prefix"
  err.flush

theorem compactSpan048_prefix :
    (compactRest00 20433).take 426 = active8Chunk041Chars00 := by rfl

theorem compactSpan048_split :
    compactRest00 20433 = active8Chunk041Chars00 ++ compactRest00 20859 := by
  calc
    compactRest00 20433 =
        (compactRest00 20433).take 426 ++ (compactRest00 20433).drop 426 :=
      (List.take_append_drop 426 (compactRest00 20433)).symm
    _ = active8Chunk041Chars00 ++ (compactRest00 20433).drop 426 :=
      congrArg (fun part => part ++ (compactRest00 20433).drop 426) compactSpan048_prefix
    _ = active8Chunk041Chars00 ++ compactRest00 20859 :=
      congrArg (fun tail => active8Chunk041Chars00 ++ tail) (compactRest00_drop 20433 426)

theorem compactSpan048_rest_eq (htail : geometryChars00.drop 20859 = compactRest00 20859) :
    geometryChars00.drop 20433 = compactRest00 20433 := by
  have hp : (geometryChars00.drop 20433).take 426 = active8Chunk041Chars00 :=
    geometryChars00_active8_chunk_041_prefix
  exact (list_drop_split_of_prefix geometryChars00 20433 426 active8Chunk041Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk041Chars00 ++ tail) htail).trans compactSpan048_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_048_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_049_before_prefix"
  err.flush

theorem compactSpan049_prefix :
    (compactRest00 20859).take 457 = active8Chunk042Chars00 := by rfl

theorem compactSpan049_split :
    compactRest00 20859 = active8Chunk042Chars00 ++ compactRest00 21316 := by
  calc
    compactRest00 20859 =
        (compactRest00 20859).take 457 ++ (compactRest00 20859).drop 457 :=
      (List.take_append_drop 457 (compactRest00 20859)).symm
    _ = active8Chunk042Chars00 ++ (compactRest00 20859).drop 457 :=
      congrArg (fun part => part ++ (compactRest00 20859).drop 457) compactSpan049_prefix
    _ = active8Chunk042Chars00 ++ compactRest00 21316 :=
      congrArg (fun tail => active8Chunk042Chars00 ++ tail) (compactRest00_drop 20859 457)

theorem compactSpan049_rest_eq (htail : geometryChars00.drop 21316 = compactRest00 21316) :
    geometryChars00.drop 20859 = compactRest00 20859 := by
  have hp : (geometryChars00.drop 20859).take 457 = active8Chunk042Chars00 :=
    geometryChars00_active8_chunk_042_prefix
  exact (list_drop_split_of_prefix geometryChars00 20859 457 active8Chunk042Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk042Chars00 ++ tail) htail).trans compactSpan049_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_049_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_050_before_prefix"
  err.flush

theorem compactSpan050_prefix :
    (compactRest00 21316).take 481 = active8Chunk043Chars00 := by rfl

theorem compactSpan050_split :
    compactRest00 21316 = active8Chunk043Chars00 ++ compactRest00 21797 := by
  calc
    compactRest00 21316 =
        (compactRest00 21316).take 481 ++ (compactRest00 21316).drop 481 :=
      (List.take_append_drop 481 (compactRest00 21316)).symm
    _ = active8Chunk043Chars00 ++ (compactRest00 21316).drop 481 :=
      congrArg (fun part => part ++ (compactRest00 21316).drop 481) compactSpan050_prefix
    _ = active8Chunk043Chars00 ++ compactRest00 21797 :=
      congrArg (fun tail => active8Chunk043Chars00 ++ tail) (compactRest00_drop 21316 481)

theorem compactSpan050_rest_eq (htail : geometryChars00.drop 21797 = compactRest00 21797) :
    geometryChars00.drop 21316 = compactRest00 21316 := by
  have hp : (geometryChars00.drop 21316).take 481 = active8Chunk043Chars00 :=
    geometryChars00_active8_chunk_043_prefix
  exact (list_drop_split_of_prefix geometryChars00 21316 481 active8Chunk043Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk043Chars00 ++ tail) htail).trans compactSpan050_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_050_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_051_before_prefix"
  err.flush

theorem compactSpan051_prefix :
    (compactRest00 21797).take 428 = active8Chunk044Chars00 := by rfl

theorem compactSpan051_split :
    compactRest00 21797 = active8Chunk044Chars00 ++ compactRest00 22225 := by
  calc
    compactRest00 21797 =
        (compactRest00 21797).take 428 ++ (compactRest00 21797).drop 428 :=
      (List.take_append_drop 428 (compactRest00 21797)).symm
    _ = active8Chunk044Chars00 ++ (compactRest00 21797).drop 428 :=
      congrArg (fun part => part ++ (compactRest00 21797).drop 428) compactSpan051_prefix
    _ = active8Chunk044Chars00 ++ compactRest00 22225 :=
      congrArg (fun tail => active8Chunk044Chars00 ++ tail) (compactRest00_drop 21797 428)

theorem compactSpan051_rest_eq (htail : geometryChars00.drop 22225 = compactRest00 22225) :
    geometryChars00.drop 21797 = compactRest00 21797 := by
  have hp : (geometryChars00.drop 21797).take 428 = active8Chunk044Chars00 :=
    geometryChars00_active8_chunk_044_prefix
  exact (list_drop_split_of_prefix geometryChars00 21797 428 active8Chunk044Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk044Chars00 ++ tail) htail).trans compactSpan051_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_051_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_052_before_prefix"
  err.flush

theorem compactSpan052_prefix :
    (compactRest00 22225).take 532 = active8Chunk045Chars00 := by rfl

theorem compactSpan052_split :
    compactRest00 22225 = active8Chunk045Chars00 ++ compactRest00 22757 := by
  calc
    compactRest00 22225 =
        (compactRest00 22225).take 532 ++ (compactRest00 22225).drop 532 :=
      (List.take_append_drop 532 (compactRest00 22225)).symm
    _ = active8Chunk045Chars00 ++ (compactRest00 22225).drop 532 :=
      congrArg (fun part => part ++ (compactRest00 22225).drop 532) compactSpan052_prefix
    _ = active8Chunk045Chars00 ++ compactRest00 22757 :=
      congrArg (fun tail => active8Chunk045Chars00 ++ tail) (compactRest00_drop 22225 532)

theorem compactSpan052_rest_eq (htail : geometryChars00.drop 22757 = compactRest00 22757) :
    geometryChars00.drop 22225 = compactRest00 22225 := by
  have hp : (geometryChars00.drop 22225).take 532 = active8Chunk045Chars00 :=
    geometryChars00_active8_chunk_045_prefix
  exact (list_drop_split_of_prefix geometryChars00 22225 532 active8Chunk045Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk045Chars00 ++ tail) htail).trans compactSpan052_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_052_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_053_before_prefix"
  err.flush

theorem compactSpan053_prefix :
    (compactRest00 22757).take 479 = active8Chunk046Chars00 := by rfl

theorem compactSpan053_split :
    compactRest00 22757 = active8Chunk046Chars00 ++ compactRest00 23236 := by
  calc
    compactRest00 22757 =
        (compactRest00 22757).take 479 ++ (compactRest00 22757).drop 479 :=
      (List.take_append_drop 479 (compactRest00 22757)).symm
    _ = active8Chunk046Chars00 ++ (compactRest00 22757).drop 479 :=
      congrArg (fun part => part ++ (compactRest00 22757).drop 479) compactSpan053_prefix
    _ = active8Chunk046Chars00 ++ compactRest00 23236 :=
      congrArg (fun tail => active8Chunk046Chars00 ++ tail) (compactRest00_drop 22757 479)

theorem compactSpan053_rest_eq (htail : geometryChars00.drop 23236 = compactRest00 23236) :
    geometryChars00.drop 22757 = compactRest00 22757 := by
  have hp : (geometryChars00.drop 22757).take 479 = active8Chunk046Chars00 :=
    geometryChars00_active8_chunk_046_prefix
  exact (list_drop_split_of_prefix geometryChars00 22757 479 active8Chunk046Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk046Chars00 ++ tail) htail).trans compactSpan053_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_053_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_054_before_prefix"
  err.flush

theorem compactSpan054_prefix :
    (compactRest00 23236).take 531 = active8Chunk047Chars00 := by rfl

theorem compactSpan054_split :
    compactRest00 23236 = active8Chunk047Chars00 ++ compactRest00 23767 := by
  calc
    compactRest00 23236 =
        (compactRest00 23236).take 531 ++ (compactRest00 23236).drop 531 :=
      (List.take_append_drop 531 (compactRest00 23236)).symm
    _ = active8Chunk047Chars00 ++ (compactRest00 23236).drop 531 :=
      congrArg (fun part => part ++ (compactRest00 23236).drop 531) compactSpan054_prefix
    _ = active8Chunk047Chars00 ++ compactRest00 23767 :=
      congrArg (fun tail => active8Chunk047Chars00 ++ tail) (compactRest00_drop 23236 531)

theorem compactSpan054_rest_eq (htail : geometryChars00.drop 23767 = compactRest00 23767) :
    geometryChars00.drop 23236 = compactRest00 23236 := by
  have hp : (geometryChars00.drop 23236).take 531 = active8Chunk047Chars00 :=
    geometryChars00_active8_chunk_047_prefix
  exact (list_drop_split_of_prefix geometryChars00 23236 531 active8Chunk047Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk047Chars00 ++ tail) htail).trans compactSpan054_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_054_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_055_before_prefix"
  err.flush

theorem compactSpan055_prefix :
    (compactRest00 23767).take 480 = active8Chunk048Chars00 := by rfl

theorem compactSpan055_split :
    compactRest00 23767 = active8Chunk048Chars00 ++ compactRest00 24247 := by
  calc
    compactRest00 23767 =
        (compactRest00 23767).take 480 ++ (compactRest00 23767).drop 480 :=
      (List.take_append_drop 480 (compactRest00 23767)).symm
    _ = active8Chunk048Chars00 ++ (compactRest00 23767).drop 480 :=
      congrArg (fun part => part ++ (compactRest00 23767).drop 480) compactSpan055_prefix
    _ = active8Chunk048Chars00 ++ compactRest00 24247 :=
      congrArg (fun tail => active8Chunk048Chars00 ++ tail) (compactRest00_drop 23767 480)

theorem compactSpan055_rest_eq (htail : geometryChars00.drop 24247 = compactRest00 24247) :
    geometryChars00.drop 23767 = compactRest00 23767 := by
  have hp : (geometryChars00.drop 23767).take 480 = active8Chunk048Chars00 :=
    geometryChars00_active8_chunk_048_prefix
  exact (list_drop_split_of_prefix geometryChars00 23767 480 active8Chunk048Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk048Chars00 ++ tail) htail).trans compactSpan055_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_055_complete"
  err.flush

theorem group006_rest_eq
    (htail : geometryChars00.drop 24247 = compactRest00 24247) :
    geometryChars00.drop 20433 = compactRest00 20433 := by
  have h055 := compactSpan055_rest_eq htail
  have h054 := compactSpan054_rest_eq h055
  have h053 := compactSpan053_rest_eq h054
  have h052 := compactSpan052_rest_eq h053
  have h051 := compactSpan051_rest_eq h052
  have h050 := compactSpan050_rest_eq h051
  have h049 := compactSpan049_rest_eq h050
  have h048 := compactSpan048_rest_eq h049
  exact h048

#print axioms compactSpan048_prefix
#print axioms compactSpan048_split
#print axioms compactSpan048_rest_eq
#print axioms compactSpan049_prefix
#print axioms compactSpan049_split
#print axioms compactSpan049_rest_eq
#print axioms compactSpan050_prefix
#print axioms compactSpan050_split
#print axioms compactSpan050_rest_eq
#print axioms compactSpan051_prefix
#print axioms compactSpan051_split
#print axioms compactSpan051_rest_eq
#print axioms compactSpan052_prefix
#print axioms compactSpan052_split
#print axioms compactSpan052_rest_eq
#print axioms compactSpan053_prefix
#print axioms compactSpan053_split
#print axioms compactSpan053_rest_eq
#print axioms compactSpan054_prefix
#print axioms compactSpan054_split
#print axioms compactSpan054_rest_eq
#print axioms compactSpan055_prefix
#print axioms compactSpan055_split
#print axioms compactSpan055_rest_eq
#print axioms group006_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
