import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00000
import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00100
import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00200

/-! Exact compact prefix group 12, bytes [42000,45608).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_096_before_prefix"
  err.flush

theorem compactSpan096_prefix :
    (compactRest00 42000).take 453 = verticesChunk003Chars00 := by rfl

theorem compactSpan096_split :
    compactRest00 42000 = verticesChunk003Chars00 ++ compactRest00 42453 := by
  calc
    compactRest00 42000 =
        (compactRest00 42000).take 453 ++ (compactRest00 42000).drop 453 :=
      (List.take_append_drop 453 (compactRest00 42000)).symm
    _ = verticesChunk003Chars00 ++ (compactRest00 42000).drop 453 :=
      congrArg (fun part => part ++ (compactRest00 42000).drop 453) compactSpan096_prefix
    _ = verticesChunk003Chars00 ++ compactRest00 42453 :=
      congrArg (fun tail => verticesChunk003Chars00 ++ tail) (compactRest00_drop 42000 453)

theorem compactSpan096_rest_eq (htail : geometryChars00.drop 42453 = compactRest00 42453) :
    geometryChars00.drop 42000 = compactRest00 42000 := by
  have hp : (geometryChars00.drop 42000).take 453 = verticesChunk003Chars00 :=
    geometryChars00_vertices_chunk_003_prefix
  exact (list_drop_split_of_prefix geometryChars00 42000 453 verticesChunk003Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk003Chars00 ++ tail) htail).trans compactSpan096_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_096_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_097_before_prefix"
  err.flush

theorem compactSpan097_prefix :
    (compactRest00 42453).take 461 = verticesChunk004Chars00 := by rfl

theorem compactSpan097_split :
    compactRest00 42453 = verticesChunk004Chars00 ++ compactRest00 42914 := by
  calc
    compactRest00 42453 =
        (compactRest00 42453).take 461 ++ (compactRest00 42453).drop 461 :=
      (List.take_append_drop 461 (compactRest00 42453)).symm
    _ = verticesChunk004Chars00 ++ (compactRest00 42453).drop 461 :=
      congrArg (fun part => part ++ (compactRest00 42453).drop 461) compactSpan097_prefix
    _ = verticesChunk004Chars00 ++ compactRest00 42914 :=
      congrArg (fun tail => verticesChunk004Chars00 ++ tail) (compactRest00_drop 42453 461)

theorem compactSpan097_rest_eq (htail : geometryChars00.drop 42914 = compactRest00 42914) :
    geometryChars00.drop 42453 = compactRest00 42453 := by
  have hp : (geometryChars00.drop 42453).take 461 = verticesChunk004Chars00 :=
    geometryChars00_vertices_chunk_004_prefix
  exact (list_drop_split_of_prefix geometryChars00 42453 461 verticesChunk004Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk004Chars00 ++ tail) htail).trans compactSpan097_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_097_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_098_before_prefix"
  err.flush

theorem compactSpan098_prefix :
    (compactRest00 42914).take 457 = verticesChunk005Chars00 := by rfl

theorem compactSpan098_split :
    compactRest00 42914 = verticesChunk005Chars00 ++ compactRest00 43371 := by
  calc
    compactRest00 42914 =
        (compactRest00 42914).take 457 ++ (compactRest00 42914).drop 457 :=
      (List.take_append_drop 457 (compactRest00 42914)).symm
    _ = verticesChunk005Chars00 ++ (compactRest00 42914).drop 457 :=
      congrArg (fun part => part ++ (compactRest00 42914).drop 457) compactSpan098_prefix
    _ = verticesChunk005Chars00 ++ compactRest00 43371 :=
      congrArg (fun tail => verticesChunk005Chars00 ++ tail) (compactRest00_drop 42914 457)

theorem compactSpan098_rest_eq (htail : geometryChars00.drop 43371 = compactRest00 43371) :
    geometryChars00.drop 42914 = compactRest00 42914 := by
  have hp : (geometryChars00.drop 42914).take 457 = verticesChunk005Chars00 :=
    geometryChars00_vertices_chunk_005_prefix
  exact (list_drop_split_of_prefix geometryChars00 42914 457 verticesChunk005Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk005Chars00 ++ tail) htail).trans compactSpan098_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_098_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_099_before_prefix"
  err.flush

theorem compactSpan099_prefix :
    (compactRest00 43371).take 475 = verticesChunk006Chars00 := by rfl

theorem compactSpan099_split :
    compactRest00 43371 = verticesChunk006Chars00 ++ compactRest00 43846 := by
  calc
    compactRest00 43371 =
        (compactRest00 43371).take 475 ++ (compactRest00 43371).drop 475 :=
      (List.take_append_drop 475 (compactRest00 43371)).symm
    _ = verticesChunk006Chars00 ++ (compactRest00 43371).drop 475 :=
      congrArg (fun part => part ++ (compactRest00 43371).drop 475) compactSpan099_prefix
    _ = verticesChunk006Chars00 ++ compactRest00 43846 :=
      congrArg (fun tail => verticesChunk006Chars00 ++ tail) (compactRest00_drop 43371 475)

theorem compactSpan099_rest_eq (htail : geometryChars00.drop 43846 = compactRest00 43846) :
    geometryChars00.drop 43371 = compactRest00 43371 := by
  have hp : (geometryChars00.drop 43371).take 475 = verticesChunk006Chars00 :=
    geometryChars00_vertices_chunk_006_prefix
  exact (list_drop_split_of_prefix geometryChars00 43371 475 verticesChunk006Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk006Chars00 ++ tail) htail).trans compactSpan099_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_099_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_100_before_prefix"
  err.flush

theorem compactSpan100_prefix :
    (compactRest00 43846).take 444 = verticesChunk007Chars00 := by rfl

theorem compactSpan100_split :
    compactRest00 43846 = verticesChunk007Chars00 ++ compactRest00 44290 := by
  calc
    compactRest00 43846 =
        (compactRest00 43846).take 444 ++ (compactRest00 43846).drop 444 :=
      (List.take_append_drop 444 (compactRest00 43846)).symm
    _ = verticesChunk007Chars00 ++ (compactRest00 43846).drop 444 :=
      congrArg (fun part => part ++ (compactRest00 43846).drop 444) compactSpan100_prefix
    _ = verticesChunk007Chars00 ++ compactRest00 44290 :=
      congrArg (fun tail => verticesChunk007Chars00 ++ tail) (compactRest00_drop 43846 444)

theorem compactSpan100_rest_eq (htail : geometryChars00.drop 44290 = compactRest00 44290) :
    geometryChars00.drop 43846 = compactRest00 43846 := by
  have hp : (geometryChars00.drop 43846).take 444 = verticesChunk007Chars00 :=
    geometryChars00_vertices_chunk_007_prefix
  exact (list_drop_split_of_prefix geometryChars00 43846 444 verticesChunk007Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk007Chars00 ++ tail) htail).trans compactSpan100_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_100_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_101_before_prefix"
  err.flush

theorem compactSpan101_prefix :
    (compactRest00 44290).take 439 = verticesChunk008Chars00 := by rfl

theorem compactSpan101_split :
    compactRest00 44290 = verticesChunk008Chars00 ++ compactRest00 44729 := by
  calc
    compactRest00 44290 =
        (compactRest00 44290).take 439 ++ (compactRest00 44290).drop 439 :=
      (List.take_append_drop 439 (compactRest00 44290)).symm
    _ = verticesChunk008Chars00 ++ (compactRest00 44290).drop 439 :=
      congrArg (fun part => part ++ (compactRest00 44290).drop 439) compactSpan101_prefix
    _ = verticesChunk008Chars00 ++ compactRest00 44729 :=
      congrArg (fun tail => verticesChunk008Chars00 ++ tail) (compactRest00_drop 44290 439)

theorem compactSpan101_rest_eq (htail : geometryChars00.drop 44729 = compactRest00 44729) :
    geometryChars00.drop 44290 = compactRest00 44290 := by
  have hp : (geometryChars00.drop 44290).take 439 = verticesChunk008Chars00 :=
    geometryChars00_vertices_chunk_008_prefix
  exact (list_drop_split_of_prefix geometryChars00 44290 439 verticesChunk008Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk008Chars00 ++ tail) htail).trans compactSpan101_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_101_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_102_before_prefix"
  err.flush

theorem compactSpan102_prefix :
    (compactRest00 44729).take 444 = verticesChunk009Chars00 := by rfl

theorem compactSpan102_split :
    compactRest00 44729 = verticesChunk009Chars00 ++ compactRest00 45173 := by
  calc
    compactRest00 44729 =
        (compactRest00 44729).take 444 ++ (compactRest00 44729).drop 444 :=
      (List.take_append_drop 444 (compactRest00 44729)).symm
    _ = verticesChunk009Chars00 ++ (compactRest00 44729).drop 444 :=
      congrArg (fun part => part ++ (compactRest00 44729).drop 444) compactSpan102_prefix
    _ = verticesChunk009Chars00 ++ compactRest00 45173 :=
      congrArg (fun tail => verticesChunk009Chars00 ++ tail) (compactRest00_drop 44729 444)

theorem compactSpan102_rest_eq (htail : geometryChars00.drop 45173 = compactRest00 45173) :
    geometryChars00.drop 44729 = compactRest00 44729 := by
  have hp : (geometryChars00.drop 44729).take 444 = verticesChunk009Chars00 :=
    geometryChars00_vertices_chunk_009_prefix
  exact (list_drop_split_of_prefix geometryChars00 44729 444 verticesChunk009Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk009Chars00 ++ tail) htail).trans compactSpan102_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_102_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_103_before_prefix"
  err.flush

theorem compactSpan103_prefix :
    (compactRest00 45173).take 435 = verticesChunk010Chars00 := by rfl

theorem compactSpan103_split :
    compactRest00 45173 = verticesChunk010Chars00 ++ compactRest00 45608 := by
  calc
    compactRest00 45173 =
        (compactRest00 45173).take 435 ++ (compactRest00 45173).drop 435 :=
      (List.take_append_drop 435 (compactRest00 45173)).symm
    _ = verticesChunk010Chars00 ++ (compactRest00 45173).drop 435 :=
      congrArg (fun part => part ++ (compactRest00 45173).drop 435) compactSpan103_prefix
    _ = verticesChunk010Chars00 ++ compactRest00 45608 :=
      congrArg (fun tail => verticesChunk010Chars00 ++ tail) (compactRest00_drop 45173 435)

theorem compactSpan103_rest_eq (htail : geometryChars00.drop 45608 = compactRest00 45608) :
    geometryChars00.drop 45173 = compactRest00 45173 := by
  have hp : (geometryChars00.drop 45173).take 435 = verticesChunk010Chars00 :=
    geometryChars00_vertices_chunk_010_prefix
  exact (list_drop_split_of_prefix geometryChars00 45173 435 verticesChunk010Chars00 hp).trans
    ((congrArg (fun tail => verticesChunk010Chars00 ++ tail) htail).trans compactSpan103_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_103_complete"
  err.flush

theorem group012_rest_eq
    (htail : geometryChars00.drop 45608 = compactRest00 45608) :
    geometryChars00.drop 42000 = compactRest00 42000 := by
  have h103 := compactSpan103_rest_eq htail
  have h102 := compactSpan102_rest_eq h103
  have h101 := compactSpan101_rest_eq h102
  have h100 := compactSpan100_rest_eq h101
  have h099 := compactSpan099_rest_eq h100
  have h098 := compactSpan098_rest_eq h099
  have h097 := compactSpan097_rest_eq h098
  have h096 := compactSpan096_rest_eq h097
  exact h096

#print axioms compactSpan096_prefix
#print axioms compactSpan096_split
#print axioms compactSpan096_rest_eq
#print axioms compactSpan097_prefix
#print axioms compactSpan097_split
#print axioms compactSpan097_rest_eq
#print axioms compactSpan098_prefix
#print axioms compactSpan098_split
#print axioms compactSpan098_rest_eq
#print axioms compactSpan099_prefix
#print axioms compactSpan099_split
#print axioms compactSpan099_rest_eq
#print axioms compactSpan100_prefix
#print axioms compactSpan100_split
#print axioms compactSpan100_rest_eq
#print axioms compactSpan101_prefix
#print axioms compactSpan101_split
#print axioms compactSpan101_rest_eq
#print axioms compactSpan102_prefix
#print axioms compactSpan102_split
#print axioms compactSpan102_rest_eq
#print axioms compactSpan103_prefix
#print axioms compactSpan103_split
#print axioms compactSpan103_rest_eq
#print axioms group012_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
