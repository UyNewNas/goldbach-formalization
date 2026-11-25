import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19DimensionPrefix00
import ImbalancedChen.P2OriginalSaving19FirstThreeFields00
import ImbalancedChen.P2OriginalSaving19PositiveBalanceSegments00
import ImbalancedChen.P2OriginalSaving19NormalRankPrefix00
import ImbalancedChen.P2OriginalSaving19Active8Field00
import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock00000

/-! Exact compact prefix group 0, bytes [0,856).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_000_before_prefix"
  err.flush

theorem compactSpan000_prefix :
    (compactRest00 0).take 20 = dimensionPrefixChars00 := by rfl

theorem compactSpan000_split :
    compactRest00 0 = dimensionPrefixChars00 ++ compactRest00 20 := by
  calc
    compactRest00 0 =
        (compactRest00 0).take 20 ++ (compactRest00 0).drop 20 :=
      (List.take_append_drop 20 (compactRest00 0)).symm
    _ = dimensionPrefixChars00 ++ (compactRest00 0).drop 20 :=
      congrArg (fun part => part ++ (compactRest00 0).drop 20) compactSpan000_prefix
    _ = dimensionPrefixChars00 ++ compactRest00 20 :=
      congrArg (fun tail => dimensionPrefixChars00 ++ tail) (compactRest00_drop 0 20)

theorem compactSpan000_rest_eq (htail : geometryChars00.drop 20 = compactRest00 20) :
    geometryChars00.drop 0 = compactRest00 0 := by
  have hp : (geometryChars00.drop 0).take 20 = dimensionPrefixChars00 :=
    by simpa only [List.drop_zero] using geometryChars00_dimension_prefix
  exact (list_drop_split_of_prefix geometryChars00 0 20 dimensionPrefixChars00 hp).trans
    ((congrArg (fun tail => dimensionPrefixChars00 ++ tail) htail).trans compactSpan000_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_000_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_001_before_prefix"
  err.flush

theorem compactSpan001_prefix :
    (compactRest00 20).take 27 = physicalPrefixChars00 := by rfl

theorem compactSpan001_split :
    compactRest00 20 = physicalPrefixChars00 ++ compactRest00 47 := by
  calc
    compactRest00 20 =
        (compactRest00 20).take 27 ++ (compactRest00 20).drop 27 :=
      (List.take_append_drop 27 (compactRest00 20)).symm
    _ = physicalPrefixChars00 ++ (compactRest00 20).drop 27 :=
      congrArg (fun part => part ++ (compactRest00 20).drop 27) compactSpan001_prefix
    _ = physicalPrefixChars00 ++ compactRest00 47 :=
      congrArg (fun tail => physicalPrefixChars00 ++ tail) (compactRest00_drop 20 27)

theorem compactSpan001_rest_eq (htail : geometryChars00.drop 47 = compactRest00 47) :
    geometryChars00.drop 20 = compactRest00 20 := by
  have hp : (geometryChars00.drop 20).take 27 = physicalPrefixChars00 :=
    geometryChars00_physical_prefix
  exact (list_drop_split_of_prefix geometryChars00 20 27 physicalPrefixChars00 hp).trans
    ((congrArg (fun tail => physicalPrefixChars00 ++ tail) htail).trans compactSpan001_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_001_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_002_before_prefix"
  err.flush

theorem compactSpan002_prefix :
    (compactRest00 47).take 132 = facetIndicesPrefixChars00 := by rfl

theorem compactSpan002_split :
    compactRest00 47 = facetIndicesPrefixChars00 ++ compactRest00 179 := by
  calc
    compactRest00 47 =
        (compactRest00 47).take 132 ++ (compactRest00 47).drop 132 :=
      (List.take_append_drop 132 (compactRest00 47)).symm
    _ = facetIndicesPrefixChars00 ++ (compactRest00 47).drop 132 :=
      congrArg (fun part => part ++ (compactRest00 47).drop 132) compactSpan002_prefix
    _ = facetIndicesPrefixChars00 ++ compactRest00 179 :=
      congrArg (fun tail => facetIndicesPrefixChars00 ++ tail) (compactRest00_drop 47 132)

theorem compactSpan002_rest_eq (htail : geometryChars00.drop 179 = compactRest00 179) :
    geometryChars00.drop 47 = compactRest00 47 := by
  have hp : (geometryChars00.drop 47).take 132 = facetIndicesPrefixChars00 :=
    geometryChars00_facet_indices_prefix
  exact (list_drop_split_of_prefix geometryChars00 47 132 facetIndicesPrefixChars00 hp).trans
    ((congrArg (fun tail => facetIndicesPrefixChars00 ++ tail) htail).trans compactSpan002_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_002_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_003_before_prefix"
  err.flush

theorem compactSpan003_prefix :
    (compactRest00 179).take 180 = positiveBalancePrefixChars00 := by rfl

theorem compactSpan003_split :
    compactRest00 179 = positiveBalancePrefixChars00 ++ compactRest00 359 := by
  calc
    compactRest00 179 =
        (compactRest00 179).take 180 ++ (compactRest00 179).drop 180 :=
      (List.take_append_drop 180 (compactRest00 179)).symm
    _ = positiveBalancePrefixChars00 ++ (compactRest00 179).drop 180 :=
      congrArg (fun part => part ++ (compactRest00 179).drop 180) compactSpan003_prefix
    _ = positiveBalancePrefixChars00 ++ compactRest00 359 :=
      congrArg (fun tail => positiveBalancePrefixChars00 ++ tail) (compactRest00_drop 179 180)

theorem compactSpan003_rest_eq (htail : geometryChars00.drop 359 = compactRest00 359) :
    geometryChars00.drop 179 = compactRest00 179 := by
  have hp : (geometryChars00.drop 179).take 180 = positiveBalancePrefixChars00 :=
    geometryChars00_positive_balance_prefix
  exact (list_drop_split_of_prefix geometryChars00 179 180 positiveBalancePrefixChars00 hp).trans
    ((congrArg (fun tail => positiveBalancePrefixChars00 ++ tail) htail).trans compactSpan003_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_003_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_004_before_prefix"
  err.flush

theorem compactSpan004_prefix :
    (compactRest00 359).take 21 = normalRankPrefixChars00 := by rfl

theorem compactSpan004_split :
    compactRest00 359 = normalRankPrefixChars00 ++ compactRest00 380 := by
  calc
    compactRest00 359 =
        (compactRest00 359).take 21 ++ (compactRest00 359).drop 21 :=
      (List.take_append_drop 21 (compactRest00 359)).symm
    _ = normalRankPrefixChars00 ++ (compactRest00 359).drop 21 :=
      congrArg (fun part => part ++ (compactRest00 359).drop 21) compactSpan004_prefix
    _ = normalRankPrefixChars00 ++ compactRest00 380 :=
      congrArg (fun tail => normalRankPrefixChars00 ++ tail) (compactRest00_drop 359 21)

theorem compactSpan004_rest_eq (htail : geometryChars00.drop 380 = compactRest00 380) :
    geometryChars00.drop 359 = compactRest00 359 := by
  have hp : (geometryChars00.drop 359).take 21 = normalRankPrefixChars00 :=
    geometryChars00_normal_rank_prefix
  exact (list_drop_split_of_prefix geometryChars00 359 21 normalRankPrefixChars00 hp).trans
    ((congrArg (fun tail => normalRankPrefixChars00 ++ tail) htail).trans compactSpan004_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_004_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_005_before_prefix"
  err.flush

theorem compactSpan005_prefix :
    (compactRest00 380).take 27 = active8HeaderChars00 := by rfl

theorem compactSpan005_split :
    compactRest00 380 = active8HeaderChars00 ++ compactRest00 407 := by
  calc
    compactRest00 380 =
        (compactRest00 380).take 27 ++ (compactRest00 380).drop 27 :=
      (List.take_append_drop 27 (compactRest00 380)).symm
    _ = active8HeaderChars00 ++ (compactRest00 380).drop 27 :=
      congrArg (fun part => part ++ (compactRest00 380).drop 27) compactSpan005_prefix
    _ = active8HeaderChars00 ++ compactRest00 407 :=
      congrArg (fun tail => active8HeaderChars00 ++ tail) (compactRest00_drop 380 27)

theorem compactSpan005_rest_eq (htail : geometryChars00.drop 407 = compactRest00 407) :
    geometryChars00.drop 380 = compactRest00 380 := by
  have hp : (geometryChars00.drop 380).take 27 = active8HeaderChars00 :=
    geometryChars00_active8_header_prefix
  exact (list_drop_split_of_prefix geometryChars00 380 27 active8HeaderChars00 hp).trans
    ((congrArg (fun tail => active8HeaderChars00 ++ tail) htail).trans compactSpan005_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_005_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_006_before_prefix"
  err.flush

theorem compactSpan006_prefix :
    (compactRest00 407).take 1 = active8OpenChars00 := by rfl

theorem compactSpan006_split :
    compactRest00 407 = active8OpenChars00 ++ compactRest00 408 := by
  calc
    compactRest00 407 =
        (compactRest00 407).take 1 ++ (compactRest00 407).drop 1 :=
      (List.take_append_drop 1 (compactRest00 407)).symm
    _ = active8OpenChars00 ++ (compactRest00 407).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 407).drop 1) compactSpan006_prefix
    _ = active8OpenChars00 ++ compactRest00 408 :=
      congrArg (fun tail => active8OpenChars00 ++ tail) (compactRest00_drop 407 1)

theorem compactSpan006_rest_eq (htail : geometryChars00.drop 408 = compactRest00 408) :
    geometryChars00.drop 407 = compactRest00 407 := by
  have hp : (geometryChars00.drop 407).take 1 = active8OpenChars00 :=
    geometryChars00_active8_open_prefix
  exact (list_drop_split_of_prefix geometryChars00 407 1 active8OpenChars00 hp).trans
    ((congrArg (fun tail => active8OpenChars00 ++ tail) htail).trans compactSpan006_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_006_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_007_before_prefix"
  err.flush

theorem compactSpan007_prefix :
    (compactRest00 408).take 448 = active8Chunk000Chars00 := by rfl

theorem compactSpan007_split :
    compactRest00 408 = active8Chunk000Chars00 ++ compactRest00 856 := by
  calc
    compactRest00 408 =
        (compactRest00 408).take 448 ++ (compactRest00 408).drop 448 :=
      (List.take_append_drop 448 (compactRest00 408)).symm
    _ = active8Chunk000Chars00 ++ (compactRest00 408).drop 448 :=
      congrArg (fun part => part ++ (compactRest00 408).drop 448) compactSpan007_prefix
    _ = active8Chunk000Chars00 ++ compactRest00 856 :=
      congrArg (fun tail => active8Chunk000Chars00 ++ tail) (compactRest00_drop 408 448)

theorem compactSpan007_rest_eq (htail : geometryChars00.drop 856 = compactRest00 856) :
    geometryChars00.drop 408 = compactRest00 408 := by
  have hp : (geometryChars00.drop 408).take 448 = active8Chunk000Chars00 :=
    geometryChars00_active8_chunk_000_prefix
  exact (list_drop_split_of_prefix geometryChars00 408 448 active8Chunk000Chars00 hp).trans
    ((congrArg (fun tail => active8Chunk000Chars00 ++ tail) htail).trans compactSpan007_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_007_complete"
  err.flush

theorem group000_rest_eq
    (htail : geometryChars00.drop 856 = compactRest00 856) :
    geometryChars00.drop 0 = compactRest00 0 := by
  have h007 := compactSpan007_rest_eq htail
  have h006 := compactSpan006_rest_eq h007
  have h005 := compactSpan005_rest_eq h006
  have h004 := compactSpan004_rest_eq h005
  have h003 := compactSpan003_rest_eq h004
  have h002 := compactSpan002_rest_eq h003
  have h001 := compactSpan001_rest_eq h002
  have h000 := compactSpan000_rest_eq h001
  exact h000

#print axioms compactSpan000_prefix
#print axioms compactSpan000_split
#print axioms compactSpan000_rest_eq
#print axioms compactSpan001_prefix
#print axioms compactSpan001_split
#print axioms compactSpan001_rest_eq
#print axioms compactSpan002_prefix
#print axioms compactSpan002_split
#print axioms compactSpan002_rest_eq
#print axioms compactSpan003_prefix
#print axioms compactSpan003_split
#print axioms compactSpan003_rest_eq
#print axioms compactSpan004_prefix
#print axioms compactSpan004_split
#print axioms compactSpan004_rest_eq
#print axioms compactSpan005_prefix
#print axioms compactSpan005_split
#print axioms compactSpan005_rest_eq
#print axioms compactSpan006_prefix
#print axioms compactSpan006_split
#print axioms compactSpan006_rest_eq
#print axioms compactSpan007_prefix
#print axioms compactSpan007_split
#print axioms compactSpan007_rest_eq
#print axioms group000_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
