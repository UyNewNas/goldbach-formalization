import ImbalancedChen.P2OriginalSaving19GeometryPackedTransportInput00
import ImbalancedChen.P2OriginalSaving19GeometrySlice18833400
import ImbalancedChen.P2OriginalSaving19SimplicesField00
import ImbalancedChen.P2OriginalSaving19PhysicalVolumePrefix00
import ImbalancedChen.P2OriginalSaving19WholeValue00
import ImbalancedChen.P2OriginalSaving19WholeParse00

/-! Exact compact prefix group 36, bytes [188334,195134).
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
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_181_before_prefix"
  err.flush

theorem compactSpan181_prefix :
    (compactRest00 188334).take 6442 = geometrySlice188334Chars00 := by rfl

theorem compactSpan181_split :
    compactRest00 188334 = geometrySlice188334Chars00 ++ compactRest00 194776 := by
  calc
    compactRest00 188334 =
        (compactRest00 188334).take 6442 ++ (compactRest00 188334).drop 6442 :=
      (List.take_append_drop 6442 (compactRest00 188334)).symm
    _ = geometrySlice188334Chars00 ++ (compactRest00 188334).drop 6442 :=
      congrArg (fun part => part ++ (compactRest00 188334).drop 6442) compactSpan181_prefix
    _ = geometrySlice188334Chars00 ++ compactRest00 194776 :=
      congrArg (fun tail => geometrySlice188334Chars00 ++ tail) (compactRest00_drop 188334 6442)

theorem compactSpan181_rest_eq (htail : geometryChars00.drop 194776 = compactRest00 194776) :
    geometryChars00.drop 188334 = compactRest00 188334 := by
  have hp : (geometryChars00.drop 188334).take 6442 = geometrySlice188334Chars00 :=
    geometryChars00_slice_188334_prefix
  exact (list_drop_split_of_prefix geometryChars00 188334 6442 geometrySlice188334Chars00 hp).trans
    ((congrArg (fun tail => geometrySlice188334Chars00 ++ tail) htail).trans compactSpan181_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_181_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_182_before_prefix"
  err.flush

theorem compactSpan182_prefix :
    (compactRest00 194776).take 1 = simplicesSeparatorChars00 := by rfl

theorem compactSpan182_split :
    compactRest00 194776 = simplicesSeparatorChars00 ++ compactRest00 194777 := by
  calc
    compactRest00 194776 =
        (compactRest00 194776).take 1 ++ (compactRest00 194776).drop 1 :=
      (List.take_append_drop 1 (compactRest00 194776)).symm
    _ = simplicesSeparatorChars00 ++ (compactRest00 194776).drop 1 :=
      congrArg (fun part => part ++ (compactRest00 194776).drop 1) compactSpan182_prefix
    _ = simplicesSeparatorChars00 ++ compactRest00 194777 :=
      congrArg (fun tail => simplicesSeparatorChars00 ++ tail) (compactRest00_drop 194776 1)

theorem compactSpan182_rest_eq (htail : geometryChars00.drop 194777 = compactRest00 194777) :
    geometryChars00.drop 194776 = compactRest00 194776 := by
  have hp : (geometryChars00.drop 194776).take 1 = simplicesSeparatorChars00 :=
    geometryChars00_simplices_separator_prefix
  exact (list_drop_split_of_prefix geometryChars00 194776 1 simplicesSeparatorChars00 hp).trans
    ((congrArg (fun tail => simplicesSeparatorChars00 ++ tail) htail).trans compactSpan182_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_182_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_183_before_prefix"
  err.flush

theorem compactSpan183_prefix :
    (compactRest00 194777).take 165 = physicalVolumePrefixChars00 := by rfl

theorem compactSpan183_split :
    compactRest00 194777 = physicalVolumePrefixChars00 ++ compactRest00 194942 := by
  calc
    compactRest00 194777 =
        (compactRest00 194777).take 165 ++ (compactRest00 194777).drop 165 :=
      (List.take_append_drop 165 (compactRest00 194777)).symm
    _ = physicalVolumePrefixChars00 ++ (compactRest00 194777).drop 165 :=
      congrArg (fun part => part ++ (compactRest00 194777).drop 165) compactSpan183_prefix
    _ = physicalVolumePrefixChars00 ++ compactRest00 194942 :=
      congrArg (fun tail => physicalVolumePrefixChars00 ++ tail) (compactRest00_drop 194777 165)

theorem compactSpan183_rest_eq (htail : geometryChars00.drop 194942 = compactRest00 194942) :
    geometryChars00.drop 194777 = compactRest00 194777 := by
  have hp : (geometryChars00.drop 194777).take 165 = physicalVolumePrefixChars00 :=
    geometryChars00_physical_volume_prefix
  exact (list_drop_split_of_prefix geometryChars00 194777 165 physicalVolumePrefixChars00 hp).trans
    ((congrArg (fun tail => physicalVolumePrefixChars00 ++ tail) htail).trans compactSpan183_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_183_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_184_before_prefix"
  err.flush

theorem compactSpan184_prefix :
    (compactRest00 194942).take 190 = integralGapPrefixChars00 := by rfl

theorem compactSpan184_split :
    compactRest00 194942 = integralGapPrefixChars00 ++ compactRest00 195132 := by
  calc
    compactRest00 194942 =
        (compactRest00 194942).take 190 ++ (compactRest00 194942).drop 190 :=
      (List.take_append_drop 190 (compactRest00 194942)).symm
    _ = integralGapPrefixChars00 ++ (compactRest00 194942).drop 190 :=
      congrArg (fun part => part ++ (compactRest00 194942).drop 190) compactSpan184_prefix
    _ = integralGapPrefixChars00 ++ compactRest00 195132 :=
      congrArg (fun tail => integralGapPrefixChars00 ++ tail) (compactRest00_drop 194942 190)

theorem compactSpan184_rest_eq (htail : geometryChars00.drop 195132 = compactRest00 195132) :
    geometryChars00.drop 194942 = compactRest00 194942 := by
  have hp : (geometryChars00.drop 194942).take 190 = integralGapPrefixChars00 :=
    geometryChars00_integral_gap_prefix
  exact (list_drop_split_of_prefix geometryChars00 194942 190 integralGapPrefixChars00 hp).trans
    ((congrArg (fun tail => integralGapPrefixChars00 ++ tail) htail).trans compactSpan184_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_184_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_185_before_prefix"
  err.flush

theorem compactSpan185_prefix :
    (compactRest00 195132).take 2 = geometryTailChars00 := by rfl

theorem compactSpan185_split :
    compactRest00 195132 = geometryTailChars00 ++ compactRest00 195134 := by
  calc
    compactRest00 195132 =
        (compactRest00 195132).take 2 ++ (compactRest00 195132).drop 2 :=
      (List.take_append_drop 2 (compactRest00 195132)).symm
    _ = geometryTailChars00 ++ (compactRest00 195132).drop 2 :=
      congrArg (fun part => part ++ (compactRest00 195132).drop 2) compactSpan185_prefix
    _ = geometryTailChars00 ++ compactRest00 195134 :=
      congrArg (fun tail => geometryTailChars00 ++ tail) (compactRest00_drop 195132 2)

theorem compactSpan185_rest_eq (htail : geometryChars00.drop 195134 = compactRest00 195134) :
    geometryChars00.drop 195132 = compactRest00 195132 := by
  have hp : (geometryChars00.drop 195132).take 2 = geometryTailChars00 :=
    geometryChars00_final_tail_prefix
  exact (list_drop_split_of_prefix geometryChars00 195132 2 geometryTailChars00 hp).trans
    ((congrArg (fun tail => geometryTailChars00 ++ tail) htail).trans compactSpan185_split.symm)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY_TRANSPORT span_185_complete"
  err.flush

theorem group036_rest_eq
    (htail : geometryChars00.drop 195134 = compactRest00 195134) :
    geometryChars00.drop 188334 = compactRest00 188334 := by
  have h185 := compactSpan185_rest_eq htail
  have h184 := compactSpan184_rest_eq h185
  have h183 := compactSpan183_rest_eq h184
  have h182 := compactSpan182_rest_eq h183
  have h181 := compactSpan181_rest_eq h182
  exact h181

#print axioms compactSpan181_prefix
#print axioms compactSpan181_split
#print axioms compactSpan181_rest_eq
#print axioms compactSpan182_prefix
#print axioms compactSpan182_split
#print axioms compactSpan182_rest_eq
#print axioms compactSpan183_prefix
#print axioms compactSpan183_split
#print axioms compactSpan183_rest_eq
#print axioms compactSpan184_prefix
#print axioms compactSpan184_split
#print axioms compactSpan184_rest_eq
#print axioms compactSpan185_prefix
#print axioms compactSpan185_split
#print axioms compactSpan185_rest_eq
#print axioms group036_rest_eq

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
