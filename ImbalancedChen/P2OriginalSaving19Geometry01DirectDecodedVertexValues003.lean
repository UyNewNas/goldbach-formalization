import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVertexValuesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedVertexValues002

/-! Original vertex_values typed block 3, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson024 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped024 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((15327977 : ℚ) / (228000000 : ℚ)), ((15327977 : ℚ) / (228000000 : ℚ)), ((5515597 : ℚ) / (38000000 : ℚ)), ((2859379 : ℚ) / (28500000 : ℚ)), ((571891 : ℚ) / (11400000 : ℚ)), ((953101 : ℚ) / (19000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_024_before_decode"
  err.flush

theorem decode_geometry_VertexValues_024 :
    decodeVertexValues geometryVertexValuesJson024 = .ok geometryVertexValuesTyped024 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_024_decoded"
  err.flush

noncomputable def geometryVertexValuesJson025 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped025 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((14718969 : ℚ) / (171500000 : ℚ)), ((14718969 : ℚ) / (171500000 : ℚ)), ((178123 : ℚ) / (1225000 : ℚ)), ((500781 : ℚ) / (4287500 : ℚ)), ((178123 : ℚ) / (2450000 : ℚ)), ((756263 : ℚ) / (17150000 : ℚ)), ((178123 : ℚ) / (4900000 : ℚ)), ((178123 : ℚ) / (4900000 : ℚ)), ((4906323 : ℚ) / (171500000 : ℚ)), ((4906323 : ℚ) / (171500000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_025_before_decode"
  err.flush

theorem decode_geometry_VertexValues_025 :
    decodeVertexValues geometryVertexValuesJson025 = .ok geometryVertexValuesTyped025 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_025_decoded"
  err.flush

noncomputable def geometryVertexValuesJson026 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped026 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((1823 : ℚ) / (25000 : ℚ)), ((1823 : ℚ) / (25000 : ℚ)), ((1317691 : ℚ) / (9000000 : ℚ)), ((1098949 : ℚ) / (9000000 : ℚ)), ((1317691 : ℚ) / (18000000 : ℚ)), ((880207 : ℚ) / (18000000 : ℚ)), ((1317691 : ℚ) / (36000000 : ℚ)), ((1317691 : ℚ) / (36000000 : ℚ)), ((1317691 : ℚ) / (36000000 : ℚ)), ((1823 : ℚ) / (75000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_026_before_decode"
  err.flush

theorem decode_geometry_VertexValues_026 :
    decodeVertexValues geometryVertexValuesJson026 = .ok geometryVertexValuesTyped026 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_026_decoded"
  err.flush

noncomputable def geometryVertexValuesJson027 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped027 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5109507 : ℚ) / (64000000 : ℚ)), ((5109507 : ℚ) / (64000000 : ℚ)), ((14202913 : ℚ) / (96000000 : ℚ)), ((23296703 : ℚ) / (192000000 : ℚ)), ((14202913 : ℚ) / (192000000 : ℚ)), ((909379 : ℚ) / (19200000 : ℚ)), ((4546639 : ℚ) / (96000000 : ℚ)), ((1021927 : ℚ) / (38400000 : ℚ)), ((1021927 : ℚ) / (38400000 : ℚ)), ((1703169 : ℚ) / (64000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_027_before_decode"
  err.flush

theorem decode_geometry_VertexValues_027 :
    decodeVertexValues geometryVertexValuesJson027 = .ok geometryVertexValuesTyped027 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_027_decoded"
  err.flush

noncomputable def geometryVertexValuesJson028 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped028 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5109531 : ℚ) / (64000000 : ℚ)), ((5109531 : ℚ) / (64000000 : ℚ)), ((4734307 : ℚ) / (32000000 : ℚ)), ((1553113 : ℚ) / (12800000 : ℚ)), ((4734307 : ℚ) / (64000000 : ℚ)), ((1515629 : ℚ) / (32000000 : ℚ)), ((4734307 : ℚ) / (128000000 : ℚ)), ((4734307 : ℚ) / (128000000 : ℚ)), ((1703177 : ℚ) / (64000000 : ℚ)), ((1703177 : ℚ) / (64000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_028_before_decode"
  err.flush

theorem decode_geometry_VertexValues_028 :
    decodeVertexValues geometryVertexValuesJson028 = .ok geometryVertexValuesTyped028 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_028_decoded"
  err.flush

noncomputable def geometryVertexValuesJson029 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped029 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5109531 : ℚ) / (64000000 : ℚ)), ((5109531 : ℚ) / (64000000 : ℚ)), ((4734307 : ℚ) / (32000000 : ℚ)), ((1553113 : ℚ) / (12800000 : ℚ)), ((4734307 : ℚ) / (64000000 : ℚ)), ((1515629 : ℚ) / (32000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((5109659 : ℚ) / (192000000 : ℚ)), ((1703177 : ℚ) / (64000000 : ℚ)), ((1703177 : ℚ) / (64000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_029_before_decode"
  err.flush

theorem decode_geometry_VertexValues_029 :
    decodeVertexValues geometryVertexValuesJson029 = .ok geometryVertexValuesTyped029 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_029_decoded"
  err.flush

noncomputable def geometryVertexValuesJson030 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped030 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484283 : ℚ) / (36000000 : ℚ)), ((2484283 : ℚ) / (36000000 : ℚ)), ((403111 : ℚ) / (2700000 : ℚ)), ((5577961 : ℚ) / (54000000 : ℚ)), ((2484691 : ℚ) / (54000000 : ℚ)), ((2484547 : ℚ) / (54000000 : ℚ)), ((2484403 : ℚ) / (54000000 : ℚ)), ((2484403 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_030_before_decode"
  err.flush

theorem decode_geometry_VertexValues_030 :
    decodeVertexValues geometryVertexValuesJson030 = .ok geometryVertexValuesTyped030 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_030_decoded"
  err.flush

noncomputable def geometryVertexValuesJson031 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped031 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484307 : ℚ) / (36000000 : ℚ)), ((2484307 : ℚ) / (36000000 : ℚ)), ((2015561 : ℚ) / (13500000 : ℚ)), ((5578009 : ℚ) / (54000000 : ℚ)), ((2484667 : ℚ) / (54000000 : ℚ)), ((2484523 : ℚ) / (54000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_031_before_decode"
  err.flush

theorem decode_geometry_VertexValues_031 :
    decodeVertexValues geometryVertexValuesJson031 = .ok geometryVertexValuesTyped031 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_031_decoded"
  err.flush

noncomputable def geometryVertexValuesJsonBlock003 : List SourceJson := [geometryVertexValuesJson024, geometryVertexValuesJson025, geometryVertexValuesJson026, geometryVertexValuesJson027, geometryVertexValuesJson028, geometryVertexValuesJson029, geometryVertexValuesJson030, geometryVertexValuesJson031]
noncomputable def geometryVertexValuesTypedBlock003 : List (VertexValues) := [geometryVertexValuesTyped024, geometryVertexValuesTyped025, geometryVertexValuesTyped026, geometryVertexValuesTyped027, geometryVertexValuesTyped028, geometryVertexValuesTyped029, geometryVertexValuesTyped030, geometryVertexValuesTyped031]
noncomputable def geometryVertexValuesTypedThroughBlock003 : List (VertexValues) := geometryVertexValuesTypedThroughBlock002 ++ geometryVertexValuesTypedBlock003

theorem geometry_VertexValues_block_003_push_eq (acc : List SourceJson) :
    VertexValuesBlock003.blockPush acc = [geometryVertexValuesJson031, geometryVertexValuesJson030, geometryVertexValuesJson029, geometryVertexValuesJson028, geometryVertexValuesJson027, geometryVertexValuesJson026, geometryVertexValuesJson025, geometryVertexValuesJson024] ++ acc := by rfl

theorem geometry_VertexValues_block_003_reverse (acc : List SourceJson) :
    (VertexValuesBlock003.blockPush acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock003 := by
  rw [geometry_VertexValues_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_003 :
    geometryVertexValuesJsonBlock003.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock003 := by
  simp only [geometryVertexValuesJsonBlock003, geometryVertexValuesTypedBlock003, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_024, decode_geometry_VertexValues_025, decode_geometry_VertexValues_026, decode_geometry_VertexValues_027, decode_geometry_VertexValues_028, decode_geometry_VertexValues_029, decode_geometry_VertexValues_030, decode_geometry_VertexValues_031]
  rfl

theorem decode_geometry_VertexValues_through_block_003 :
    VertexValuesValue.arrayAcc004.reverse.mapM decodeVertexValues = .ok geometryVertexValuesTypedThroughBlock003 := by
  change (VertexValuesBlock003.blockPush VertexValuesValue.arrayAcc003).reverse.mapM decodeVertexValues = _
  rw [geometry_VertexValues_block_003_reverse]
  rw [List.mapM_append, decode_geometry_VertexValues_through_block_002, decode_geometry_VertexValues_block_003]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_block_003_complete"
  err.flush

#print axioms decode_geometry_VertexValues_024
#print axioms decode_geometry_VertexValues_025
#print axioms decode_geometry_VertexValues_026
#print axioms decode_geometry_VertexValues_027
#print axioms decode_geometry_VertexValues_028
#print axioms decode_geometry_VertexValues_029
#print axioms decode_geometry_VertexValues_030
#print axioms decode_geometry_VertexValues_031
#print axioms geometry_VertexValues_block_003_push_eq
#print axioms geometry_VertexValues_block_003_reverse
#print axioms decode_geometry_VertexValues_block_003
#print axioms decode_geometry_VertexValues_through_block_003

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
