import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVertexValuesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedVertexValues003

/-! Original vertex_values typed block 4, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson032 : SourceJson :=
  (VertexValuesBlock004.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped032 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((3328841 : ℚ) / (60000000 : ℚ)), ((3328841 : ℚ) / (60000000 : ℚ)), ((1515549 : ℚ) / (10000000 : ℚ)), ((3234139 : ℚ) / (30000000 : ℚ)), ((1921471 : ℚ) / (30000000 : ℚ)), ((109389 : ℚ) / (2500000 : ℚ)), ((328147 : ℚ) / (7500000 : ℚ)), ((328147 : ℚ) / (7500000 : ℚ)), ((164071 : ℚ) / (3750000 : ℚ)), ((164071 : ℚ) / (3750000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_032_before_decode"
  err.flush

theorem decode_geometry_VertexValues_032 :
    decodeVertexValues geometryVertexValuesJson032 = .ok geometryVertexValuesTyped032 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_032_decoded"
  err.flush

noncomputable def geometryVertexValuesJson033 : SourceJson :=
  (VertexValuesBlock004.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped033 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((3328753 : ℚ) / (60000000 : ℚ)), ((3328753 : ℚ) / (60000000 : ℚ)), ((1515557 : ℚ) / (10000000 : ℚ)), ((3234187 : ℚ) / (30000000 : ℚ)), ((1921543 : ℚ) / (30000000 : ℚ)), ((109387 : ℚ) / (2500000 : ℚ)), ((328141 : ℚ) / (7500000 : ℚ)), ((328141 : ℚ) / (7500000 : ℚ)), ((328141 : ℚ) / (7500000 : ℚ)), ((41017 : ℚ) / (937500 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_033_before_decode"
  err.flush

theorem decode_geometry_VertexValues_033 :
    decodeVertexValues geometryVertexValuesJson033 = .ok geometryVertexValuesTyped033 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_033_decoded"
  err.flush

noncomputable def geometryVertexValuesJson034 : SourceJson :=
  (VertexValuesBlock004.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped034 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((3047359 : ℚ) / (60000000 : ℚ)), ((3047359 : ℚ) / (60000000 : ℚ)), ((1171847 : ℚ) / (7500000 : ℚ)), ((3515621 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1171927 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_034_before_decode"
  err.flush

theorem decode_geometry_VertexValues_034 :
    decodeVertexValues geometryVertexValuesJson034 = .ok geometryVertexValuesTyped034 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_034_decoded"
  err.flush

noncomputable def geometryVertexValuesJson035 : SourceJson :=
  (VertexValuesBlock004.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped035 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((1015773 : ℚ) / (20000000 : ℚ)), ((1015773 : ℚ) / (20000000 : ℚ)), ((1171847 : ℚ) / (7500000 : ℚ)), ((3515621 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1171927 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_035_before_decode"
  err.flush

theorem decode_geometry_VertexValues_035 :
    decodeVertexValues geometryVertexValuesJson035 = .ok geometryVertexValuesTyped035 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_035_decoded"
  err.flush

noncomputable def geometryVertexValuesJson036 : SourceJson :=
  (VertexValuesBlock004.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped036 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((3859259 : ℚ) / (24000000 : ℚ)), ((505199 : ℚ) / (4000000 : ℚ)), ((828257 : ℚ) / (24000000 : ℚ)), ((828193 : ℚ) / (24000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_036_before_decode"
  err.flush

theorem decode_geometry_VertexValues_036 :
    decodeVertexValues geometryVertexValuesJson036 = .ok geometryVertexValuesTyped036 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_036_decoded"
  err.flush

noncomputable def geometryVertexValuesJson037 : SourceJson :=
  (VertexValuesBlock004.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped037 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2315557 : ℚ) / (14400000 : ℚ)), ((4546799 : ℚ) / (36000000 : ℚ)), ((2484763 : ℚ) / (72000000 : ℚ)), ((2484571 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_037_before_decode"
  err.flush

theorem decode_geometry_VertexValues_037 :
    decodeVertexValues geometryVertexValuesJson037 = .ok geometryVertexValuesTyped037 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_037_decoded"
  err.flush

noncomputable def geometryVertexValuesJson038 : SourceJson :=
  (VertexValuesBlock004.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped038 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((496879 : ℚ) / (5600000 : ℚ)), ((496879 : ℚ) / (5600000 : ℚ)), ((4640469 : ℚ) / (28000000 : ℚ)), ((571859 : ℚ) / (4200000 : ℚ)), ((2484451 : ℚ) / (42000000 : ℚ)), ((33129 : ℚ) / (1120000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_038_before_decode"
  err.flush

theorem decode_geometry_VertexValues_038 :
    decodeVertexValues geometryVertexValuesJson038 = .ok geometryVertexValuesTyped038 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_038_decoded"
  err.flush

noncomputable def geometryVertexValuesJson039 : SourceJson :=
  (VertexValuesBlock004.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped039 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2484443 : ℚ) / (42000000 : ℚ)), ((2484667 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((828129 : ℚ) / (28000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_039_before_decode"
  err.flush

theorem decode_geometry_VertexValues_039 :
    decodeVertexValues geometryVertexValuesJson039 = .ok geometryVertexValuesTyped039 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_039_decoded"
  err.flush

noncomputable def geometryVertexValuesJsonBlock004 : List SourceJson := [geometryVertexValuesJson032, geometryVertexValuesJson033, geometryVertexValuesJson034, geometryVertexValuesJson035, geometryVertexValuesJson036, geometryVertexValuesJson037, geometryVertexValuesJson038, geometryVertexValuesJson039]
noncomputable def geometryVertexValuesTypedBlock004 : List (VertexValues) := [geometryVertexValuesTyped032, geometryVertexValuesTyped033, geometryVertexValuesTyped034, geometryVertexValuesTyped035, geometryVertexValuesTyped036, geometryVertexValuesTyped037, geometryVertexValuesTyped038, geometryVertexValuesTyped039]
noncomputable def geometryVertexValuesTypedThroughBlock004 : List (VertexValues) := geometryVertexValuesTypedThroughBlock003 ++ geometryVertexValuesTypedBlock004

theorem geometry_VertexValues_block_004_push_eq (acc : List SourceJson) :
    VertexValuesBlock004.blockPush acc = [geometryVertexValuesJson039, geometryVertexValuesJson038, geometryVertexValuesJson037, geometryVertexValuesJson036, geometryVertexValuesJson035, geometryVertexValuesJson034, geometryVertexValuesJson033, geometryVertexValuesJson032] ++ acc := by rfl

theorem geometry_VertexValues_block_004_reverse (acc : List SourceJson) :
    (VertexValuesBlock004.blockPush acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock004 := by
  rw [geometry_VertexValues_block_004_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_004 :
    geometryVertexValuesJsonBlock004.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock004 := by
  simp only [geometryVertexValuesJsonBlock004, geometryVertexValuesTypedBlock004, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_032, decode_geometry_VertexValues_033, decode_geometry_VertexValues_034, decode_geometry_VertexValues_035, decode_geometry_VertexValues_036, decode_geometry_VertexValues_037, decode_geometry_VertexValues_038, decode_geometry_VertexValues_039]
  rfl

theorem decode_geometry_VertexValues_through_block_004 :
    VertexValuesValue.arrayAcc005.reverse.mapM decodeVertexValues = .ok geometryVertexValuesTypedThroughBlock004 := by
  change (VertexValuesBlock004.blockPush VertexValuesValue.arrayAcc004).reverse.mapM decodeVertexValues = _
  rw [geometry_VertexValues_block_004_reverse]
  rw [List.mapM_append, decode_geometry_VertexValues_through_block_003, decode_geometry_VertexValues_block_004]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_block_004_complete"
  err.flush

#print axioms decode_geometry_VertexValues_032
#print axioms decode_geometry_VertexValues_033
#print axioms decode_geometry_VertexValues_034
#print axioms decode_geometry_VertexValues_035
#print axioms decode_geometry_VertexValues_036
#print axioms decode_geometry_VertexValues_037
#print axioms decode_geometry_VertexValues_038
#print axioms decode_geometry_VertexValues_039
#print axioms geometry_VertexValues_block_004_push_eq
#print axioms geometry_VertexValues_block_004_reverse
#print axioms decode_geometry_VertexValues_block_004
#print axioms decode_geometry_VertexValues_through_block_004

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
