import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVerticesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedVertices001

/-! Original vertices typed block 2, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVerticesJson032 : SourceJson :=
  (VerticesBlock002.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVerticesTyped032 : Array ℚ :=
  #[((1515549 : ℚ) / (10000000 : ℚ)), ((3234139 : ℚ) / (30000000 : ℚ)), ((1921471 : ℚ) / (30000000 : ℚ)), ((109389 : ℚ) / (2500000 : ℚ)), ((328147 : ℚ) / (7500000 : ℚ)), ((328147 : ℚ) / (7500000 : ℚ)), ((164071 : ℚ) / (3750000 : ℚ)), ((164071 : ℚ) / (3750000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_032_before_decode"
  err.flush

theorem decode_geometry_Vertices_032 :
    rationalArray geometryVerticesJson032 = .ok geometryVerticesTyped032 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_032_decoded"
  err.flush

noncomputable def geometryVerticesJson033 : SourceJson :=
  (VerticesBlock002.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVerticesTyped033 : Array ℚ :=
  #[((1515557 : ℚ) / (10000000 : ℚ)), ((3234187 : ℚ) / (30000000 : ℚ)), ((1921543 : ℚ) / (30000000 : ℚ)), ((109387 : ℚ) / (2500000 : ℚ)), ((328141 : ℚ) / (7500000 : ℚ)), ((328141 : ℚ) / (7500000 : ℚ)), ((328141 : ℚ) / (7500000 : ℚ)), ((41017 : ℚ) / (937500 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_033_before_decode"
  err.flush

theorem decode_geometry_Vertices_033 :
    rationalArray geometryVerticesJson033 = .ok geometryVerticesTyped033 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_033_decoded"
  err.flush

noncomputable def geometryVerticesJson034 : SourceJson :=
  (VerticesBlock002.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVerticesTyped034 : Array ℚ :=
  #[((1171847 : ℚ) / (7500000 : ℚ)), ((3515621 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1171927 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_034_before_decode"
  err.flush

theorem decode_geometry_Vertices_034 :
    rationalArray geometryVerticesJson034 = .ok geometryVerticesTyped034 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_034_decoded"
  err.flush

noncomputable def geometryVerticesJson035 : SourceJson :=
  (VerticesBlock002.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVerticesTyped035 : Array ℚ :=
  #[((1171847 : ℚ) / (7500000 : ℚ)), ((3515621 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1171927 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_035_before_decode"
  err.flush

theorem decode_geometry_Vertices_035 :
    rationalArray geometryVerticesJson035 = .ok geometryVerticesTyped035 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_035_decoded"
  err.flush

noncomputable def geometryVerticesJson036 : SourceJson :=
  (VerticesBlock002.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVerticesTyped036 : Array ℚ :=
  #[((3859259 : ℚ) / (24000000 : ℚ)), ((505199 : ℚ) / (4000000 : ℚ)), ((828257 : ℚ) / (24000000 : ℚ)), ((828193 : ℚ) / (24000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_036_before_decode"
  err.flush

theorem decode_geometry_Vertices_036 :
    rationalArray geometryVerticesJson036 = .ok geometryVerticesTyped036 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_036_decoded"
  err.flush

noncomputable def geometryVerticesJson037 : SourceJson :=
  (VerticesBlock002.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVerticesTyped037 : Array ℚ :=
  #[((2315557 : ℚ) / (14400000 : ℚ)), ((4546799 : ℚ) / (36000000 : ℚ)), ((2484763 : ℚ) / (72000000 : ℚ)), ((2484571 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_037_before_decode"
  err.flush

theorem decode_geometry_Vertices_037 :
    rationalArray geometryVerticesJson037 = .ok geometryVerticesTyped037 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_037_decoded"
  err.flush

noncomputable def geometryVerticesJson038 : SourceJson :=
  (VerticesBlock002.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped038 : Array ℚ :=
  #[((4640469 : ℚ) / (28000000 : ℚ)), ((571859 : ℚ) / (4200000 : ℚ)), ((2484451 : ℚ) / (42000000 : ℚ)), ((33129 : ℚ) / (1120000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_038_before_decode"
  err.flush

theorem decode_geometry_Vertices_038 :
    rationalArray geometryVerticesJson038 = .ok geometryVerticesTyped038 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_038_decoded"
  err.flush

noncomputable def geometryVerticesJson039 : SourceJson :=
  (VerticesBlock002.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped039 : Array ℚ :=
  #[((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2484443 : ℚ) / (42000000 : ℚ)), ((2484667 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((828129 : ℚ) / (28000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_039_before_decode"
  err.flush

theorem decode_geometry_Vertices_039 :
    rationalArray geometryVerticesJson039 = .ok geometryVerticesTyped039 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_039_decoded"
  err.flush

noncomputable def geometryVerticesJsonBlock002 : List SourceJson := [geometryVerticesJson032, geometryVerticesJson033, geometryVerticesJson034, geometryVerticesJson035, geometryVerticesJson036, geometryVerticesJson037, geometryVerticesJson038, geometryVerticesJson039]
noncomputable def geometryVerticesTypedBlock002 : List (Array ℚ) := [geometryVerticesTyped032, geometryVerticesTyped033, geometryVerticesTyped034, geometryVerticesTyped035, geometryVerticesTyped036, geometryVerticesTyped037, geometryVerticesTyped038, geometryVerticesTyped039]
noncomputable def geometryVerticesTypedThroughBlock002 : List (Array ℚ) := geometryVerticesTypedThroughBlock001 ++ geometryVerticesTypedBlock002

theorem geometry_Vertices_block_002_push_eq (acc : List SourceJson) :
    VerticesBlock002.blockPush acc = [geometryVerticesJson039, geometryVerticesJson038, geometryVerticesJson037, geometryVerticesJson036, geometryVerticesJson035, geometryVerticesJson034, geometryVerticesJson033, geometryVerticesJson032] ++ acc := by rfl

theorem geometry_Vertices_block_002_reverse (acc : List SourceJson) :
    (VerticesBlock002.blockPush acc).reverse = acc.reverse ++ geometryVerticesJsonBlock002 := by
  rw [geometry_Vertices_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Vertices_block_002 :
    geometryVerticesJsonBlock002.mapM rationalArray = .ok geometryVerticesTypedBlock002 := by
  simp only [geometryVerticesJsonBlock002, geometryVerticesTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_Vertices_032, decode_geometry_Vertices_033, decode_geometry_Vertices_034, decode_geometry_Vertices_035, decode_geometry_Vertices_036, decode_geometry_Vertices_037, decode_geometry_Vertices_038, decode_geometry_Vertices_039]
  rfl

theorem decode_geometry_Vertices_through_block_002 :
    VerticesValue.arrayAcc003.reverse.mapM rationalArray = .ok geometryVerticesTypedThroughBlock002 := by
  change (VerticesBlock002.blockPush VerticesValue.arrayAcc002).reverse.mapM rationalArray = _
  rw [geometry_Vertices_block_002_reverse]
  rw [List.mapM_append, decode_geometry_Vertices_through_block_001, decode_geometry_Vertices_block_002]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_block_002_complete"
  err.flush

#print axioms decode_geometry_Vertices_032
#print axioms decode_geometry_Vertices_033
#print axioms decode_geometry_Vertices_034
#print axioms decode_geometry_Vertices_035
#print axioms decode_geometry_Vertices_036
#print axioms decode_geometry_Vertices_037
#print axioms decode_geometry_Vertices_038
#print axioms decode_geometry_Vertices_039
#print axioms geometry_Vertices_block_002_push_eq
#print axioms geometry_Vertices_block_002_reverse
#print axioms decode_geometry_Vertices_block_002
#print axioms decode_geometry_Vertices_through_block_002

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
