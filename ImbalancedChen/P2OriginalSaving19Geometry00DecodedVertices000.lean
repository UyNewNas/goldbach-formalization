import ImbalancedChen.P2OriginalSaving19ArchiveSchema
import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00000

/-! Actual original vertices typed block 0; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryVerticesJson000 : SourceJson :=
  (verticesChunk000Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped000 : Array ℚ :=
  #[((16546927 : ℚ) / (144000000 : ℚ)), ((11578553 : ℚ) / (144000000 : ℚ)), ((11578169 : ℚ) / (144000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_000_before_decode"
  err.flush

theorem decode_geometry_Vertices_000 :
    rationalArray geometryVerticesJson000 = .ok geometryVerticesTyped000 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_000_decoded"
  err.flush

noncomputable def geometryVerticesJson001 : SourceJson :=
  (verticesChunk000Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped001 : Array ℚ :=
  #[((1103129 : ℚ) / (9600000 : ℚ)), ((257301 : ℚ) / (3200000 : ℚ)), ((3859387 : ℚ) / (48000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_001_before_decode"
  err.flush

theorem decode_geometry_Vertices_001 :
    rationalArray geometryVerticesJson001 = .ok geometryVerticesTyped001 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_001_decoded"
  err.flush

theorem geometry_Vertices_chunk_000_push_eq (acc : List SourceJson) :
    verticesChunk000Push00 acc = [geometryVerticesJson001, geometryVerticesJson000] ++ acc := by rfl

noncomputable def geometryVerticesJson002 : SourceJson :=
  (verticesChunk001Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped002 : Array ℚ :=
  #[((24265621 : ℚ) / (208000000 : ℚ)), ((734379 : ℚ) / (8000000 : ℚ)), ((8453137 : ℚ) / (104000000 : ℚ)), ((7359347 : ℚ) / (104000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((1703113 : ℚ) / (52000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_002_before_decode"
  err.flush

theorem decode_geometry_Vertices_002 :
    rationalArray geometryVerticesJson002 = .ok geometryVerticesTyped002 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_002_decoded"
  err.flush

noncomputable def geometryVerticesJson003 : SourceJson :=
  (verticesChunk001Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped003 : Array ℚ :=
  #[((26609371 : ℚ) / (228000000 : ℚ)), ((10328177 : ℚ) / (114000000 : ℚ)), ((3078129 : ℚ) / (38000000 : ℚ)), ((8140597 : ℚ) / (114000000 : ℚ)), ((8140597 : ℚ) / (228000000 : ℚ)), ((8140597 : ℚ) / (228000000 : ℚ)), ((1265617 : ℚ) / (38000000 : ℚ)), ((1265617 : ℚ) / (38000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_003_before_decode"
  err.flush

theorem decode_geometry_Vertices_003 :
    rationalArray geometryVerticesJson003 = .ok geometryVerticesTyped003 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_003_decoded"
  err.flush

theorem geometry_Vertices_chunk_001_push_eq (acc : List SourceJson) :
    verticesChunk001Push00 acc = [geometryVerticesJson003, geometryVerticesJson002] ++ acc := by rfl

noncomputable def geometryVerticesJson004 : SourceJson :=
  (verticesChunk002Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped004 : Array ℚ :=
  #[((6109371 : ℚ) / (52250000 : ℚ)), ((1109401 : ℚ) / (13062500 : ℚ)), ((8328173 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (52250000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3343743 : ℚ) / (104500000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_004_before_decode"
  err.flush

theorem decode_geometry_Vertices_004 :
    rationalArray geometryVerticesJson004 = .ok geometryVerticesTyped004 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_004_decoded"
  err.flush

noncomputable def geometryVerticesJson005 : SourceJson :=
  (verticesChunk002Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped005 : Array ℚ :=
  #[((1456249 : ℚ) / (12450000 : ℚ)), ((65236 : ℚ) / (778125 : ℚ)), ((659379 : ℚ) / (8300000 : ℚ)), ((934361 : ℚ) / (12450000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((1374993 : ℚ) / (41500000 : ℚ)), ((1374993 : ℚ) / (41500000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_005_before_decode"
  err.flush

theorem decode_geometry_Vertices_005 :
    rationalArray geometryVerticesJson005 = .ok geometryVerticesTyped005 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_005_decoded"
  err.flush

theorem geometry_Vertices_chunk_002_push_eq (acc : List SourceJson) :
    verticesChunk002Push00 acc = [geometryVerticesJson005, geometryVerticesJson004] ++ acc := by rfl

noncomputable def geometryVerticesJson006 : SourceJson :=
  (verticesChunk003Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped006 : Array ℚ :=
  #[((3515621 : ℚ) / (30000000 : ℚ)), ((1171927 : ℚ) / (15000000 : ℚ)), ((390629 : ℚ) / (5000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_006_before_decode"
  err.flush

theorem decode_geometry_Vertices_006 :
    rationalArray geometryVerticesJson006 = .ok geometryVerticesTyped006 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_006_decoded"
  err.flush

noncomputable def geometryVerticesJson007 : SourceJson :=
  (verticesChunk003Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped007 : Array ℚ :=
  #[((3515621 : ℚ) / (30000000 : ℚ)), ((1171927 : ℚ) / (15000000 : ℚ)), ((390629 : ℚ) / (5000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_007_before_decode"
  err.flush

theorem decode_geometry_Vertices_007 :
    rationalArray geometryVerticesJson007 = .ok geometryVerticesTyped007 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_007_decoded"
  err.flush

theorem geometry_Vertices_chunk_003_push_eq (acc : List SourceJson) :
    verticesChunk003Push00 acc = [geometryVerticesJson007, geometryVerticesJson006] ++ acc := by rfl

noncomputable def geometryVerticesJsonBlock000 : List SourceJson := [geometryVerticesJson000, geometryVerticesJson001, geometryVerticesJson002, geometryVerticesJson003, geometryVerticesJson004, geometryVerticesJson005, geometryVerticesJson006, geometryVerticesJson007]
noncomputable def geometryVerticesTypedBlock000 : List (Array ℚ) := [geometryVerticesTyped000, geometryVerticesTyped001, geometryVerticesTyped002, geometryVerticesTyped003, geometryVerticesTyped004, geometryVerticesTyped005, geometryVerticesTyped006, geometryVerticesTyped007]
noncomputable def geometryVerticesBlock000Push (acc : List SourceJson) : List SourceJson := verticesChunk003Push00 (verticesChunk002Push00 (verticesChunk001Push00 (verticesChunk000Push00 (acc))))

theorem geometry_Vertices_block_000_push_eq (acc : List SourceJson) :
    geometryVerticesBlock000Push acc = [geometryVerticesJson007, geometryVerticesJson006, geometryVerticesJson005, geometryVerticesJson004, geometryVerticesJson003, geometryVerticesJson002, geometryVerticesJson001, geometryVerticesJson000] ++ acc := by rfl

theorem geometry_Vertices_block_000_reverse (acc : List SourceJson) :
    (geometryVerticesBlock000Push acc).reverse = acc.reverse ++ geometryVerticesJsonBlock000 := by
  rw [geometry_Vertices_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Vertices_block_000 :
    geometryVerticesJsonBlock000.mapM rationalArray = .ok geometryVerticesTypedBlock000 := by
  simp only [geometryVerticesJsonBlock000, geometryVerticesTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_Vertices_000, decode_geometry_Vertices_001, decode_geometry_Vertices_002, decode_geometry_Vertices_003, decode_geometry_Vertices_004, decode_geometry_Vertices_005, decode_geometry_Vertices_006, decode_geometry_Vertices_007]
  rfl

noncomputable def geometryVerticesTypedThroughBlock000 : List (Array ℚ) := geometryVerticesTypedBlock000

theorem decode_geometry_Vertices_through_block_000 :
    verticesArrayAcc00400.reverse.mapM rationalArray = .ok geometryVerticesTypedThroughBlock000 := by
  change (geometryVerticesBlock000Push verticesArrayAcc00000).reverse.mapM rationalArray = _
  rw [geometry_Vertices_block_000_reverse]
  exact decode_geometry_Vertices_block_000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_block_000_complete"
  err.flush

#print axioms decode_geometry_Vertices_000
#print axioms decode_geometry_Vertices_001
#print axioms geometry_Vertices_chunk_000_push_eq
#print axioms decode_geometry_Vertices_002
#print axioms decode_geometry_Vertices_003
#print axioms geometry_Vertices_chunk_001_push_eq
#print axioms decode_geometry_Vertices_004
#print axioms decode_geometry_Vertices_005
#print axioms geometry_Vertices_chunk_002_push_eq
#print axioms decode_geometry_Vertices_006
#print axioms decode_geometry_Vertices_007
#print axioms geometry_Vertices_chunk_003_push_eq
#print axioms geometry_Vertices_block_000_push_eq
#print axioms geometry_Vertices_block_000_reverse
#print axioms decode_geometry_Vertices_block_000
#print axioms decode_geometry_Vertices_through_block_000

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
