import ImbalancedChen.P2OriginalSaving19Geometry00DecodedVertices001
import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00200

/-! Actual original vertices typed block 2; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryVerticesJson016 : SourceJson :=
  (verticesChunk008Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped016 : Array ℚ :=
  #[((25323 : ℚ) / (200000 : ℚ)), ((392781 : ℚ) / (4000000 : ℚ)), ((375533 : ℚ) / (4000000 : ℚ)), ((130927 : ℚ) / (2000000 : ℚ)), ((130927 : ℚ) / (4000000 : ℚ)), ((130927 : ℚ) / (4000000 : ℚ)), ((130927 : ℚ) / (4000000 : ℚ)), ((113687 : ℚ) / (4000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_016_before_decode"
  err.flush

theorem decode_geometry_Vertices_016 :
    rationalArray geometryVerticesJson016 = .ok geometryVerticesTyped016 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_016_decoded"
  err.flush

noncomputable def geometryVerticesJson017 : SourceJson :=
  (verticesChunk008Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped017 : Array ℚ :=
  #[((2671843 : ℚ) / (21000000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((571871 : ℚ) / (8400000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((828129 : ℚ) / (28000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_017_before_decode"
  err.flush

theorem decode_geometry_Vertices_017 :
    rationalArray geometryVerticesJson017 = .ok geometryVerticesTyped017 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_017_decoded"
  err.flush

theorem geometry_Vertices_chunk_008_push_eq (acc : List SourceJson) :
    verticesChunk008Push00 acc = [geometryVerticesJson017, geometryVerticesJson016] ++ acc := by rfl

noncomputable def geometryVerticesJson018 : SourceJson :=
  (verticesChunk009Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped018 : Array ℚ :=
  #[((178123 : ℚ) / (1400000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((953117 : ℚ) / (14000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_018_before_decode"
  err.flush

theorem decode_geometry_Vertices_018 :
    rationalArray geometryVerticesJson018 = .ok geometryVerticesTyped018 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_018_decoded"
  err.flush

noncomputable def geometryVerticesJson019 : SourceJson :=
  (verticesChunk009Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped019 : Array ℚ :=
  #[((178123 : ℚ) / (1400000 : ℚ)), ((2746881 : ℚ) / (28000000 : ℚ)), ((378119 : ℚ) / (4000000 : ℚ)), ((915627 : ℚ) / (14000000 : ℚ)), ((915627 : ℚ) / (28000000 : ℚ)), ((915627 : ℚ) / (28000000 : ℚ)), ((163127 : ℚ) / (5600000 : ℚ)), ((163127 : ℚ) / (5600000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_019_before_decode"
  err.flush

theorem decode_geometry_Vertices_019 :
    rationalArray geometryVerticesJson019 = .ok geometryVerticesTyped019 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_019_decoded"
  err.flush

theorem geometry_Vertices_chunk_009_push_eq (acc : List SourceJson) :
    verticesChunk009Push00 acc = [geometryVerticesJson019, geometryVerticesJson018] ++ acc := by rfl

noncomputable def geometryVerticesJson020 : SourceJson :=
  (verticesChunk010Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped020 : Array ℚ :=
  #[((2171847 : ℚ) / (17000000 : ℚ)), ((6890589 : ℚ) / (68000000 : ℚ)), ((255621 : ℚ) / (2720000 : ℚ)), ((2296863 : ℚ) / (34000000 : ℚ)), ((2296863 : ℚ) / (68000000 : ℚ)), ((2296863 : ℚ) / (68000000 : ℚ)), ((2296863 : ℚ) / (68000000 : ℚ)), ((359387 : ℚ) / (13600000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_020_before_decode"
  err.flush

theorem decode_geometry_Vertices_020 :
    rationalArray geometryVerticesJson020 = .ok geometryVerticesTyped020 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_020_decoded"
  err.flush

noncomputable def geometryVerticesJson021 : SourceJson :=
  (verticesChunk010Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped021 : Array ℚ :=
  #[((25679 : ℚ) / (200000 : ℚ)), ((401493 : ℚ) / (4000000 : ℚ)), ((379749 : ℚ) / (4000000 : ℚ)), ((133831 : ℚ) / (2000000 : ℚ)), ((133831 : ℚ) / (4000000 : ℚ)), ((133831 : ℚ) / (4000000 : ℚ)), ((22419 : ℚ) / (800000 : ℚ)), ((22419 : ℚ) / (800000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_021_before_decode"
  err.flush

theorem decode_geometry_Vertices_021 :
    rationalArray geometryVerticesJson021 = .ok geometryVerticesTyped021 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_021_decoded"
  err.flush

theorem geometry_Vertices_chunk_010_push_eq (acc : List SourceJson) :
    verticesChunk010Push00 acc = [geometryVerticesJson021, geometryVerticesJson020] ++ acc := by rfl

noncomputable def geometryVerticesJson022 : SourceJson :=
  (verticesChunk011Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped022 : Array ℚ :=
  #[((234371 : ℚ) / (1800000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((1171879 : ℚ) / (18000000 : ℚ)), ((1171879 : ℚ) / (36000000 : ℚ)), ((1171879 : ℚ) / (36000000 : ℚ)), ((234371 : ℚ) / (7200000 : ℚ)), ((234371 : ℚ) / (7200000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_022_before_decode"
  err.flush

theorem decode_geometry_Vertices_022 :
    rationalArray geometryVerticesJson022 = .ok geometryVerticesTyped022 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_022_decoded"
  err.flush

noncomputable def geometryVerticesJson023 : SourceJson :=
  (verticesChunk011Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped023 : Array ℚ :=
  #[((234371 : ℚ) / (1800000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((1171879 : ℚ) / (18000000 : ℚ)), ((1171879 : ℚ) / (36000000 : ℚ)), ((1171879 : ℚ) / (36000000 : ℚ)), ((1171879 : ℚ) / (36000000 : ℚ)), ((234371 : ℚ) / (7200000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_023_before_decode"
  err.flush

theorem decode_geometry_Vertices_023 :
    rationalArray geometryVerticesJson023 = .ok geometryVerticesTyped023 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_023_decoded"
  err.flush

theorem geometry_Vertices_chunk_011_push_eq (acc : List SourceJson) :
    verticesChunk011Push00 acc = [geometryVerticesJson023, geometryVerticesJson022] ++ acc := by rfl

noncomputable def geometryVerticesJsonBlock002 : List SourceJson := [geometryVerticesJson016, geometryVerticesJson017, geometryVerticesJson018, geometryVerticesJson019, geometryVerticesJson020, geometryVerticesJson021, geometryVerticesJson022, geometryVerticesJson023]
noncomputable def geometryVerticesTypedBlock002 : List (Array ℚ) := [geometryVerticesTyped016, geometryVerticesTyped017, geometryVerticesTyped018, geometryVerticesTyped019, geometryVerticesTyped020, geometryVerticesTyped021, geometryVerticesTyped022, geometryVerticesTyped023]
noncomputable def geometryVerticesBlock002Push (acc : List SourceJson) : List SourceJson := verticesChunk011Push00 (verticesChunk010Push00 (verticesChunk009Push00 (verticesChunk008Push00 (acc))))

theorem geometry_Vertices_block_002_push_eq (acc : List SourceJson) :
    geometryVerticesBlock002Push acc = [geometryVerticesJson023, geometryVerticesJson022, geometryVerticesJson021, geometryVerticesJson020, geometryVerticesJson019, geometryVerticesJson018, geometryVerticesJson017, geometryVerticesJson016] ++ acc := by rfl

theorem geometry_Vertices_block_002_reverse (acc : List SourceJson) :
    (geometryVerticesBlock002Push acc).reverse = acc.reverse ++ geometryVerticesJsonBlock002 := by
  rw [geometry_Vertices_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Vertices_block_002 :
    geometryVerticesJsonBlock002.mapM rationalArray = .ok geometryVerticesTypedBlock002 := by
  simp only [geometryVerticesJsonBlock002, geometryVerticesTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_Vertices_016, decode_geometry_Vertices_017, decode_geometry_Vertices_018, decode_geometry_Vertices_019, decode_geometry_Vertices_020, decode_geometry_Vertices_021, decode_geometry_Vertices_022, decode_geometry_Vertices_023]
  rfl

noncomputable def geometryVerticesTypedThroughBlock002 : List (Array ℚ) := geometryVerticesTypedThroughBlock001 ++ geometryVerticesTypedBlock002

theorem decode_geometry_Vertices_through_block_002 :
    verticesArrayAcc01200.reverse.mapM rationalArray = .ok geometryVerticesTypedThroughBlock002 := by
  change (geometryVerticesBlock002Push verticesArrayAcc00800).reverse.mapM rationalArray = _
  rw [geometry_Vertices_block_002_reverse]
  rw [List.mapM_append, decode_geometry_Vertices_through_block_001, decode_geometry_Vertices_block_002]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_block_002_complete"
  err.flush

#print axioms decode_geometry_Vertices_016
#print axioms decode_geometry_Vertices_017
#print axioms geometry_Vertices_chunk_008_push_eq
#print axioms decode_geometry_Vertices_018
#print axioms decode_geometry_Vertices_019
#print axioms geometry_Vertices_chunk_009_push_eq
#print axioms decode_geometry_Vertices_020
#print axioms decode_geometry_Vertices_021
#print axioms geometry_Vertices_chunk_010_push_eq
#print axioms decode_geometry_Vertices_022
#print axioms decode_geometry_Vertices_023
#print axioms geometry_Vertices_chunk_011_push_eq
#print axioms geometry_Vertices_block_002_push_eq
#print axioms geometry_Vertices_block_002_reverse
#print axioms decode_geometry_Vertices_block_002
#print axioms decode_geometry_Vertices_through_block_002

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
