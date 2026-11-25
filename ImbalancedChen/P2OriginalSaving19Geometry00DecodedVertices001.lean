import ImbalancedChen.P2OriginalSaving19Geometry00DecodedVertices000
import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00100

/-! Actual original vertices typed block 1; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryVerticesJson008 : SourceJson :=
  (verticesChunk004Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped008 : Array ℚ :=
  #[((3515621 : ℚ) / (30000000 : ℚ)), ((20391061 : ℚ) / (240000000 : ℚ)), ((390629 : ℚ) / (5000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((2578129 : ℚ) / (80000000 : ℚ)), ((2578129 : ℚ) / (80000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_008_before_decode"
  err.flush

theorem decode_geometry_Vertices_008 :
    rationalArray geometryVerticesJson008 = .ok geometryVerticesTyped008 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_008_decoded"
  err.flush

noncomputable def geometryVerticesJson009 : SourceJson :=
  (verticesChunk004Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped009 : Array ℚ :=
  #[((3515621 : ℚ) / (30000000 : ℚ)), ((15703393 : ℚ) / (180000000 : ℚ)), ((390629 : ℚ) / (5000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((5390693 : ℚ) / (180000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_009_before_decode"
  err.flush

theorem decode_geometry_Vertices_009 :
    rationalArray geometryVerticesJson009 = .ok geometryVerticesTyped009 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_009_decoded"
  err.flush

theorem geometry_Vertices_chunk_004_push_eq (acc : List SourceJson) :
    verticesChunk004Push00 acc = [geometryVerticesJson009, geometryVerticesJson008] ++ acc := by rfl

noncomputable def geometryVerticesJson010 : SourceJson :=
  (verticesChunk005Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped010 : Array ℚ :=
  #[((744371 : ℚ) / (6240000 : ℚ)), ((210941 : ℚ) / (2437500 : ℚ)), ((3953193 : ℚ) / (52000000 : ℚ)), ((11859163 : ℚ) / (156000000 : ℚ)), ((26366 : ℚ) / (609375 : ℚ)), ((5109467 : ℚ) / (156000000 : ℚ)), ((1703121 : ℚ) / (52000000 : ℚ)), ((1703121 : ℚ) / (52000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_010_before_decode"
  err.flush

theorem decode_geometry_Vertices_010 :
    rationalArray geometryVerticesJson010 = .ok geometryVerticesTyped010 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_010_decoded"
  err.flush

noncomputable def geometryVerticesJson011 : SourceJson :=
  (verticesChunk005Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped011 : Array ℚ :=
  #[((18609283 : ℚ) / (156000000 : ℚ)), ((421883 : ℚ) / (4875000 : ℚ)), ((11859571 : ℚ) / (156000000 : ℚ)), ((2371831 : ℚ) / (31200000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((5109443 : ℚ) / (156000000 : ℚ)), ((5109443 : ℚ) / (156000000 : ℚ)), ((1703113 : ℚ) / (52000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_011_before_decode"
  err.flush

theorem decode_geometry_Vertices_011 :
    rationalArray geometryVerticesJson011 = .ok geometryVerticesTyped011 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_011_decoded"
  err.flush

theorem geometry_Vertices_chunk_005_push_eq (acc : List SourceJson) :
    verticesChunk005Push00 acc = [geometryVerticesJson011, geometryVerticesJson010] ++ acc := by rfl

noncomputable def geometryVerticesJson012 : SourceJson :=
  (verticesChunk006Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped012 : Array ℚ :=
  #[((1296871 : ℚ) / (10600000 : ℚ)), ((20953137 : ℚ) / (212000000 : ℚ)), ((18953041 : ℚ) / (212000000 : ℚ)), ((6984379 : ℚ) / (106000000 : ℚ)), ((6984379 : ℚ) / (212000000 : ℚ)), ((6984379 : ℚ) / (212000000 : ℚ)), ((6984379 : ℚ) / (212000000 : ℚ)), ((1296871 : ℚ) / (42400000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_012_before_decode"
  err.flush

theorem decode_geometry_Vertices_012 :
    rationalArray geometryVerticesJson012 = .ok geometryVerticesTyped012 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_012_decoded"
  err.flush

noncomputable def geometryVerticesJson013 : SourceJson :=
  (verticesChunk006Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped013 : Array ℚ :=
  #[((1453121 : ℚ) / (11800000 : ℚ)), ((23296887 : ℚ) / (236000000 : ℚ)), ((21296791 : ℚ) / (236000000 : ℚ)), ((7765629 : ℚ) / (118000000 : ℚ)), ((7765629 : ℚ) / (236000000 : ℚ)), ((7765629 : ℚ) / (236000000 : ℚ)), ((1453121 : ℚ) / (47200000 : ℚ)), ((1453121 : ℚ) / (47200000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_013_before_decode"
  err.flush

theorem decode_geometry_Vertices_013 :
    rationalArray geometryVerticesJson013 = .ok geometryVerticesTyped013 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_013_decoded"
  err.flush

theorem geometry_Vertices_chunk_006_push_eq (acc : List SourceJson) :
    verticesChunk006Push00 acc = [geometryVerticesJson013, geometryVerticesJson012] ++ acc := by rfl

noncomputable def geometryVerticesJson014 : SourceJson :=
  (verticesChunk007Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped014 : Array ℚ :=
  #[((505199 : ℚ) / (4000000 : ℚ)), ((2203129 : ℚ) / (24000000 : ℚ)), ((828161 : ℚ) / (12000000 : ℚ)), ((276043 : ℚ) / (4000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_014_before_decode"
  err.flush

theorem decode_geometry_Vertices_014 :
    rationalArray geometryVerticesJson014 = .ok geometryVerticesTyped014 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_014_decoded"
  err.flush

noncomputable def geometryVerticesJson015 : SourceJson :=
  (verticesChunk007Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped015 : Array ℚ :=
  #[((4546799 : ℚ) / (36000000 : ℚ)), ((734379 : ℚ) / (8000000 : ℚ)), ((99379 : ℚ) / (1440000 : ℚ)), ((2484379 : ℚ) / (36000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_015_before_decode"
  err.flush

theorem decode_geometry_Vertices_015 :
    rationalArray geometryVerticesJson015 = .ok geometryVerticesTyped015 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_015_decoded"
  err.flush

theorem geometry_Vertices_chunk_007_push_eq (acc : List SourceJson) :
    verticesChunk007Push00 acc = [geometryVerticesJson015, geometryVerticesJson014] ++ acc := by rfl

noncomputable def geometryVerticesJsonBlock001 : List SourceJson := [geometryVerticesJson008, geometryVerticesJson009, geometryVerticesJson010, geometryVerticesJson011, geometryVerticesJson012, geometryVerticesJson013, geometryVerticesJson014, geometryVerticesJson015]
noncomputable def geometryVerticesTypedBlock001 : List (Array ℚ) := [geometryVerticesTyped008, geometryVerticesTyped009, geometryVerticesTyped010, geometryVerticesTyped011, geometryVerticesTyped012, geometryVerticesTyped013, geometryVerticesTyped014, geometryVerticesTyped015]
noncomputable def geometryVerticesBlock001Push (acc : List SourceJson) : List SourceJson := verticesChunk007Push00 (verticesChunk006Push00 (verticesChunk005Push00 (verticesChunk004Push00 (acc))))

theorem geometry_Vertices_block_001_push_eq (acc : List SourceJson) :
    geometryVerticesBlock001Push acc = [geometryVerticesJson015, geometryVerticesJson014, geometryVerticesJson013, geometryVerticesJson012, geometryVerticesJson011, geometryVerticesJson010, geometryVerticesJson009, geometryVerticesJson008] ++ acc := by rfl

theorem geometry_Vertices_block_001_reverse (acc : List SourceJson) :
    (geometryVerticesBlock001Push acc).reverse = acc.reverse ++ geometryVerticesJsonBlock001 := by
  rw [geometry_Vertices_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Vertices_block_001 :
    geometryVerticesJsonBlock001.mapM rationalArray = .ok geometryVerticesTypedBlock001 := by
  simp only [geometryVerticesJsonBlock001, geometryVerticesTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_Vertices_008, decode_geometry_Vertices_009, decode_geometry_Vertices_010, decode_geometry_Vertices_011, decode_geometry_Vertices_012, decode_geometry_Vertices_013, decode_geometry_Vertices_014, decode_geometry_Vertices_015]
  rfl

noncomputable def geometryVerticesTypedThroughBlock001 : List (Array ℚ) := geometryVerticesTypedThroughBlock000 ++ geometryVerticesTypedBlock001

theorem decode_geometry_Vertices_through_block_001 :
    verticesArrayAcc00800.reverse.mapM rationalArray = .ok geometryVerticesTypedThroughBlock001 := by
  change (geometryVerticesBlock001Push verticesArrayAcc00400).reverse.mapM rationalArray = _
  rw [geometry_Vertices_block_001_reverse]
  rw [List.mapM_append, decode_geometry_Vertices_through_block_000, decode_geometry_Vertices_block_001]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_block_001_complete"
  err.flush

#print axioms decode_geometry_Vertices_008
#print axioms decode_geometry_Vertices_009
#print axioms geometry_Vertices_chunk_004_push_eq
#print axioms decode_geometry_Vertices_010
#print axioms decode_geometry_Vertices_011
#print axioms geometry_Vertices_chunk_005_push_eq
#print axioms decode_geometry_Vertices_012
#print axioms decode_geometry_Vertices_013
#print axioms geometry_Vertices_chunk_006_push_eq
#print axioms decode_geometry_Vertices_014
#print axioms decode_geometry_Vertices_015
#print axioms geometry_Vertices_chunk_007_push_eq
#print axioms geometry_Vertices_block_001_push_eq
#print axioms geometry_Vertices_block_001_reverse
#print axioms decode_geometry_Vertices_block_001
#print axioms decode_geometry_Vertices_through_block_001

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
