import ImbalancedChen.P2OriginalSaving19Geometry00DecodedVertexValues001
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00200

/-! Actual original vertex_values typed block 2; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryVertexValuesJson008 : SourceJson :=
  (vertexValuesChunk008Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped008 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((7734387 : ℚ) / (80000000 : ℚ)), ((7734387 : ℚ) / (80000000 : ℚ)), ((3515621 : ℚ) / (30000000 : ℚ)), ((20391061 : ℚ) / (240000000 : ℚ)), ((390629 : ℚ) / (5000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((2578129 : ℚ) / (80000000 : ℚ)), ((2578129 : ℚ) / (80000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_008_before_decode"
  err.flush

theorem decode_geometry_VertexValues_008 :
    decodeVertexValues geometryVertexValuesJson008 = .ok geometryVertexValuesTyped008 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_008_decoded"
  err.flush

theorem geometry_VertexValues_chunk_008_push_eq (acc : List SourceJson) :
    vertexValuesChunk008Push00 acc = [geometryVertexValuesJson008] ++ acc := by rfl

noncomputable def geometryVertexValuesJson009 : SourceJson :=
  (vertexValuesChunk009Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped009 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5390693 : ℚ) / (60000000 : ℚ)), ((5390693 : ℚ) / (60000000 : ℚ)), ((3515621 : ℚ) / (30000000 : ℚ)), ((15703393 : ℚ) / (180000000 : ℚ)), ((390629 : ℚ) / (5000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((5390693 : ℚ) / (180000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_009_before_decode"
  err.flush

theorem decode_geometry_VertexValues_009 :
    decodeVertexValues geometryVertexValuesJson009 = .ok geometryVertexValuesTyped009 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_009_decoded"
  err.flush

theorem geometry_VertexValues_chunk_009_push_eq (acc : List SourceJson) :
    vertexValuesChunk009Push00 acc = [geometryVertexValuesJson009] ++ acc := by rfl

noncomputable def geometryVertexValuesJson010 : SourceJson :=
  (vertexValuesChunk010Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped010 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5109363 : ℚ) / (52000000 : ℚ)), ((5109363 : ℚ) / (52000000 : ℚ)), ((744371 : ℚ) / (6240000 : ℚ)), ((210941 : ℚ) / (2437500 : ℚ)), ((3953193 : ℚ) / (52000000 : ℚ)), ((11859163 : ℚ) / (156000000 : ℚ)), ((26366 : ℚ) / (609375 : ℚ)), ((5109467 : ℚ) / (156000000 : ℚ)), ((1703121 : ℚ) / (52000000 : ℚ)), ((1703121 : ℚ) / (52000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_010_before_decode"
  err.flush

theorem decode_geometry_VertexValues_010 :
    decodeVertexValues geometryVertexValuesJson010 = .ok geometryVertexValuesTyped010 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_010_decoded"
  err.flush

theorem geometry_VertexValues_chunk_010_push_eq (acc : List SourceJson) :
    vertexValuesChunk010Push00 acc = [geometryVertexValuesJson010] ++ acc := by rfl

noncomputable def geometryVertexValuesJson011 : SourceJson :=
  (vertexValuesChunk011Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped011 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5109339 : ℚ) / (52000000 : ℚ)), ((5109339 : ℚ) / (52000000 : ℚ)), ((18609283 : ℚ) / (156000000 : ℚ)), ((421883 : ℚ) / (4875000 : ℚ)), ((11859571 : ℚ) / (156000000 : ℚ)), ((2371831 : ℚ) / (31200000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((5109443 : ℚ) / (156000000 : ℚ)), ((5109443 : ℚ) / (156000000 : ℚ)), ((1703113 : ℚ) / (52000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_011_before_decode"
  err.flush

theorem decode_geometry_VertexValues_011 :
    decodeVertexValues geometryVertexValuesJson011 = .ok geometryVertexValuesTyped011 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_011_decoded"
  err.flush

theorem geometry_VertexValues_chunk_011_push_eq (acc : List SourceJson) :
    vertexValuesChunk011Push00 acc = [geometryVertexValuesJson011] ++ acc := by rfl

noncomputable def geometryVertexValuesJsonBlock002 : List SourceJson := [geometryVertexValuesJson008, geometryVertexValuesJson009, geometryVertexValuesJson010, geometryVertexValuesJson011]
noncomputable def geometryVertexValuesTypedBlock002 : List (VertexValues) := [geometryVertexValuesTyped008, geometryVertexValuesTyped009, geometryVertexValuesTyped010, geometryVertexValuesTyped011]
noncomputable def geometryVertexValuesBlock002Push (acc : List SourceJson) : List SourceJson := vertexValuesChunk011Push00 (vertexValuesChunk010Push00 (vertexValuesChunk009Push00 (vertexValuesChunk008Push00 (acc))))

theorem geometry_VertexValues_block_002_push_eq (acc : List SourceJson) :
    geometryVertexValuesBlock002Push acc = [geometryVertexValuesJson011, geometryVertexValuesJson010, geometryVertexValuesJson009, geometryVertexValuesJson008] ++ acc := by rfl

theorem geometry_VertexValues_block_002_reverse (acc : List SourceJson) :
    (geometryVertexValuesBlock002Push acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock002 := by
  rw [geometry_VertexValues_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_002 :
    geometryVertexValuesJsonBlock002.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock002 := by
  simp only [geometryVertexValuesJsonBlock002, geometryVertexValuesTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_008, decode_geometry_VertexValues_009, decode_geometry_VertexValues_010, decode_geometry_VertexValues_011]
  rfl

noncomputable def geometryVertexValuesTypedThroughBlock002 : List (VertexValues) := geometryVertexValuesTypedThroughBlock001 ++ geometryVertexValuesTypedBlock002

theorem decode_geometry_VertexValues_through_block_002 :
    vertexValuesArrayAcc01200.reverse.mapM decodeVertexValues = .ok geometryVertexValuesTypedThroughBlock002 := by
  change (geometryVertexValuesBlock002Push vertexValuesArrayAcc00800).reverse.mapM decodeVertexValues = _
  rw [geometry_VertexValues_block_002_reverse]
  rw [List.mapM_append, decode_geometry_VertexValues_through_block_001, decode_geometry_VertexValues_block_002]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_block_002_complete"
  err.flush

#print axioms decode_geometry_VertexValues_008
#print axioms geometry_VertexValues_chunk_008_push_eq
#print axioms decode_geometry_VertexValues_009
#print axioms geometry_VertexValues_chunk_009_push_eq
#print axioms decode_geometry_VertexValues_010
#print axioms geometry_VertexValues_chunk_010_push_eq
#print axioms decode_geometry_VertexValues_011
#print axioms geometry_VertexValues_chunk_011_push_eq
#print axioms geometry_VertexValues_block_002_push_eq
#print axioms geometry_VertexValues_block_002_reverse
#print axioms decode_geometry_VertexValues_block_002
#print axioms decode_geometry_VertexValues_through_block_002

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
