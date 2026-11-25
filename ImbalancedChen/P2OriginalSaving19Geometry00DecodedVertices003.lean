import ImbalancedChen.P2OriginalSaving19Geometry00DecodedVertices002
import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00300

/-! Actual original vertices typed block 3; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryVerticesJson024 : SourceJson :=
  (verticesChunk012Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped024 : Array ℚ :=
  #[((234371 : ℚ) / (1800000 : ℚ)), ((3665597 : ℚ) / (36000000 : ℚ)), ((3365581 : ℚ) / (36000000 : ℚ)), ((1171879 : ℚ) / (18000000 : ℚ)), ((146871 : ℚ) / (4000000 : ℚ)), ((1021919 : ℚ) / (36000000 : ℚ)), ((204379 : ℚ) / (7200000 : ℚ)), ((204379 : ℚ) / (7200000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_024_before_decode"
  err.flush

theorem decode_geometry_Vertices_024 :
    rationalArray geometryVerticesJson024 = .ok geometryVerticesTyped024 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_024_decoded"
  err.flush

noncomputable def geometryVerticesJson025 : SourceJson :=
  (verticesChunk012Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped025 : Array ℚ :=
  #[((234371 : ℚ) / (1800000 : ℚ)), ((18328009 : ℚ) / (180000000 : ℚ)), ((16827881 : ℚ) / (180000000 : ℚ)), ((1171879 : ℚ) / (18000000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((5109571 : ℚ) / (180000000 : ℚ)), ((5109571 : ℚ) / (180000000 : ℚ)), ((5109451 : ℚ) / (180000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_025_before_decode"
  err.flush

theorem decode_geometry_Vertices_025 :
    rationalArray geometryVerticesJson025 = .ok geometryVerticesTyped025 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_025_decoded"
  err.flush

theorem geometry_Vertices_chunk_012_push_eq (acc : List SourceJson) :
    verticesChunk012Push00 acc = [geometryVerticesJson025, geometryVerticesJson024] ++ acc := by rfl

noncomputable def geometryVerticesJson026 : SourceJson :=
  (verticesChunk013Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped026 : Array ℚ :=
  #[((571859 : ℚ) / (4200000 : ℚ)), ((8952953 : ℚ) / (84000000 : ℚ)), ((7453129 : ℚ) / (84000000 : ℚ)), ((2484451 : ℚ) / (42000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_026_before_decode"
  err.flush

theorem decode_geometry_Vertices_026 :
    rationalArray geometryVerticesJson026 = .ok geometryVerticesTyped026 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_026_decoded"
  err.flush

noncomputable def geometryVerticesJson027 : SourceJson :=
  (verticesChunk013Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped027 : Array ℚ :=
  #[((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1490621 : ℚ) / (16800000 : ℚ)), ((2484443 : ℚ) / (42000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((828129 : ℚ) / (28000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_027_before_decode"
  err.flush

theorem decode_geometry_Vertices_027 :
    rationalArray geometryVerticesJson027 = .ok geometryVerticesTyped027 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_record_027_decoded"
  err.flush

theorem geometry_Vertices_chunk_013_push_eq (acc : List SourceJson) :
    verticesChunk013Push00 acc = [geometryVerticesJson027, geometryVerticesJson026] ++ acc := by rfl

noncomputable def geometryVerticesJsonBlock003 : List SourceJson := [geometryVerticesJson024, geometryVerticesJson025, geometryVerticesJson026, geometryVerticesJson027]
noncomputable def geometryVerticesTypedBlock003 : List (Array ℚ) := [geometryVerticesTyped024, geometryVerticesTyped025, geometryVerticesTyped026, geometryVerticesTyped027]
noncomputable def geometryVerticesBlock003Push (acc : List SourceJson) : List SourceJson := verticesChunk013Push00 (verticesChunk012Push00 (acc))

theorem geometry_Vertices_block_003_push_eq (acc : List SourceJson) :
    geometryVerticesBlock003Push acc = [geometryVerticesJson027, geometryVerticesJson026, geometryVerticesJson025, geometryVerticesJson024] ++ acc := by rfl

theorem geometry_Vertices_block_003_reverse (acc : List SourceJson) :
    (geometryVerticesBlock003Push acc).reverse = acc.reverse ++ geometryVerticesJsonBlock003 := by
  rw [geometry_Vertices_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Vertices_block_003 :
    geometryVerticesJsonBlock003.mapM rationalArray = .ok geometryVerticesTypedBlock003 := by
  simp only [geometryVerticesJsonBlock003, geometryVerticesTypedBlock003, List.mapM_cons, List.mapM_nil,
    decode_geometry_Vertices_024, decode_geometry_Vertices_025, decode_geometry_Vertices_026, decode_geometry_Vertices_027]
  rfl

noncomputable def geometryVerticesTypedThroughBlock003 : List (Array ℚ) := geometryVerticesTypedThroughBlock002 ++ geometryVerticesTypedBlock003

theorem decode_geometry_Vertices_through_block_003 :
    verticesArrayAcc01400.reverse.mapM rationalArray = .ok geometryVerticesTypedThroughBlock003 := by
  change (geometryVerticesBlock003Push verticesArrayAcc01200).reverse.mapM rationalArray = _
  rw [geometry_Vertices_block_003_reverse]
  rw [List.mapM_append, decode_geometry_Vertices_through_block_002, decode_geometry_Vertices_block_003]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Vertices_block_003_complete"
  err.flush

#print axioms decode_geometry_Vertices_024
#print axioms decode_geometry_Vertices_025
#print axioms geometry_Vertices_chunk_012_push_eq
#print axioms decode_geometry_Vertices_026
#print axioms decode_geometry_Vertices_027
#print axioms geometry_Vertices_chunk_013_push_eq
#print axioms geometry_Vertices_block_003_push_eq
#print axioms geometry_Vertices_block_003_reverse
#print axioms decode_geometry_Vertices_block_003
#print axioms decode_geometry_Vertices_through_block_003

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
