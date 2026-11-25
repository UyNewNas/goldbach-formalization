import ImbalancedChen.P2OriginalSaving19Geometry00DecodedVertexValues005
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00600

/-! Actual original vertex_values typed block 6; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryVertexValuesJson024 : SourceJson :=
  (vertexValuesChunk024Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped024 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((204379 : ℚ) / (2400000 : ℚ)), ((204379 : ℚ) / (2400000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3665597 : ℚ) / (36000000 : ℚ)), ((3365581 : ℚ) / (36000000 : ℚ)), ((1171879 : ℚ) / (18000000 : ℚ)), ((146871 : ℚ) / (4000000 : ℚ)), ((1021919 : ℚ) / (36000000 : ℚ)), ((204379 : ℚ) / (7200000 : ℚ)), ((204379 : ℚ) / (7200000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_024_before_decode"
  err.flush

theorem decode_geometry_VertexValues_024 :
    decodeVertexValues geometryVertexValuesJson024 = .ok geometryVertexValuesTyped024 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_024_decoded"
  err.flush

theorem geometry_VertexValues_chunk_024_push_eq (acc : List SourceJson) :
    vertexValuesChunk024Push00 acc = [geometryVertexValuesJson024] ++ acc := by rfl

noncomputable def geometryVertexValuesJson025 : SourceJson :=
  (vertexValuesChunk025Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped025 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5109451 : ℚ) / (60000000 : ℚ)), ((5109451 : ℚ) / (60000000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((18328009 : ℚ) / (180000000 : ℚ)), ((16827881 : ℚ) / (180000000 : ℚ)), ((1171879 : ℚ) / (18000000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((5109571 : ℚ) / (180000000 : ℚ)), ((5109571 : ℚ) / (180000000 : ℚ)), ((5109451 : ℚ) / (180000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_025_before_decode"
  err.flush

theorem decode_geometry_VertexValues_025 :
    decodeVertexValues geometryVertexValuesJson025 = .ok geometryVertexValuesTyped025 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_025_decoded"
  err.flush

theorem geometry_VertexValues_chunk_025_push_eq (acc : List SourceJson) :
    vertexValuesChunk025Push00 acc = [geometryVertexValuesJson025] ++ acc := by rfl

noncomputable def geometryVertexValuesJson026 : SourceJson :=
  (vertexValuesChunk026Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped026 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((496879 : ℚ) / (5600000 : ℚ)), ((496879 : ℚ) / (5600000 : ℚ)), ((571859 : ℚ) / (4200000 : ℚ)), ((8952953 : ℚ) / (84000000 : ℚ)), ((7453129 : ℚ) / (84000000 : ℚ)), ((2484451 : ℚ) / (42000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_026_before_decode"
  err.flush

theorem decode_geometry_VertexValues_026 :
    decodeVertexValues geometryVertexValuesJson026 = .ok geometryVertexValuesTyped026 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_026_decoded"
  err.flush

theorem geometry_VertexValues_chunk_026_push_eq (acc : List SourceJson) :
    vertexValuesChunk026Push00 acc = [geometryVertexValuesJson026] ++ acc := by rfl

noncomputable def geometryVertexValuesJson027 : SourceJson :=
  (vertexValuesChunk027Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped027 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1490621 : ℚ) / (16800000 : ℚ)), ((2484443 : ℚ) / (42000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((828129 : ℚ) / (28000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_027_before_decode"
  err.flush

theorem decode_geometry_VertexValues_027 :
    decodeVertexValues geometryVertexValuesJson027 = .ok geometryVertexValuesTyped027 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_027_decoded"
  err.flush

theorem geometry_VertexValues_chunk_027_push_eq (acc : List SourceJson) :
    vertexValuesChunk027Push00 acc = [geometryVertexValuesJson027] ++ acc := by rfl

noncomputable def geometryVertexValuesJsonBlock006 : List SourceJson := [geometryVertexValuesJson024, geometryVertexValuesJson025, geometryVertexValuesJson026, geometryVertexValuesJson027]
noncomputable def geometryVertexValuesTypedBlock006 : List (VertexValues) := [geometryVertexValuesTyped024, geometryVertexValuesTyped025, geometryVertexValuesTyped026, geometryVertexValuesTyped027]
noncomputable def geometryVertexValuesBlock006Push (acc : List SourceJson) : List SourceJson := vertexValuesChunk027Push00 (vertexValuesChunk026Push00 (vertexValuesChunk025Push00 (vertexValuesChunk024Push00 (acc))))

theorem geometry_VertexValues_block_006_push_eq (acc : List SourceJson) :
    geometryVertexValuesBlock006Push acc = [geometryVertexValuesJson027, geometryVertexValuesJson026, geometryVertexValuesJson025, geometryVertexValuesJson024] ++ acc := by rfl

theorem geometry_VertexValues_block_006_reverse (acc : List SourceJson) :
    (geometryVertexValuesBlock006Push acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock006 := by
  rw [geometry_VertexValues_block_006_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_006 :
    geometryVertexValuesJsonBlock006.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock006 := by
  simp only [geometryVertexValuesJsonBlock006, geometryVertexValuesTypedBlock006, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_024, decode_geometry_VertexValues_025, decode_geometry_VertexValues_026, decode_geometry_VertexValues_027]
  rfl

noncomputable def geometryVertexValuesTypedThroughBlock006 : List (VertexValues) := geometryVertexValuesTypedThroughBlock005 ++ geometryVertexValuesTypedBlock006

theorem decode_geometry_VertexValues_through_block_006 :
    vertexValuesArrayAcc02800.reverse.mapM decodeVertexValues = .ok geometryVertexValuesTypedThroughBlock006 := by
  change (geometryVertexValuesBlock006Push vertexValuesArrayAcc02400).reverse.mapM decodeVertexValues = _
  rw [geometry_VertexValues_block_006_reverse]
  rw [List.mapM_append, decode_geometry_VertexValues_through_block_005, decode_geometry_VertexValues_block_006]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_block_006_complete"
  err.flush

#print axioms decode_geometry_VertexValues_024
#print axioms geometry_VertexValues_chunk_024_push_eq
#print axioms decode_geometry_VertexValues_025
#print axioms geometry_VertexValues_chunk_025_push_eq
#print axioms decode_geometry_VertexValues_026
#print axioms geometry_VertexValues_chunk_026_push_eq
#print axioms decode_geometry_VertexValues_027
#print axioms geometry_VertexValues_chunk_027_push_eq
#print axioms geometry_VertexValues_block_006_push_eq
#print axioms geometry_VertexValues_block_006_reverse
#print axioms decode_geometry_VertexValues_block_006
#print axioms decode_geometry_VertexValues_through_block_006

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
