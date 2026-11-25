import ImbalancedChen.P2OriginalSaving19ArchiveSchema
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00000

/-! Actual original vertex_values typed block 0; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryVertexValuesJson000 : SourceJson :=
  (vertexValuesChunk000Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped000 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((16546927 : ℚ) / (144000000 : ℚ)), ((11578553 : ℚ) / (144000000 : ℚ)), ((11578169 : ℚ) / (144000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_000_before_decode"
  err.flush

theorem decode_geometry_VertexValues_000 :
    decodeVertexValues geometryVertexValuesJson000 = .ok geometryVertexValuesTyped000 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_000_decoded"
  err.flush

theorem geometry_VertexValues_chunk_000_push_eq (acc : List SourceJson) :
    vertexValuesChunk000Push00 acc = [geometryVertexValuesJson000] ++ acc := by rfl

noncomputable def geometryVertexValuesJson001 : SourceJson :=
  (vertexValuesChunk001Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped001 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1103129 : ℚ) / (9600000 : ℚ)), ((257301 : ℚ) / (3200000 : ℚ)), ((3859387 : ℚ) / (48000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_001_before_decode"
  err.flush

theorem decode_geometry_VertexValues_001 :
    decodeVertexValues geometryVertexValuesJson001 = .ok geometryVertexValuesTyped001 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_001_decoded"
  err.flush

theorem geometry_VertexValues_chunk_001_push_eq (acc : List SourceJson) :
    vertexValuesChunk001Push00 acc = [geometryVertexValuesJson001] ++ acc := by rfl

noncomputable def geometryVertexValuesJson002 : SourceJson :=
  (vertexValuesChunk002Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped002 : VertexValues :=
  { gap := ((1640269 : ℚ) / (416000000 : ℚ)),
    factors := #[((39234443 : ℚ) / (416000000 : ℚ)), ((5109339 : ℚ) / (52000000 : ℚ)), ((24265621 : ℚ) / (208000000 : ℚ)), ((734379 : ℚ) / (8000000 : ℚ)), ((8453137 : ℚ) / (104000000 : ℚ)), ((7359347 : ℚ) / (104000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((1703113 : ℚ) / (52000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_002_before_decode"
  err.flush

theorem decode_geometry_VertexValues_002 :
    decodeVertexValues geometryVertexValuesJson002 = .ok geometryVertexValuesTyped002 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_002_decoded"
  err.flush

theorem geometry_VertexValues_chunk_002_push_eq (acc : List SourceJson) :
    vertexValuesChunk002Push00 acc = [geometryVertexValuesJson002] ++ acc := by rfl

noncomputable def geometryVertexValuesJson003 : SourceJson :=
  (vertexValuesChunk003Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped003 : VertexValues :=
  { gap := ((546743 : ℚ) / (152000000 : ℚ)),
    factors := #[((14640661 : ℚ) / (152000000 : ℚ)), ((3796851 : ℚ) / (38000000 : ℚ)), ((26609371 : ℚ) / (228000000 : ℚ)), ((10328177 : ℚ) / (114000000 : ℚ)), ((3078129 : ℚ) / (38000000 : ℚ)), ((8140597 : ℚ) / (114000000 : ℚ)), ((8140597 : ℚ) / (228000000 : ℚ)), ((8140597 : ℚ) / (228000000 : ℚ)), ((1265617 : ℚ) / (38000000 : ℚ)), ((1265617 : ℚ) / (38000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_003_before_decode"
  err.flush

theorem decode_geometry_VertexValues_003 :
    decodeVertexValues geometryVertexValuesJson003 = .ok geometryVertexValuesTyped003 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_003_decoded"
  err.flush

theorem geometry_VertexValues_chunk_003_push_eq (acc : List SourceJson) :
    vertexValuesChunk003Push00 acc = [geometryVertexValuesJson003] ++ acc := by rfl

noncomputable def geometryVertexValuesJsonBlock000 : List SourceJson := [geometryVertexValuesJson000, geometryVertexValuesJson001, geometryVertexValuesJson002, geometryVertexValuesJson003]
noncomputable def geometryVertexValuesTypedBlock000 : List (VertexValues) := [geometryVertexValuesTyped000, geometryVertexValuesTyped001, geometryVertexValuesTyped002, geometryVertexValuesTyped003]
noncomputable def geometryVertexValuesBlock000Push (acc : List SourceJson) : List SourceJson := vertexValuesChunk003Push00 (vertexValuesChunk002Push00 (vertexValuesChunk001Push00 (vertexValuesChunk000Push00 (acc))))

theorem geometry_VertexValues_block_000_push_eq (acc : List SourceJson) :
    geometryVertexValuesBlock000Push acc = [geometryVertexValuesJson003, geometryVertexValuesJson002, geometryVertexValuesJson001, geometryVertexValuesJson000] ++ acc := by rfl

theorem geometry_VertexValues_block_000_reverse (acc : List SourceJson) :
    (geometryVertexValuesBlock000Push acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock000 := by
  rw [geometry_VertexValues_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_000 :
    geometryVertexValuesJsonBlock000.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock000 := by
  simp only [geometryVertexValuesJsonBlock000, geometryVertexValuesTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_000, decode_geometry_VertexValues_001, decode_geometry_VertexValues_002, decode_geometry_VertexValues_003]
  rfl

noncomputable def geometryVertexValuesTypedThroughBlock000 : List (VertexValues) := geometryVertexValuesTypedBlock000

theorem decode_geometry_VertexValues_through_block_000 :
    vertexValuesArrayAcc00400.reverse.mapM decodeVertexValues = .ok geometryVertexValuesTypedThroughBlock000 := by
  change (geometryVertexValuesBlock000Push vertexValuesArrayAcc00000).reverse.mapM decodeVertexValues = _
  rw [geometry_VertexValues_block_000_reverse]
  exact decode_geometry_VertexValues_block_000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_block_000_complete"
  err.flush

#print axioms decode_geometry_VertexValues_000
#print axioms geometry_VertexValues_chunk_000_push_eq
#print axioms decode_geometry_VertexValues_001
#print axioms geometry_VertexValues_chunk_001_push_eq
#print axioms decode_geometry_VertexValues_002
#print axioms geometry_VertexValues_chunk_002_push_eq
#print axioms decode_geometry_VertexValues_003
#print axioms geometry_VertexValues_chunk_003_push_eq
#print axioms geometry_VertexValues_block_000_push_eq
#print axioms geometry_VertexValues_block_000_reverse
#print axioms decode_geometry_VertexValues_block_000
#print axioms decode_geometry_VertexValues_through_block_000

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
