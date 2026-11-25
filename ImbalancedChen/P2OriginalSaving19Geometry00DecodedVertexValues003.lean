import ImbalancedChen.P2OriginalSaving19Geometry00DecodedVertexValues002
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00300

/-! Actual original vertex_values typed block 3; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryVertexValuesJson012 : SourceJson :=
  (vertexValuesChunk012Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped012 : VertexValues :=
  { gap := ((2929 : ℚ) / (828125 : ℚ)),
    factors := #[((18703241 : ℚ) / (212000000 : ℚ)), ((3890613 : ℚ) / (42400000 : ℚ)), ((1296871 : ℚ) / (10600000 : ℚ)), ((20953137 : ℚ) / (212000000 : ℚ)), ((18953041 : ℚ) / (212000000 : ℚ)), ((6984379 : ℚ) / (106000000 : ℚ)), ((6984379 : ℚ) / (212000000 : ℚ)), ((6984379 : ℚ) / (212000000 : ℚ)), ((6984379 : ℚ) / (212000000 : ℚ)), ((1296871 : ℚ) / (42400000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_012_before_decode"
  err.flush

theorem decode_geometry_VertexValues_012 :
    decodeVertexValues geometryVertexValuesJson012 = .ok geometryVertexValuesTyped012 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_012_decoded"
  err.flush

theorem geometry_VertexValues_chunk_012_push_eq (acc : List SourceJson) :
    vertexValuesChunk012Push00 acc = [geometryVertexValuesJson012] ++ acc := by rfl

noncomputable def geometryVertexValuesJson013 : SourceJson :=
  (vertexValuesChunk013Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped013 : VertexValues :=
  { gap := ((3749 : ℚ) / (1180000 : ℚ)),
    factors := #[((4209403 : ℚ) / (47200000 : ℚ)), ((4359363 : ℚ) / (47200000 : ℚ)), ((1453121 : ℚ) / (11800000 : ℚ)), ((23296887 : ℚ) / (236000000 : ℚ)), ((21296791 : ℚ) / (236000000 : ℚ)), ((7765629 : ℚ) / (118000000 : ℚ)), ((7765629 : ℚ) / (236000000 : ℚ)), ((7765629 : ℚ) / (236000000 : ℚ)), ((1453121 : ℚ) / (47200000 : ℚ)), ((1453121 : ℚ) / (47200000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_013_before_decode"
  err.flush

theorem decode_geometry_VertexValues_013 :
    decodeVertexValues geometryVertexValuesJson013 = .ok geometryVertexValuesTyped013 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_013_decoded"
  err.flush

theorem geometry_VertexValues_chunk_013_push_eq (acc : List SourceJson) :
    vertexValuesChunk013Push00 acc = [geometryVertexValuesJson013] ++ acc := by rfl

noncomputable def geometryVertexValuesJson014 : SourceJson :=
  (vertexValuesChunk014Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped014 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((505199 : ℚ) / (4000000 : ℚ)), ((2203129 : ℚ) / (24000000 : ℚ)), ((828161 : ℚ) / (12000000 : ℚ)), ((276043 : ℚ) / (4000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_014_before_decode"
  err.flush

theorem decode_geometry_VertexValues_014 :
    decodeVertexValues geometryVertexValuesJson014 = .ok geometryVertexValuesTyped014 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_014_decoded"
  err.flush

theorem geometry_VertexValues_chunk_014_push_eq (acc : List SourceJson) :
    vertexValuesChunk014Push00 acc = [geometryVertexValuesJson014] ++ acc := by rfl

noncomputable def geometryVertexValuesJson015 : SourceJson :=
  (vertexValuesChunk015Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped015 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((4546799 : ℚ) / (36000000 : ℚ)), ((734379 : ℚ) / (8000000 : ℚ)), ((99379 : ℚ) / (1440000 : ℚ)), ((2484379 : ℚ) / (36000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_015_before_decode"
  err.flush

theorem decode_geometry_VertexValues_015 :
    decodeVertexValues geometryVertexValuesJson015 = .ok geometryVertexValuesTyped015 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_015_decoded"
  err.flush

theorem geometry_VertexValues_chunk_015_push_eq (acc : List SourceJson) :
    vertexValuesChunk015Push00 acc = [geometryVertexValuesJson015] ++ acc := by rfl

noncomputable def geometryVertexValuesJsonBlock003 : List SourceJson := [geometryVertexValuesJson012, geometryVertexValuesJson013, geometryVertexValuesJson014, geometryVertexValuesJson015]
noncomputable def geometryVertexValuesTypedBlock003 : List (VertexValues) := [geometryVertexValuesTyped012, geometryVertexValuesTyped013, geometryVertexValuesTyped014, geometryVertexValuesTyped015]
noncomputable def geometryVertexValuesBlock003Push (acc : List SourceJson) : List SourceJson := vertexValuesChunk015Push00 (vertexValuesChunk014Push00 (vertexValuesChunk013Push00 (vertexValuesChunk012Push00 (acc))))

theorem geometry_VertexValues_block_003_push_eq (acc : List SourceJson) :
    geometryVertexValuesBlock003Push acc = [geometryVertexValuesJson015, geometryVertexValuesJson014, geometryVertexValuesJson013, geometryVertexValuesJson012] ++ acc := by rfl

theorem geometry_VertexValues_block_003_reverse (acc : List SourceJson) :
    (geometryVertexValuesBlock003Push acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock003 := by
  rw [geometry_VertexValues_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_003 :
    geometryVertexValuesJsonBlock003.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock003 := by
  simp only [geometryVertexValuesJsonBlock003, geometryVertexValuesTypedBlock003, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_012, decode_geometry_VertexValues_013, decode_geometry_VertexValues_014, decode_geometry_VertexValues_015]
  rfl

noncomputable def geometryVertexValuesTypedThroughBlock003 : List (VertexValues) := geometryVertexValuesTypedThroughBlock002 ++ geometryVertexValuesTypedBlock003

theorem decode_geometry_VertexValues_through_block_003 :
    vertexValuesArrayAcc01600.reverse.mapM decodeVertexValues = .ok geometryVertexValuesTypedThroughBlock003 := by
  change (geometryVertexValuesBlock003Push vertexValuesArrayAcc01200).reverse.mapM decodeVertexValues = _
  rw [geometry_VertexValues_block_003_reverse]
  rw [List.mapM_append, decode_geometry_VertexValues_through_block_002, decode_geometry_VertexValues_block_003]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_block_003_complete"
  err.flush

#print axioms decode_geometry_VertexValues_012
#print axioms geometry_VertexValues_chunk_012_push_eq
#print axioms decode_geometry_VertexValues_013
#print axioms geometry_VertexValues_chunk_013_push_eq
#print axioms decode_geometry_VertexValues_014
#print axioms geometry_VertexValues_chunk_014_push_eq
#print axioms decode_geometry_VertexValues_015
#print axioms geometry_VertexValues_chunk_015_push_eq
#print axioms geometry_VertexValues_block_003_push_eq
#print axioms geometry_VertexValues_block_003_reverse
#print axioms decode_geometry_VertexValues_block_003
#print axioms decode_geometry_VertexValues_through_block_003

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
