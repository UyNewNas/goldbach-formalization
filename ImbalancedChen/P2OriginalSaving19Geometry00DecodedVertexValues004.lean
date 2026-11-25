import ImbalancedChen.P2OriginalSaving19Geometry00DecodedVertexValues003
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00400

/-! Actual original vertex_values typed block 4; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryVertexValuesJson016 : SourceJson :=
  (vertexValuesChunk016Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped016 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((341061 : ℚ) / (4000000 : ℚ)), ((341061 : ℚ) / (4000000 : ℚ)), ((25323 : ℚ) / (200000 : ℚ)), ((392781 : ℚ) / (4000000 : ℚ)), ((375533 : ℚ) / (4000000 : ℚ)), ((130927 : ℚ) / (2000000 : ℚ)), ((130927 : ℚ) / (4000000 : ℚ)), ((130927 : ℚ) / (4000000 : ℚ)), ((130927 : ℚ) / (4000000 : ℚ)), ((113687 : ℚ) / (4000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_016_before_decode"
  err.flush

theorem decode_geometry_VertexValues_016 :
    decodeVertexValues geometryVertexValuesJson016 = .ok geometryVertexValuesTyped016 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_016_decoded"
  err.flush

theorem geometry_VertexValues_chunk_016_push_eq (acc : List SourceJson) :
    vertexValuesChunk016Push00 acc = [geometryVertexValuesJson016] ++ acc := by rfl

noncomputable def geometryVertexValuesJson017 : SourceJson :=
  (vertexValuesChunk017Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped017 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2671843 : ℚ) / (21000000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((571871 : ℚ) / (8400000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((828129 : ℚ) / (28000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_017_before_decode"
  err.flush

theorem decode_geometry_VertexValues_017 :
    decodeVertexValues geometryVertexValuesJson017 = .ok geometryVertexValuesTyped017 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_017_decoded"
  err.flush

theorem geometry_VertexValues_chunk_017_push_eq (acc : List SourceJson) :
    vertexValuesChunk017Push00 acc = [geometryVertexValuesJson017] ++ acc := by rfl

noncomputable def geometryVertexValuesJson018 : SourceJson :=
  (vertexValuesChunk018Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped018 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((496879 : ℚ) / (5600000 : ℚ)), ((496879 : ℚ) / (5600000 : ℚ)), ((178123 : ℚ) / (1400000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((953117 : ℚ) / (14000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_018_before_decode"
  err.flush

theorem decode_geometry_VertexValues_018 :
    decodeVertexValues geometryVertexValuesJson018 = .ok geometryVertexValuesTyped018 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_018_decoded"
  err.flush

theorem geometry_VertexValues_chunk_018_push_eq (acc : List SourceJson) :
    vertexValuesChunk018Push00 acc = [geometryVertexValuesJson018] ++ acc := by rfl

noncomputable def geometryVertexValuesJson019 : SourceJson :=
  (vertexValuesChunk019Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped019 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((489381 : ℚ) / (5600000 : ℚ)), ((489381 : ℚ) / (5600000 : ℚ)), ((178123 : ℚ) / (1400000 : ℚ)), ((2746881 : ℚ) / (28000000 : ℚ)), ((378119 : ℚ) / (4000000 : ℚ)), ((915627 : ℚ) / (14000000 : ℚ)), ((915627 : ℚ) / (28000000 : ℚ)), ((915627 : ℚ) / (28000000 : ℚ)), ((163127 : ℚ) / (5600000 : ℚ)), ((163127 : ℚ) / (5600000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_019_before_decode"
  err.flush

theorem decode_geometry_VertexValues_019 :
    decodeVertexValues geometryVertexValuesJson019 = .ok geometryVertexValuesTyped019 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_019_decoded"
  err.flush

theorem geometry_VertexValues_chunk_019_push_eq (acc : List SourceJson) :
    vertexValuesChunk019Push00 acc = [geometryVertexValuesJson019] ++ acc := by rfl

noncomputable def geometryVertexValuesJsonBlock004 : List SourceJson := [geometryVertexValuesJson016, geometryVertexValuesJson017, geometryVertexValuesJson018, geometryVertexValuesJson019]
noncomputable def geometryVertexValuesTypedBlock004 : List (VertexValues) := [geometryVertexValuesTyped016, geometryVertexValuesTyped017, geometryVertexValuesTyped018, geometryVertexValuesTyped019]
noncomputable def geometryVertexValuesBlock004Push (acc : List SourceJson) : List SourceJson := vertexValuesChunk019Push00 (vertexValuesChunk018Push00 (vertexValuesChunk017Push00 (vertexValuesChunk016Push00 (acc))))

theorem geometry_VertexValues_block_004_push_eq (acc : List SourceJson) :
    geometryVertexValuesBlock004Push acc = [geometryVertexValuesJson019, geometryVertexValuesJson018, geometryVertexValuesJson017, geometryVertexValuesJson016] ++ acc := by rfl

theorem geometry_VertexValues_block_004_reverse (acc : List SourceJson) :
    (geometryVertexValuesBlock004Push acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock004 := by
  rw [geometry_VertexValues_block_004_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_004 :
    geometryVertexValuesJsonBlock004.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock004 := by
  simp only [geometryVertexValuesJsonBlock004, geometryVertexValuesTypedBlock004, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_016, decode_geometry_VertexValues_017, decode_geometry_VertexValues_018, decode_geometry_VertexValues_019]
  rfl

noncomputable def geometryVertexValuesTypedThroughBlock004 : List (VertexValues) := geometryVertexValuesTypedThroughBlock003 ++ geometryVertexValuesTypedBlock004

theorem decode_geometry_VertexValues_through_block_004 :
    vertexValuesArrayAcc02000.reverse.mapM decodeVertexValues = .ok geometryVertexValuesTypedThroughBlock004 := by
  change (geometryVertexValuesBlock004Push vertexValuesArrayAcc01600).reverse.mapM decodeVertexValues = _
  rw [geometry_VertexValues_block_004_reverse]
  rw [List.mapM_append, decode_geometry_VertexValues_through_block_003, decode_geometry_VertexValues_block_004]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_block_004_complete"
  err.flush

#print axioms decode_geometry_VertexValues_016
#print axioms geometry_VertexValues_chunk_016_push_eq
#print axioms decode_geometry_VertexValues_017
#print axioms geometry_VertexValues_chunk_017_push_eq
#print axioms decode_geometry_VertexValues_018
#print axioms geometry_VertexValues_chunk_018_push_eq
#print axioms decode_geometry_VertexValues_019
#print axioms geometry_VertexValues_chunk_019_push_eq
#print axioms geometry_VertexValues_block_004_push_eq
#print axioms geometry_VertexValues_block_004_reverse
#print axioms decode_geometry_VertexValues_block_004
#print axioms decode_geometry_VertexValues_through_block_004

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
