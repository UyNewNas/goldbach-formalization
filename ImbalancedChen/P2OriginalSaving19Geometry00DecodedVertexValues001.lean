import ImbalancedChen.P2OriginalSaving19Geometry00DecodedVertexValues000
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00100

/-! Actual original vertex_values typed block 1; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryVertexValuesJson004 : SourceJson :=
  (vertexValuesChunk004Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped004 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((10031229 : ℚ) / (104500000 : ℚ)), ((10031229 : ℚ) / (104500000 : ℚ)), ((6109371 : ℚ) / (52250000 : ℚ)), ((1109401 : ℚ) / (13062500 : ℚ)), ((8328173 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (52250000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3343743 : ℚ) / (104500000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_004_before_decode"
  err.flush

theorem decode_geometry_VertexValues_004 :
    decodeVertexValues geometryVertexValuesJson004 = .ok geometryVertexValuesTyped004 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_004_decoded"
  err.flush

theorem geometry_VertexValues_chunk_004_push_eq (acc : List SourceJson) :
    vertexValuesChunk004Push00 acc = [geometryVertexValuesJson004] ++ acc := by rfl

noncomputable def geometryVertexValuesJson005 : SourceJson :=
  (vertexValuesChunk005Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped005 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((4124979 : ℚ) / (41500000 : ℚ)), ((4124979 : ℚ) / (41500000 : ℚ)), ((1456249 : ℚ) / (12450000 : ℚ)), ((65236 : ℚ) / (778125 : ℚ)), ((659379 : ℚ) / (8300000 : ℚ)), ((934361 : ℚ) / (12450000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((1374993 : ℚ) / (41500000 : ℚ)), ((1374993 : ℚ) / (41500000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_005_before_decode"
  err.flush

theorem decode_geometry_VertexValues_005 :
    decodeVertexValues geometryVertexValuesJson005 = .ok geometryVertexValuesTyped005 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_005_decoded"
  err.flush

theorem geometry_VertexValues_chunk_005_push_eq (acc : List SourceJson) :
    vertexValuesChunk005Push00 acc = [geometryVertexValuesJson005] ++ acc := by rfl

noncomputable def geometryVertexValuesJson006 : SourceJson :=
  (vertexValuesChunk006Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped006 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((1796911 : ℚ) / (20000000 : ℚ)), ((1796911 : ℚ) / (20000000 : ℚ)), ((3515621 : ℚ) / (30000000 : ℚ)), ((1171927 : ℚ) / (15000000 : ℚ)), ((390629 : ℚ) / (5000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_006_before_decode"
  err.flush

theorem decode_geometry_VertexValues_006 :
    decodeVertexValues geometryVertexValuesJson006 = .ok geometryVertexValuesTyped006 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_006_decoded"
  err.flush

theorem geometry_VertexValues_chunk_006_push_eq (acc : List SourceJson) :
    vertexValuesChunk006Push00 acc = [geometryVertexValuesJson006] ++ acc := by rfl

noncomputable def geometryVertexValuesJson007 : SourceJson :=
  (vertexValuesChunk007Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped007 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5390693 : ℚ) / (60000000 : ℚ)), ((5390693 : ℚ) / (60000000 : ℚ)), ((3515621 : ℚ) / (30000000 : ℚ)), ((1171927 : ℚ) / (15000000 : ℚ)), ((390629 : ℚ) / (5000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_007_before_decode"
  err.flush

theorem decode_geometry_VertexValues_007 :
    decodeVertexValues geometryVertexValuesJson007 = .ok geometryVertexValuesTyped007 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_007_decoded"
  err.flush

theorem geometry_VertexValues_chunk_007_push_eq (acc : List SourceJson) :
    vertexValuesChunk007Push00 acc = [geometryVertexValuesJson007] ++ acc := by rfl

noncomputable def geometryVertexValuesJsonBlock001 : List SourceJson := [geometryVertexValuesJson004, geometryVertexValuesJson005, geometryVertexValuesJson006, geometryVertexValuesJson007]
noncomputable def geometryVertexValuesTypedBlock001 : List (VertexValues) := [geometryVertexValuesTyped004, geometryVertexValuesTyped005, geometryVertexValuesTyped006, geometryVertexValuesTyped007]
noncomputable def geometryVertexValuesBlock001Push (acc : List SourceJson) : List SourceJson := vertexValuesChunk007Push00 (vertexValuesChunk006Push00 (vertexValuesChunk005Push00 (vertexValuesChunk004Push00 (acc))))

theorem geometry_VertexValues_block_001_push_eq (acc : List SourceJson) :
    geometryVertexValuesBlock001Push acc = [geometryVertexValuesJson007, geometryVertexValuesJson006, geometryVertexValuesJson005, geometryVertexValuesJson004] ++ acc := by rfl

theorem geometry_VertexValues_block_001_reverse (acc : List SourceJson) :
    (geometryVertexValuesBlock001Push acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock001 := by
  rw [geometry_VertexValues_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_001 :
    geometryVertexValuesJsonBlock001.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock001 := by
  simp only [geometryVertexValuesJsonBlock001, geometryVertexValuesTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_004, decode_geometry_VertexValues_005, decode_geometry_VertexValues_006, decode_geometry_VertexValues_007]
  rfl

noncomputable def geometryVertexValuesTypedThroughBlock001 : List (VertexValues) := geometryVertexValuesTypedThroughBlock000 ++ geometryVertexValuesTypedBlock001

theorem decode_geometry_VertexValues_through_block_001 :
    vertexValuesArrayAcc00800.reverse.mapM decodeVertexValues = .ok geometryVertexValuesTypedThroughBlock001 := by
  change (geometryVertexValuesBlock001Push vertexValuesArrayAcc00400).reverse.mapM decodeVertexValues = _
  rw [geometry_VertexValues_block_001_reverse]
  rw [List.mapM_append, decode_geometry_VertexValues_through_block_000, decode_geometry_VertexValues_block_001]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_block_001_complete"
  err.flush

#print axioms decode_geometry_VertexValues_004
#print axioms geometry_VertexValues_chunk_004_push_eq
#print axioms decode_geometry_VertexValues_005
#print axioms geometry_VertexValues_chunk_005_push_eq
#print axioms decode_geometry_VertexValues_006
#print axioms geometry_VertexValues_chunk_006_push_eq
#print axioms decode_geometry_VertexValues_007
#print axioms geometry_VertexValues_chunk_007_push_eq
#print axioms geometry_VertexValues_block_001_push_eq
#print axioms geometry_VertexValues_block_001_reverse
#print axioms decode_geometry_VertexValues_block_001
#print axioms decode_geometry_VertexValues_through_block_001

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
