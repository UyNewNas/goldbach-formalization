import ImbalancedChen.P2OriginalSaving19Geometry00DecodedVertexValues004
import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00500

/-! Actual original vertex_values typed block 5; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryVertexValuesJson020 : SourceJson :=
  (vertexValuesChunk020Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped020 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((1078161 : ℚ) / (13600000 : ℚ)), ((1078161 : ℚ) / (13600000 : ℚ)), ((2171847 : ℚ) / (17000000 : ℚ)), ((6890589 : ℚ) / (68000000 : ℚ)), ((255621 : ℚ) / (2720000 : ℚ)), ((2296863 : ℚ) / (34000000 : ℚ)), ((2296863 : ℚ) / (68000000 : ℚ)), ((2296863 : ℚ) / (68000000 : ℚ)), ((2296863 : ℚ) / (68000000 : ℚ)), ((359387 : ℚ) / (13600000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_020_before_decode"
  err.flush

theorem decode_geometry_VertexValues_020 :
    decodeVertexValues geometryVertexValuesJson020 = .ok geometryVertexValuesTyped020 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_020_decoded"
  err.flush

theorem geometry_VertexValues_chunk_020_push_eq (acc : List SourceJson) :
    vertexValuesChunk020Push00 acc = [geometryVertexValuesJson020] ++ acc := by rfl

noncomputable def geometryVertexValuesJson021 : SourceJson :=
  (vertexValuesChunk021Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped021 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((67257 : ℚ) / (800000 : ℚ)), ((67257 : ℚ) / (800000 : ℚ)), ((25679 : ℚ) / (200000 : ℚ)), ((401493 : ℚ) / (4000000 : ℚ)), ((379749 : ℚ) / (4000000 : ℚ)), ((133831 : ℚ) / (2000000 : ℚ)), ((133831 : ℚ) / (4000000 : ℚ)), ((133831 : ℚ) / (4000000 : ℚ)), ((22419 : ℚ) / (800000 : ℚ)), ((22419 : ℚ) / (800000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_021_before_decode"
  err.flush

theorem decode_geometry_VertexValues_021 :
    decodeVertexValues geometryVertexValuesJson021 = .ok geometryVertexValuesTyped021 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_021_decoded"
  err.flush

theorem geometry_VertexValues_chunk_021_push_eq (acc : List SourceJson) :
    vertexValuesChunk021Push00 acc = [geometryVertexValuesJson021] ++ acc := by rfl

noncomputable def geometryVertexValuesJson022 : SourceJson :=
  (vertexValuesChunk022Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped022 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((553153 : ℚ) / (7200000 : ℚ)), ((553153 : ℚ) / (7200000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((1171879 : ℚ) / (18000000 : ℚ)), ((1171879 : ℚ) / (36000000 : ℚ)), ((1171879 : ℚ) / (36000000 : ℚ)), ((234371 : ℚ) / (7200000 : ℚ)), ((234371 : ℚ) / (7200000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_022_before_decode"
  err.flush

theorem decode_geometry_VertexValues_022 :
    decodeVertexValues geometryVertexValuesJson022 = .ok geometryVertexValuesTyped022 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_022_decoded"
  err.flush

theorem geometry_VertexValues_chunk_022_push_eq (acc : List SourceJson) :
    vertexValuesChunk022Push00 acc = [geometryVertexValuesJson022] ++ acc := by rfl

noncomputable def geometryVertexValuesJson023 : SourceJson :=
  (vertexValuesChunk023Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped023 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2765741 : ℚ) / (36000000 : ℚ)), ((2765741 : ℚ) / (36000000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((1171879 : ℚ) / (18000000 : ℚ)), ((1171879 : ℚ) / (36000000 : ℚ)), ((1171879 : ℚ) / (36000000 : ℚ)), ((1171879 : ℚ) / (36000000 : ℚ)), ((234371 : ℚ) / (7200000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_023_before_decode"
  err.flush

theorem decode_geometry_VertexValues_023 :
    decodeVertexValues geometryVertexValuesJson023 = .ok geometryVertexValuesTyped023 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_record_023_decoded"
  err.flush

theorem geometry_VertexValues_chunk_023_push_eq (acc : List SourceJson) :
    vertexValuesChunk023Push00 acc = [geometryVertexValuesJson023] ++ acc := by rfl

noncomputable def geometryVertexValuesJsonBlock005 : List SourceJson := [geometryVertexValuesJson020, geometryVertexValuesJson021, geometryVertexValuesJson022, geometryVertexValuesJson023]
noncomputable def geometryVertexValuesTypedBlock005 : List (VertexValues) := [geometryVertexValuesTyped020, geometryVertexValuesTyped021, geometryVertexValuesTyped022, geometryVertexValuesTyped023]
noncomputable def geometryVertexValuesBlock005Push (acc : List SourceJson) : List SourceJson := vertexValuesChunk023Push00 (vertexValuesChunk022Push00 (vertexValuesChunk021Push00 (vertexValuesChunk020Push00 (acc))))

theorem geometry_VertexValues_block_005_push_eq (acc : List SourceJson) :
    geometryVertexValuesBlock005Push acc = [geometryVertexValuesJson023, geometryVertexValuesJson022, geometryVertexValuesJson021, geometryVertexValuesJson020] ++ acc := by rfl

theorem geometry_VertexValues_block_005_reverse (acc : List SourceJson) :
    (geometryVertexValuesBlock005Push acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock005 := by
  rw [geometry_VertexValues_block_005_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_005 :
    geometryVertexValuesJsonBlock005.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock005 := by
  simp only [geometryVertexValuesJsonBlock005, geometryVertexValuesTypedBlock005, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_020, decode_geometry_VertexValues_021, decode_geometry_VertexValues_022, decode_geometry_VertexValues_023]
  rfl

noncomputable def geometryVertexValuesTypedThroughBlock005 : List (VertexValues) := geometryVertexValuesTypedThroughBlock004 ++ geometryVertexValuesTypedBlock005

theorem decode_geometry_VertexValues_through_block_005 :
    vertexValuesArrayAcc02400.reverse.mapM decodeVertexValues = .ok geometryVertexValuesTypedThroughBlock005 := by
  change (geometryVertexValuesBlock005Push vertexValuesArrayAcc02000).reverse.mapM decodeVertexValues = _
  rw [geometry_VertexValues_block_005_reverse]
  rw [List.mapM_append, decode_geometry_VertexValues_through_block_004, decode_geometry_VertexValues_block_005]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED VertexValues_block_005_complete"
  err.flush

#print axioms decode_geometry_VertexValues_020
#print axioms geometry_VertexValues_chunk_020_push_eq
#print axioms decode_geometry_VertexValues_021
#print axioms geometry_VertexValues_chunk_021_push_eq
#print axioms decode_geometry_VertexValues_022
#print axioms geometry_VertexValues_chunk_022_push_eq
#print axioms decode_geometry_VertexValues_023
#print axioms geometry_VertexValues_chunk_023_push_eq
#print axioms geometry_VertexValues_block_005_push_eq
#print axioms geometry_VertexValues_block_005_reverse
#print axioms decode_geometry_VertexValues_block_005
#print axioms decode_geometry_VertexValues_through_block_005

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
