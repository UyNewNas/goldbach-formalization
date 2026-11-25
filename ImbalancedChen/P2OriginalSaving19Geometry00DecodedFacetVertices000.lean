import ImbalancedChen.P2OriginalSaving19ArchiveSchema
import ImbalancedChen.P2OriginalSaving19FacetVerticesArrayBlock00000

/-! Actual original facet_vertices typed block 0; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryFacetVerticesJson000 : SourceJson :=
  (facetVerticesChunk000Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped000 : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_000_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_000 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson000 = .ok geometryFacetVerticesTyped000 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_000_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson001 : SourceJson :=
  (facetVerticesChunk000Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped001 : Array Nat :=
  #[0, 2, 4, 7, 9, 11, 12, 15, 16, 17, 20, 23, 25, 27]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_001_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_001 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson001 = .ok geometryFacetVerticesTyped001 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_001_decoded"
  err.flush

theorem geometry_FacetVertices_chunk_000_push_eq (acc : List SourceJson) :
    facetVerticesChunk000Push00 acc = [geometryFacetVerticesJson001, geometryFacetVerticesJson000] ++ acc := by rfl

noncomputable def geometryFacetVerticesJson002 : SourceJson :=
  (facetVerticesChunk001Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped002 : Array Nat :=
  #[1, 3, 5, 6, 8, 10, 13, 14, 18, 19, 21, 22, 24, 26]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_002_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_002 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson002 = .ok geometryFacetVerticesTyped002 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_002_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson003 : SourceJson :=
  (facetVerticesChunk001Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped003 : Array Nat :=
  #[12, 13, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_003_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_003 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson003 = .ok geometryFacetVerticesTyped003 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_003_decoded"
  err.flush

theorem geometry_FacetVertices_chunk_001_push_eq (acc : List SourceJson) :
    facetVerticesChunk001Push00 acc = [geometryFacetVerticesJson003, geometryFacetVerticesJson002] ++ acc := by rfl

noncomputable def geometryFacetVerticesJson004 : SourceJson :=
  (facetVerticesChunk002Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped004 : Array Nat :=
  #[0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_004_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_004 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson004 = .ok geometryFacetVerticesTyped004 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_004_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson005 : SourceJson :=
  (facetVerticesChunk002Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped005 : Array Nat :=
  #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_005_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_005 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson005 = .ok geometryFacetVerticesTyped005 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_005_decoded"
  err.flush

theorem geometry_FacetVertices_chunk_002_push_eq (acc : List SourceJson) :
    facetVerticesChunk002Push00 acc = [geometryFacetVerticesJson005, geometryFacetVerticesJson004] ++ acc := by rfl

noncomputable def geometryFacetVerticesJson006 : SourceJson :=
  (facetVerticesChunk003Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped006 : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 24, 25, 26, 27]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_006_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_006 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson006 = .ok geometryFacetVerticesTyped006 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_006_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson007 : SourceJson :=
  (facetVerticesChunk003Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped007 : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_007_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_007 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson007 = .ok geometryFacetVerticesTyped007 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_007_decoded"
  err.flush

theorem geometry_FacetVertices_chunk_003_push_eq (acc : List SourceJson) :
    facetVerticesChunk003Push00 acc = [geometryFacetVerticesJson007, geometryFacetVerticesJson006] ++ acc := by rfl

noncomputable def geometryFacetVerticesJsonBlock000 : List SourceJson := [geometryFacetVerticesJson000, geometryFacetVerticesJson001, geometryFacetVerticesJson002, geometryFacetVerticesJson003, geometryFacetVerticesJson004, geometryFacetVerticesJson005, geometryFacetVerticesJson006, geometryFacetVerticesJson007]
noncomputable def geometryFacetVerticesTypedBlock000 : List (Array Nat) := [geometryFacetVerticesTyped000, geometryFacetVerticesTyped001, geometryFacetVerticesTyped002, geometryFacetVerticesTyped003, geometryFacetVerticesTyped004, geometryFacetVerticesTyped005, geometryFacetVerticesTyped006, geometryFacetVerticesTyped007]
noncomputable def geometryFacetVerticesBlock000Push (acc : List SourceJson) : List SourceJson := facetVerticesChunk003Push00 (facetVerticesChunk002Push00 (facetVerticesChunk001Push00 (facetVerticesChunk000Push00 (acc))))

theorem geometry_FacetVertices_block_000_push_eq (acc : List SourceJson) :
    geometryFacetVerticesBlock000Push acc = [geometryFacetVerticesJson007, geometryFacetVerticesJson006, geometryFacetVerticesJson005, geometryFacetVerticesJson004, geometryFacetVerticesJson003, geometryFacetVerticesJson002, geometryFacetVerticesJson001, geometryFacetVerticesJson000] ++ acc := by rfl

theorem geometry_FacetVertices_block_000_reverse (acc : List SourceJson) :
    (geometryFacetVerticesBlock000Push acc).reverse = acc.reverse ++ geometryFacetVerticesJsonBlock000 := by
  rw [geometry_FacetVertices_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_FacetVertices_block_000 :
    geometryFacetVerticesJsonBlock000.mapM (SourceJson.Decode.read (α := Array Nat)) = .ok geometryFacetVerticesTypedBlock000 := by
  simp only [geometryFacetVerticesJsonBlock000, geometryFacetVerticesTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_FacetVertices_000, decode_geometry_FacetVertices_001, decode_geometry_FacetVertices_002, decode_geometry_FacetVertices_003, decode_geometry_FacetVertices_004, decode_geometry_FacetVertices_005, decode_geometry_FacetVertices_006, decode_geometry_FacetVertices_007]
  rfl

noncomputable def geometryFacetVerticesTypedThroughBlock000 : List (Array Nat) := geometryFacetVerticesTypedBlock000

theorem decode_geometry_FacetVertices_through_block_000 :
    facetVerticesArrayAcc00400.reverse.mapM (SourceJson.Decode.read (α := Array Nat)) = .ok geometryFacetVerticesTypedThroughBlock000 := by
  change (geometryFacetVerticesBlock000Push facetVerticesArrayAcc00000).reverse.mapM (SourceJson.Decode.read (α := Array Nat)) = _
  rw [geometry_FacetVertices_block_000_reverse]
  exact decode_geometry_FacetVertices_block_000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_block_000_complete"
  err.flush

#print axioms decode_geometry_FacetVertices_000
#print axioms decode_geometry_FacetVertices_001
#print axioms geometry_FacetVertices_chunk_000_push_eq
#print axioms decode_geometry_FacetVertices_002
#print axioms decode_geometry_FacetVertices_003
#print axioms geometry_FacetVertices_chunk_001_push_eq
#print axioms decode_geometry_FacetVertices_004
#print axioms decode_geometry_FacetVertices_005
#print axioms geometry_FacetVertices_chunk_002_push_eq
#print axioms decode_geometry_FacetVertices_006
#print axioms decode_geometry_FacetVertices_007
#print axioms geometry_FacetVertices_chunk_003_push_eq
#print axioms geometry_FacetVertices_block_000_push_eq
#print axioms geometry_FacetVertices_block_000_reverse
#print axioms decode_geometry_FacetVertices_block_000
#print axioms decode_geometry_FacetVertices_through_block_000

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
