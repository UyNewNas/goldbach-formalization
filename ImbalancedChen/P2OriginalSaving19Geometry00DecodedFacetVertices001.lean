import ImbalancedChen.P2OriginalSaving19Geometry00DecodedFacetVertices000
import ImbalancedChen.P2OriginalSaving19FacetVerticesArrayBlock00100

/-! Actual original facet_vertices typed block 1; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryFacetVerticesJson008 : SourceJson :=
  (facetVerticesChunk004Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped008 : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_008_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_008 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson008 = .ok geometryFacetVerticesTyped008 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_008_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson009 : SourceJson :=
  (facetVerticesChunk004Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped009 : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_009_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_009 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson009 = .ok geometryFacetVerticesTyped009 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_009_decoded"
  err.flush

theorem geometry_FacetVertices_chunk_004_push_eq (acc : List SourceJson) :
    facetVerticesChunk004Push00 acc = [geometryFacetVerticesJson009, geometryFacetVerticesJson008] ++ acc := by rfl

noncomputable def geometryFacetVerticesJson010 : SourceJson :=
  (facetVerticesChunk005Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped010 : Array Nat :=
  #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22, 23, 24, 25, 26, 27]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_010_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_010 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson010 = .ok geometryFacetVerticesTyped010 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_record_010_decoded"
  err.flush

theorem geometry_FacetVertices_chunk_005_push_eq (acc : List SourceJson) :
    facetVerticesChunk005Push00 acc = [geometryFacetVerticesJson010] ++ acc := by rfl

noncomputable def geometryFacetVerticesJsonBlock001 : List SourceJson := [geometryFacetVerticesJson008, geometryFacetVerticesJson009, geometryFacetVerticesJson010]
noncomputable def geometryFacetVerticesTypedBlock001 : List (Array Nat) := [geometryFacetVerticesTyped008, geometryFacetVerticesTyped009, geometryFacetVerticesTyped010]
noncomputable def geometryFacetVerticesBlock001Push (acc : List SourceJson) : List SourceJson := facetVerticesChunk005Push00 (facetVerticesChunk004Push00 (acc))

theorem geometry_FacetVertices_block_001_push_eq (acc : List SourceJson) :
    geometryFacetVerticesBlock001Push acc = [geometryFacetVerticesJson010, geometryFacetVerticesJson009, geometryFacetVerticesJson008] ++ acc := by rfl

theorem geometry_FacetVertices_block_001_reverse (acc : List SourceJson) :
    (geometryFacetVerticesBlock001Push acc).reverse = acc.reverse ++ geometryFacetVerticesJsonBlock001 := by
  rw [geometry_FacetVertices_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_FacetVertices_block_001 :
    geometryFacetVerticesJsonBlock001.mapM (SourceJson.Decode.read (α := Array Nat)) = .ok geometryFacetVerticesTypedBlock001 := by
  simp only [geometryFacetVerticesJsonBlock001, geometryFacetVerticesTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_FacetVertices_008, decode_geometry_FacetVertices_009, decode_geometry_FacetVertices_010]
  rfl

noncomputable def geometryFacetVerticesTypedThroughBlock001 : List (Array Nat) := geometryFacetVerticesTypedThroughBlock000 ++ geometryFacetVerticesTypedBlock001

theorem decode_geometry_FacetVertices_through_block_001 :
    facetVerticesArrayAcc00600.reverse.mapM (SourceJson.Decode.read (α := Array Nat)) = .ok geometryFacetVerticesTypedThroughBlock001 := by
  change (geometryFacetVerticesBlock001Push facetVerticesArrayAcc00400).reverse.mapM (SourceJson.Decode.read (α := Array Nat)) = _
  rw [geometry_FacetVertices_block_001_reverse]
  rw [List.mapM_append, decode_geometry_FacetVertices_through_block_000, decode_geometry_FacetVertices_block_001]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED FacetVertices_block_001_complete"
  err.flush

#print axioms decode_geometry_FacetVertices_008
#print axioms decode_geometry_FacetVertices_009
#print axioms geometry_FacetVertices_chunk_004_push_eq
#print axioms decode_geometry_FacetVertices_010
#print axioms geometry_FacetVertices_chunk_005_push_eq
#print axioms geometry_FacetVertices_block_001_push_eq
#print axioms geometry_FacetVertices_block_001_reverse
#print axioms decode_geometry_FacetVertices_block_001
#print axioms decode_geometry_FacetVertices_through_block_001

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
