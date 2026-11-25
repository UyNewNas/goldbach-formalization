import ImbalancedChen.P2OriginalSaving19Geometry00DecodedFaces007
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00800

/-! Actual original face_ledger typed block 8; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryFacesJson038 : SourceJson :=
  (faceLedgerChunk032Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped038 : FaceRecord :=
  { vertices := #[3, 13],
    dimension := 1, pivot := 13,
    facetSets := #[#[3], #[13]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_038_before_decode"
  err.flush

theorem decode_geometry_Faces_038 :
    decodeFace geometryFacesJson038 = .ok geometryFacesTyped038 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_038_decoded"
  err.flush

theorem geometry_Faces_chunk_032_push_eq (acc : List SourceJson) :
    faceLedgerChunk032Push00 acc = [geometryFacesJson038] ++ acc := by rfl

noncomputable def geometryFacesJsonBlock008 : List SourceJson := [geometryFacesJson038]
noncomputable def geometryFacesTypedBlock008 : List (FaceRecord) := [geometryFacesTyped038]
noncomputable def geometryFacesBlock008Push (acc : List SourceJson) : List SourceJson := faceLedgerChunk032Push00 (acc)

theorem geometry_Faces_block_008_push_eq (acc : List SourceJson) :
    geometryFacesBlock008Push acc = [geometryFacesJson038] ++ acc := by rfl

theorem geometry_Faces_block_008_reverse (acc : List SourceJson) :
    (geometryFacesBlock008Push acc).reverse = acc.reverse ++ geometryFacesJsonBlock008 := by
  rw [geometry_Faces_block_008_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_008 :
    geometryFacesJsonBlock008.mapM decodeFace = .ok geometryFacesTypedBlock008 := by
  simp only [geometryFacesJsonBlock008, geometryFacesTypedBlock008, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_038]
  rfl

noncomputable def geometryFacesTypedThroughBlock008 : List (FaceRecord) := geometryFacesTypedThroughBlock007 ++ geometryFacesTypedBlock008

theorem decode_geometry_Faces_through_block_008 :
    faceLedgerArrayAcc03300.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock008 := by
  change (geometryFacesBlock008Push faceLedgerArrayAcc03200).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_008_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_007, decode_geometry_Faces_block_008]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_block_008_complete"
  err.flush

#print axioms decode_geometry_Faces_038
#print axioms geometry_Faces_chunk_032_push_eq
#print axioms geometry_Faces_block_008_push_eq
#print axioms geometry_Faces_block_008_reverse
#print axioms decode_geometry_Faces_block_008
#print axioms decode_geometry_Faces_through_block_008

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
