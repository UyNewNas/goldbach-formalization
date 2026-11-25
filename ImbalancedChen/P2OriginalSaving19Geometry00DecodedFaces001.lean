import ImbalancedChen.P2OriginalSaving19Geometry00DecodedFaces000
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00100

/-! Actual original face_ledger typed block 1; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryFacesJson005 : SourceJson :=
  (faceLedgerChunk004Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped005 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
    dimension := 6, pivot := 11,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11], #[0, 1, 2, 3, 4, 5, 8, 9, 10, 11], #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11], #[0, 1, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 2, 4, 7, 9, 11], #[1, 3, 5, 6, 8, 10], #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11]],
    simplices := 6 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_005_before_decode"
  err.flush

theorem decode_geometry_Faces_005 :
    decodeFace geometryFacesJson005 = .ok geometryFacesTyped005 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_005_decoded"
  err.flush

theorem geometry_Faces_chunk_004_push_eq (acc : List SourceJson) :
    faceLedgerChunk004Push00 acc = [geometryFacesJson005] ++ acc := by rfl

noncomputable def geometryFacesJson006 : SourceJson :=
  (faceLedgerChunk005Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped006 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
    dimension := 8, pivot := 27,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27], #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27], #[0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 24, 25, 26, 27], #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27], #[0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], #[0, 2, 4, 7, 9, 11, 12, 15, 16, 17, 20, 23, 25, 27], #[1, 3, 5, 6, 8, 10, 13, 14, 18, 19, 21, 22, 24, 26], #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22, 23, 24, 25, 26, 27], #[12, 13, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]],
    simplices := 56 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_006_before_decode"
  err.flush

theorem decode_geometry_Faces_006 :
    decodeFace geometryFacesJson006 = .ok geometryFacesTyped006 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_006_decoded"
  err.flush

theorem geometry_Faces_chunk_005_push_eq (acc : List SourceJson) :
    faceLedgerChunk005Push00 acc = [geometryFacesJson006] ++ acc := by rfl

noncomputable def geometryFacesJson007 : SourceJson :=
  (faceLedgerChunk006Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped007 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
    dimension := 7, pivot := 25,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 16, 17, 18, 19, 20, 21, 22, 23], #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 16, 17, 18, 19, 22, 23, 24, 25], #[0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21, 24, 25], #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 20, 21, 22, 23, 24, 25], #[0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25], #[0, 2, 4, 7, 9, 11, 12, 16, 17, 20, 23, 25], #[1, 3, 5, 6, 8, 10, 13, 18, 19, 21, 22, 24], #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 19, 20, 21, 22, 23, 24, 25], #[12, 13, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]],
    simplices := 42 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_007_before_decode"
  err.flush

theorem decode_geometry_Faces_007 :
    decodeFace geometryFacesJson007 = .ok geometryFacesTyped007 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_007_decoded"
  err.flush

theorem geometry_Faces_chunk_006_push_eq (acc : List SourceJson) :
    faceLedgerChunk006Push00 acc = [geometryFacesJson007] ++ acc := by rfl

noncomputable def geometryFacesJson008 : SourceJson :=
  (faceLedgerChunk007Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped008 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15],
    dimension := 7, pivot := 15,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 15], #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 14, 15], #[0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 14, 15], #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 14, 15], #[0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15], #[0, 2, 4, 7, 9, 11, 15], #[1, 3, 5, 6, 8, 10, 14], #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15]],
    simplices := 7 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_008_before_decode"
  err.flush

theorem decode_geometry_Faces_008 :
    decodeFace geometryFacesJson008 = .ok geometryFacesTyped008 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_008_decoded"
  err.flush

theorem geometry_Faces_chunk_007_push_eq (acc : List SourceJson) :
    faceLedgerChunk007Push00 acc = [geometryFacesJson008] ++ acc := by rfl

noncomputable def geometryFacesJsonBlock001 : List SourceJson := [geometryFacesJson005, geometryFacesJson006, geometryFacesJson007, geometryFacesJson008]
noncomputable def geometryFacesTypedBlock001 : List (FaceRecord) := [geometryFacesTyped005, geometryFacesTyped006, geometryFacesTyped007, geometryFacesTyped008]
noncomputable def geometryFacesBlock001Push (acc : List SourceJson) : List SourceJson := faceLedgerChunk007Push00 (faceLedgerChunk006Push00 (faceLedgerChunk005Push00 (faceLedgerChunk004Push00 (acc))))

theorem geometry_Faces_block_001_push_eq (acc : List SourceJson) :
    geometryFacesBlock001Push acc = [geometryFacesJson008, geometryFacesJson007, geometryFacesJson006, geometryFacesJson005] ++ acc := by rfl

theorem geometry_Faces_block_001_reverse (acc : List SourceJson) :
    (geometryFacesBlock001Push acc).reverse = acc.reverse ++ geometryFacesJsonBlock001 := by
  rw [geometry_Faces_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_001 :
    geometryFacesJsonBlock001.mapM decodeFace = .ok geometryFacesTypedBlock001 := by
  simp only [geometryFacesJsonBlock001, geometryFacesTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_005, decode_geometry_Faces_006, decode_geometry_Faces_007, decode_geometry_Faces_008]
  rfl

noncomputable def geometryFacesTypedThroughBlock001 : List (FaceRecord) := geometryFacesTypedThroughBlock000 ++ geometryFacesTypedBlock001

theorem decode_geometry_Faces_through_block_001 :
    faceLedgerArrayAcc00800.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock001 := by
  change (geometryFacesBlock001Push faceLedgerArrayAcc00400).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_001_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_000, decode_geometry_Faces_block_001]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_block_001_complete"
  err.flush

#print axioms decode_geometry_Faces_005
#print axioms geometry_Faces_chunk_004_push_eq
#print axioms decode_geometry_Faces_006
#print axioms geometry_Faces_chunk_005_push_eq
#print axioms decode_geometry_Faces_007
#print axioms geometry_Faces_chunk_006_push_eq
#print axioms decode_geometry_Faces_008
#print axioms geometry_Faces_chunk_007_push_eq
#print axioms geometry_Faces_block_001_push_eq
#print axioms geometry_Faces_block_001_reverse
#print axioms decode_geometry_Faces_block_001
#print axioms decode_geometry_Faces_through_block_001

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
