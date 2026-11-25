import ImbalancedChen.P2OriginalSaving19Geometry00DecodedFaces002
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00300

/-! Actual original face_ledger typed block 3; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryFacesJson013 : SourceJson :=
  (faceLedgerChunk012Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped013 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 12, 13, 17, 18],
    dimension := 3, pivot := 18,
    facetSets := #[#[0, 1, 2, 3], #[0, 1, 17, 18], #[0, 2, 12, 17], #[1, 3, 13, 18], #[2, 3, 12, 13], #[12, 13, 17, 18]],
    simplices := 6 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_013_before_decode"
  err.flush

theorem decode_geometry_Faces_013 :
    decodeFace geometryFacesJson013 = .ok geometryFacesTyped013 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_013_decoded"
  err.flush

theorem geometry_Faces_chunk_012_push_eq (acc : List SourceJson) :
    faceLedgerChunk012Push00 acc = [geometryFacesJson013] ++ acc := by rfl

noncomputable def geometryFacesJson014 : SourceJson :=
  (faceLedgerChunk013Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped014 : FaceRecord :=
  { vertices := #[0, 2],
    dimension := 1, pivot := 2,
    facetSets := #[#[0], #[2]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_014_before_decode"
  err.flush

theorem decode_geometry_Faces_014 :
    decodeFace geometryFacesJson014 = .ok geometryFacesTyped014 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_014_decoded"
  err.flush

noncomputable def geometryFacesJson015 : SourceJson :=
  (faceLedgerChunk013Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped015 : FaceRecord :=
  { vertices := #[0, 2, 4],
    dimension := 2, pivot := 4,
    facetSets := #[#[0, 2], #[0, 4], #[2, 4]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_015_before_decode"
  err.flush

theorem decode_geometry_Faces_015 :
    decodeFace geometryFacesJson015 = .ok geometryFacesTyped015 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_015_decoded"
  err.flush

theorem geometry_Faces_chunk_013_push_eq (acc : List SourceJson) :
    faceLedgerChunk013Push00 acc = [geometryFacesJson015, geometryFacesJson014] ++ acc := by rfl

noncomputable def geometryFacesJson016 : SourceJson :=
  (faceLedgerChunk014Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped016 : FaceRecord :=
  { vertices := #[0, 2, 4, 9],
    dimension := 3, pivot := 9,
    facetSets := #[#[0, 2, 4], #[0, 2, 9], #[0, 4, 9], #[2, 4, 9]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_016_before_decode"
  err.flush

theorem decode_geometry_Faces_016 :
    decodeFace geometryFacesJson016 = .ok geometryFacesTyped016 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_016_decoded"
  err.flush

theorem geometry_Faces_chunk_014_push_eq (acc : List SourceJson) :
    faceLedgerChunk014Push00 acc = [geometryFacesJson016] ++ acc := by rfl

noncomputable def geometryFacesJson017 : SourceJson :=
  (faceLedgerChunk015Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped017 : FaceRecord :=
  { vertices := #[0, 2, 4, 9, 12, 16, 17, 20],
    dimension := 4, pivot := 20,
    facetSets := #[#[0, 2, 4, 9], #[0, 2, 4, 12, 16, 17], #[0, 2, 9, 12, 17, 20], #[0, 4, 9, 16, 17, 20], #[2, 4, 9, 12, 16, 20], #[12, 16, 17, 20]],
    simplices := 4 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_017_before_decode"
  err.flush

theorem decode_geometry_Faces_017 :
    decodeFace geometryFacesJson017 = .ok geometryFacesTyped017 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_017_decoded"
  err.flush

theorem geometry_Faces_chunk_015_push_eq (acc : List SourceJson) :
    faceLedgerChunk015Push00 acc = [geometryFacesJson017] ++ acc := by rfl

noncomputable def geometryFacesJsonBlock003 : List SourceJson := [geometryFacesJson013, geometryFacesJson014, geometryFacesJson015, geometryFacesJson016, geometryFacesJson017]
noncomputable def geometryFacesTypedBlock003 : List (FaceRecord) := [geometryFacesTyped013, geometryFacesTyped014, geometryFacesTyped015, geometryFacesTyped016, geometryFacesTyped017]
noncomputable def geometryFacesBlock003Push (acc : List SourceJson) : List SourceJson := faceLedgerChunk015Push00 (faceLedgerChunk014Push00 (faceLedgerChunk013Push00 (faceLedgerChunk012Push00 (acc))))

theorem geometry_Faces_block_003_push_eq (acc : List SourceJson) :
    geometryFacesBlock003Push acc = [geometryFacesJson017, geometryFacesJson016, geometryFacesJson015, geometryFacesJson014, geometryFacesJson013] ++ acc := by rfl

theorem geometry_Faces_block_003_reverse (acc : List SourceJson) :
    (geometryFacesBlock003Push acc).reverse = acc.reverse ++ geometryFacesJsonBlock003 := by
  rw [geometry_Faces_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_003 :
    geometryFacesJsonBlock003.mapM decodeFace = .ok geometryFacesTypedBlock003 := by
  simp only [geometryFacesJsonBlock003, geometryFacesTypedBlock003, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_013, decode_geometry_Faces_014, decode_geometry_Faces_015, decode_geometry_Faces_016, decode_geometry_Faces_017]
  rfl

noncomputable def geometryFacesTypedThroughBlock003 : List (FaceRecord) := geometryFacesTypedThroughBlock002 ++ geometryFacesTypedBlock003

theorem decode_geometry_Faces_through_block_003 :
    faceLedgerArrayAcc01600.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock003 := by
  change (geometryFacesBlock003Push faceLedgerArrayAcc01200).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_003_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_002, decode_geometry_Faces_block_003]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_block_003_complete"
  err.flush

#print axioms decode_geometry_Faces_013
#print axioms geometry_Faces_chunk_012_push_eq
#print axioms decode_geometry_Faces_014
#print axioms decode_geometry_Faces_015
#print axioms geometry_Faces_chunk_013_push_eq
#print axioms decode_geometry_Faces_016
#print axioms geometry_Faces_chunk_014_push_eq
#print axioms decode_geometry_Faces_017
#print axioms geometry_Faces_chunk_015_push_eq
#print axioms geometry_Faces_block_003_push_eq
#print axioms geometry_Faces_block_003_reverse
#print axioms decode_geometry_Faces_block_003
#print axioms decode_geometry_Faces_through_block_003

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
