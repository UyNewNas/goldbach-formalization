import ImbalancedChen.P2OriginalSaving19Geometry00DecodedFaces003
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00400

/-! Actual original face_ledger typed block 4; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryFacesJson018 : SourceJson :=
  (faceLedgerChunk016Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped018 : FaceRecord :=
  { vertices := #[0, 2, 4, 12, 16, 17],
    dimension := 3, pivot := 17,
    facetSets := #[#[0, 2, 4], #[0, 2, 12, 17], #[0, 4, 16, 17], #[2, 4, 12, 16], #[12, 16, 17]],
    simplices := 3 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_018_before_decode"
  err.flush

theorem decode_geometry_Faces_018 :
    decodeFace geometryFacesJson018 = .ok geometryFacesTyped018 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_018_decoded"
  err.flush

theorem geometry_Faces_chunk_016_push_eq (acc : List SourceJson) :
    faceLedgerChunk016Push00 acc = [geometryFacesJson018] ++ acc := by rfl

noncomputable def geometryFacesJson019 : SourceJson :=
  (faceLedgerChunk017Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped019 : FaceRecord :=
  { vertices := #[0, 2, 12, 17],
    dimension := 2, pivot := 17,
    facetSets := #[#[0, 2], #[0, 17], #[2, 12], #[12, 17]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_019_before_decode"
  err.flush

theorem decode_geometry_Faces_019 :
    decodeFace geometryFacesJson019 = .ok geometryFacesTyped019 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_019_decoded"
  err.flush

noncomputable def geometryFacesJson020 : SourceJson :=
  (faceLedgerChunk017Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped020 : FaceRecord :=
  { vertices := #[1, 3],
    dimension := 1, pivot := 3,
    facetSets := #[#[1], #[3]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_020_before_decode"
  err.flush

theorem decode_geometry_Faces_020 :
    decodeFace geometryFacesJson020 = .ok geometryFacesTyped020 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_020_decoded"
  err.flush

theorem geometry_Faces_chunk_017_push_eq (acc : List SourceJson) :
    faceLedgerChunk017Push00 acc = [geometryFacesJson020, geometryFacesJson019] ++ acc := by rfl

noncomputable def geometryFacesJson021 : SourceJson :=
  (faceLedgerChunk018Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped021 : FaceRecord :=
  { vertices := #[1, 3, 5],
    dimension := 2, pivot := 5,
    facetSets := #[#[1, 3], #[1, 5], #[3, 5]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_021_before_decode"
  err.flush

theorem decode_geometry_Faces_021 :
    decodeFace geometryFacesJson021 = .ok geometryFacesTyped021 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_021_decoded"
  err.flush

theorem geometry_Faces_chunk_018_push_eq (acc : List SourceJson) :
    faceLedgerChunk018Push00 acc = [geometryFacesJson021] ++ acc := by rfl

noncomputable def geometryFacesJson022 : SourceJson :=
  (faceLedgerChunk019Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped022 : FaceRecord :=
  { vertices := #[1, 3, 5, 6],
    dimension := 3, pivot := 6,
    facetSets := #[#[1, 3, 5], #[1, 3, 6], #[1, 5, 6], #[3, 5, 6]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_022_before_decode"
  err.flush

theorem decode_geometry_Faces_022 :
    decodeFace geometryFacesJson022 = .ok geometryFacesTyped022 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_022_decoded"
  err.flush

theorem geometry_Faces_chunk_019_push_eq (acc : List SourceJson) :
    faceLedgerChunk019Push00 acc = [geometryFacesJson022] ++ acc := by rfl

noncomputable def geometryFacesJsonBlock004 : List SourceJson := [geometryFacesJson018, geometryFacesJson019, geometryFacesJson020, geometryFacesJson021, geometryFacesJson022]
noncomputable def geometryFacesTypedBlock004 : List (FaceRecord) := [geometryFacesTyped018, geometryFacesTyped019, geometryFacesTyped020, geometryFacesTyped021, geometryFacesTyped022]
noncomputable def geometryFacesBlock004Push (acc : List SourceJson) : List SourceJson := faceLedgerChunk019Push00 (faceLedgerChunk018Push00 (faceLedgerChunk017Push00 (faceLedgerChunk016Push00 (acc))))

theorem geometry_Faces_block_004_push_eq (acc : List SourceJson) :
    geometryFacesBlock004Push acc = [geometryFacesJson022, geometryFacesJson021, geometryFacesJson020, geometryFacesJson019, geometryFacesJson018] ++ acc := by rfl

theorem geometry_Faces_block_004_reverse (acc : List SourceJson) :
    (geometryFacesBlock004Push acc).reverse = acc.reverse ++ geometryFacesJsonBlock004 := by
  rw [geometry_Faces_block_004_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_004 :
    geometryFacesJsonBlock004.mapM decodeFace = .ok geometryFacesTypedBlock004 := by
  simp only [geometryFacesJsonBlock004, geometryFacesTypedBlock004, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_018, decode_geometry_Faces_019, decode_geometry_Faces_020, decode_geometry_Faces_021, decode_geometry_Faces_022]
  rfl

noncomputable def geometryFacesTypedThroughBlock004 : List (FaceRecord) := geometryFacesTypedThroughBlock003 ++ geometryFacesTypedBlock004

theorem decode_geometry_Faces_through_block_004 :
    faceLedgerArrayAcc02000.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock004 := by
  change (geometryFacesBlock004Push faceLedgerArrayAcc01600).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_004_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_003, decode_geometry_Faces_block_004]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_block_004_complete"
  err.flush

#print axioms decode_geometry_Faces_018
#print axioms geometry_Faces_chunk_016_push_eq
#print axioms decode_geometry_Faces_019
#print axioms decode_geometry_Faces_020
#print axioms geometry_Faces_chunk_017_push_eq
#print axioms decode_geometry_Faces_021
#print axioms geometry_Faces_chunk_018_push_eq
#print axioms decode_geometry_Faces_022
#print axioms geometry_Faces_chunk_019_push_eq
#print axioms geometry_Faces_block_004_push_eq
#print axioms geometry_Faces_block_004_reverse
#print axioms decode_geometry_Faces_block_004
#print axioms decode_geometry_Faces_through_block_004

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
