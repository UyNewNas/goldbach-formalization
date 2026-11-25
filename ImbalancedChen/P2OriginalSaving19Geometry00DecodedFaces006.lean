import ImbalancedChen.P2OriginalSaving19Geometry00DecodedFaces005
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00600

/-! Actual original face_ledger typed block 6; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryFacesJson027 : SourceJson :=
  (faceLedgerChunk024Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped027 : FaceRecord :=
  { vertices := #[1, 3, 5, 6, 8, 10, 14],
    dimension := 6, pivot := 14,
    facetSets := #[#[1, 3, 5, 6, 8, 10], #[1, 3, 5, 6, 8, 14], #[1, 3, 5, 6, 10, 14], #[1, 3, 5, 8, 10, 14], #[1, 3, 6, 8, 10, 14], #[1, 5, 6, 8, 10, 14], #[3, 5, 6, 8, 10, 14]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_027_before_decode"
  err.flush

theorem decode_geometry_Faces_027 :
    decodeFace geometryFacesJson027 = .ok geometryFacesTyped027 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_027_decoded"
  err.flush

theorem geometry_Faces_chunk_024_push_eq (acc : List SourceJson) :
    faceLedgerChunk024Push00 acc = [geometryFacesJson027] ++ acc := by rfl

noncomputable def geometryFacesJson028 : SourceJson :=
  (faceLedgerChunk025Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped028 : FaceRecord :=
  { vertices := #[1, 3, 5, 6, 8, 13, 18, 19, 21, 22],
    dimension := 5, pivot := 22,
    facetSets := #[#[1, 3, 5, 6, 8], #[1, 3, 5, 6, 13, 18, 19, 22], #[1, 3, 5, 8, 13, 18, 19, 21], #[1, 3, 6, 8, 13, 18, 21, 22], #[1, 5, 6, 8, 18, 19, 21, 22], #[3, 5, 6, 8, 13, 19, 21, 22], #[13, 18, 19, 21, 22]],
    simplices := 5 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_028_before_decode"
  err.flush

theorem decode_geometry_Faces_028 :
    decodeFace geometryFacesJson028 = .ok geometryFacesTyped028 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_028_decoded"
  err.flush

theorem geometry_Faces_chunk_025_push_eq (acc : List SourceJson) :
    faceLedgerChunk025Push00 acc = [geometryFacesJson028] ++ acc := by rfl

noncomputable def geometryFacesJson029 : SourceJson :=
  (faceLedgerChunk026Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped029 : FaceRecord :=
  { vertices := #[1, 3, 5, 8],
    dimension := 3, pivot := 8,
    facetSets := #[#[1, 3, 5], #[1, 3, 8], #[1, 5, 8], #[3, 5, 8]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_029_before_decode"
  err.flush

theorem decode_geometry_Faces_029 :
    decodeFace geometryFacesJson029 = .ok geometryFacesTyped029 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_029_decoded"
  err.flush

theorem geometry_Faces_chunk_026_push_eq (acc : List SourceJson) :
    faceLedgerChunk026Push00 acc = [geometryFacesJson029] ++ acc := by rfl

noncomputable def geometryFacesJson030 : SourceJson :=
  (faceLedgerChunk027Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped030 : FaceRecord :=
  { vertices := #[1, 3, 5, 8, 13, 18, 19, 21],
    dimension := 4, pivot := 21,
    facetSets := #[#[1, 3, 5, 8], #[1, 3, 5, 13, 18, 19], #[1, 3, 8, 13, 18, 21], #[1, 5, 8, 18, 19, 21], #[3, 5, 8, 13, 19, 21], #[13, 18, 19, 21]],
    simplices := 4 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_030_before_decode"
  err.flush

theorem decode_geometry_Faces_030 :
    decodeFace geometryFacesJson030 = .ok geometryFacesTyped030 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_030_decoded"
  err.flush

theorem geometry_Faces_chunk_027_push_eq (acc : List SourceJson) :
    faceLedgerChunk027Push00 acc = [geometryFacesJson030] ++ acc := by rfl

noncomputable def geometryFacesJsonBlock006 : List SourceJson := [geometryFacesJson027, geometryFacesJson028, geometryFacesJson029, geometryFacesJson030]
noncomputable def geometryFacesTypedBlock006 : List (FaceRecord) := [geometryFacesTyped027, geometryFacesTyped028, geometryFacesTyped029, geometryFacesTyped030]
noncomputable def geometryFacesBlock006Push (acc : List SourceJson) : List SourceJson := faceLedgerChunk027Push00 (faceLedgerChunk026Push00 (faceLedgerChunk025Push00 (faceLedgerChunk024Push00 (acc))))

theorem geometry_Faces_block_006_push_eq (acc : List SourceJson) :
    geometryFacesBlock006Push acc = [geometryFacesJson030, geometryFacesJson029, geometryFacesJson028, geometryFacesJson027] ++ acc := by rfl

theorem geometry_Faces_block_006_reverse (acc : List SourceJson) :
    (geometryFacesBlock006Push acc).reverse = acc.reverse ++ geometryFacesJsonBlock006 := by
  rw [geometry_Faces_block_006_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_006 :
    geometryFacesJsonBlock006.mapM decodeFace = .ok geometryFacesTypedBlock006 := by
  simp only [geometryFacesJsonBlock006, geometryFacesTypedBlock006, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_027, decode_geometry_Faces_028, decode_geometry_Faces_029, decode_geometry_Faces_030]
  rfl

noncomputable def geometryFacesTypedThroughBlock006 : List (FaceRecord) := geometryFacesTypedThroughBlock005 ++ geometryFacesTypedBlock006

theorem decode_geometry_Faces_through_block_006 :
    faceLedgerArrayAcc02800.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock006 := by
  change (geometryFacesBlock006Push faceLedgerArrayAcc02400).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_006_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_005, decode_geometry_Faces_block_006]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_block_006_complete"
  err.flush

#print axioms decode_geometry_Faces_027
#print axioms geometry_Faces_chunk_024_push_eq
#print axioms decode_geometry_Faces_028
#print axioms geometry_Faces_chunk_025_push_eq
#print axioms decode_geometry_Faces_029
#print axioms geometry_Faces_chunk_026_push_eq
#print axioms decode_geometry_Faces_030
#print axioms geometry_Faces_chunk_027_push_eq
#print axioms geometry_Faces_block_006_push_eq
#print axioms geometry_Faces_block_006_reverse
#print axioms decode_geometry_Faces_block_006
#print axioms decode_geometry_Faces_through_block_006

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
