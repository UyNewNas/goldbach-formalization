import ImbalancedChen.P2OriginalSaving19Geometry00DecodedFaces004
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00500

/-! Actual original face_ledger typed block 5; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryFacesJson023 : SourceJson :=
  (faceLedgerChunk020Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped023 : FaceRecord :=
  { vertices := #[1, 3, 5, 6, 8],
    dimension := 4, pivot := 8,
    facetSets := #[#[1, 3, 5, 6], #[1, 3, 5, 8], #[1, 3, 6, 8], #[1, 5, 6, 8], #[3, 5, 6, 8]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_023_before_decode"
  err.flush

theorem decode_geometry_Faces_023 :
    decodeFace geometryFacesJson023 = .ok geometryFacesTyped023 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_023_decoded"
  err.flush

theorem geometry_Faces_chunk_020_push_eq (acc : List SourceJson) :
    faceLedgerChunk020Push00 acc = [geometryFacesJson023] ++ acc := by rfl

noncomputable def geometryFacesJson024 : SourceJson :=
  (faceLedgerChunk021Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped024 : FaceRecord :=
  { vertices := #[1, 3, 5, 6, 8, 10],
    dimension := 5, pivot := 10,
    facetSets := #[#[1, 3, 5, 6, 8], #[1, 3, 5, 6, 10], #[1, 3, 5, 8, 10], #[1, 3, 6, 8, 10], #[1, 5, 6, 8, 10], #[3, 5, 6, 8, 10]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_024_before_decode"
  err.flush

theorem decode_geometry_Faces_024 :
    decodeFace geometryFacesJson024 = .ok geometryFacesTyped024 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_024_decoded"
  err.flush

theorem geometry_Faces_chunk_021_push_eq (acc : List SourceJson) :
    faceLedgerChunk021Push00 acc = [geometryFacesJson024] ++ acc := by rfl

noncomputable def geometryFacesJson025 : SourceJson :=
  (faceLedgerChunk022Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped025 : FaceRecord :=
  { vertices := #[1, 3, 5, 6, 8, 10, 13, 14, 18, 19, 21, 22, 24, 26],
    dimension := 7, pivot := 26,
    facetSets := #[#[1, 3, 5, 6, 8, 10, 13, 18, 19, 21, 22, 24], #[1, 3, 5, 6, 8, 10, 14], #[1, 3, 5, 6, 8, 13, 14, 18, 19, 21, 22, 26], #[1, 3, 5, 6, 10, 13, 14, 18, 19, 22, 24, 26], #[1, 3, 5, 8, 10, 13, 14, 18, 19, 21, 24, 26], #[1, 3, 6, 8, 10, 13, 14, 18, 21, 22, 24, 26], #[1, 5, 6, 8, 10, 14, 18, 19, 21, 22, 24, 26], #[3, 5, 6, 8, 10, 13, 14, 19, 21, 22, 24, 26], #[13, 18, 19, 21, 22, 24, 26]],
    simplices := 7 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_025_before_decode"
  err.flush

theorem decode_geometry_Faces_025 :
    decodeFace geometryFacesJson025 = .ok geometryFacesTyped025 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_025_decoded"
  err.flush

theorem geometry_Faces_chunk_022_push_eq (acc : List SourceJson) :
    faceLedgerChunk022Push00 acc = [geometryFacesJson025] ++ acc := by rfl

noncomputable def geometryFacesJson026 : SourceJson :=
  (faceLedgerChunk023Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped026 : FaceRecord :=
  { vertices := #[1, 3, 5, 6, 8, 10, 13, 18, 19, 21, 22, 24],
    dimension := 6, pivot := 24,
    facetSets := #[#[1, 3, 5, 6, 8, 10], #[1, 3, 5, 6, 8, 13, 18, 19, 21, 22], #[1, 3, 5, 6, 10, 13, 18, 19, 22, 24], #[1, 3, 5, 8, 10, 13, 18, 19, 21, 24], #[1, 3, 6, 8, 10, 13, 18, 21, 22, 24], #[1, 5, 6, 8, 10, 18, 19, 21, 22, 24], #[3, 5, 6, 8, 10, 13, 19, 21, 22, 24], #[13, 18, 19, 21, 22, 24]],
    simplices := 6 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_026_before_decode"
  err.flush

theorem decode_geometry_Faces_026 :
    decodeFace geometryFacesJson026 = .ok geometryFacesTyped026 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_026_decoded"
  err.flush

theorem geometry_Faces_chunk_023_push_eq (acc : List SourceJson) :
    faceLedgerChunk023Push00 acc = [geometryFacesJson026] ++ acc := by rfl

noncomputable def geometryFacesJsonBlock005 : List SourceJson := [geometryFacesJson023, geometryFacesJson024, geometryFacesJson025, geometryFacesJson026]
noncomputable def geometryFacesTypedBlock005 : List (FaceRecord) := [geometryFacesTyped023, geometryFacesTyped024, geometryFacesTyped025, geometryFacesTyped026]
noncomputable def geometryFacesBlock005Push (acc : List SourceJson) : List SourceJson := faceLedgerChunk023Push00 (faceLedgerChunk022Push00 (faceLedgerChunk021Push00 (faceLedgerChunk020Push00 (acc))))

theorem geometry_Faces_block_005_push_eq (acc : List SourceJson) :
    geometryFacesBlock005Push acc = [geometryFacesJson026, geometryFacesJson025, geometryFacesJson024, geometryFacesJson023] ++ acc := by rfl

theorem geometry_Faces_block_005_reverse (acc : List SourceJson) :
    (geometryFacesBlock005Push acc).reverse = acc.reverse ++ geometryFacesJsonBlock005 := by
  rw [geometry_Faces_block_005_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_005 :
    geometryFacesJsonBlock005.mapM decodeFace = .ok geometryFacesTypedBlock005 := by
  simp only [geometryFacesJsonBlock005, geometryFacesTypedBlock005, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_023, decode_geometry_Faces_024, decode_geometry_Faces_025, decode_geometry_Faces_026]
  rfl

noncomputable def geometryFacesTypedThroughBlock005 : List (FaceRecord) := geometryFacesTypedThroughBlock004 ++ geometryFacesTypedBlock005

theorem decode_geometry_Faces_through_block_005 :
    faceLedgerArrayAcc02400.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock005 := by
  change (geometryFacesBlock005Push faceLedgerArrayAcc02000).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_005_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_004, decode_geometry_Faces_block_005]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_block_005_complete"
  err.flush

#print axioms decode_geometry_Faces_023
#print axioms geometry_Faces_chunk_020_push_eq
#print axioms decode_geometry_Faces_024
#print axioms geometry_Faces_chunk_021_push_eq
#print axioms decode_geometry_Faces_025
#print axioms geometry_Faces_chunk_022_push_eq
#print axioms decode_geometry_Faces_026
#print axioms geometry_Faces_chunk_023_push_eq
#print axioms geometry_Faces_block_005_push_eq
#print axioms geometry_Faces_block_005_reverse
#print axioms decode_geometry_Faces_block_005
#print axioms decode_geometry_Faces_through_block_005

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
