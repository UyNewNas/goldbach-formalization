import ImbalancedChen.P2OriginalSaving19Geometry00DecodedFaces001
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00200

/-! Actual original face_ledger typed block 2; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryFacesJson009 : SourceJson :=
  (faceLedgerChunk008Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped009 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 16, 17, 18, 19, 20, 21, 22, 23],
    dimension := 6, pivot := 23,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], #[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 16, 17, 18, 19, 22, 23], #[0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 16, 17, 18, 19, 20, 21], #[0, 1, 2, 3, 6, 7, 8, 9, 12, 13, 17, 18, 20, 21, 22, 23], #[0, 1, 4, 5, 6, 7, 8, 9, 16, 17, 18, 19, 20, 21, 22, 23], #[0, 2, 4, 7, 9, 12, 16, 17, 20, 23], #[1, 3, 5, 6, 8, 13, 18, 19, 21, 22], #[2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 16, 19, 20, 21, 22, 23], #[12, 13, 16, 17, 18, 19, 20, 21, 22, 23]],
    simplices := 30 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_009_before_decode"
  err.flush

theorem decode_geometry_Faces_009 :
    decodeFace geometryFacesJson009 = .ok geometryFacesTyped009 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_009_decoded"
  err.flush

theorem geometry_Faces_chunk_008_push_eq (acc : List SourceJson) :
    faceLedgerChunk008Push00 acc = [geometryFacesJson009] ++ acc := by rfl

noncomputable def geometryFacesJson010 : SourceJson :=
  (faceLedgerChunk009Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped010 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 8, 9],
    dimension := 4, pivot := 9,
    facetSets := #[#[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 8, 9], #[0, 1, 4, 5, 8, 9], #[0, 2, 4, 9], #[1, 3, 5, 8], #[2, 3, 4, 5, 8, 9]],
    simplices := 4 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_010_before_decode"
  err.flush

theorem decode_geometry_Faces_010 :
    decodeFace geometryFacesJson010 = .ok geometryFacesTyped010 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_010_decoded"
  err.flush

theorem geometry_Faces_chunk_009_push_eq (acc : List SourceJson) :
    faceLedgerChunk009Push00 acc = [geometryFacesJson010] ++ acc := by rfl

noncomputable def geometryFacesJson011 : SourceJson :=
  (faceLedgerChunk010Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped011 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 16, 17, 18, 19, 20, 21],
    dimension := 5, pivot := 21,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 8, 9], #[0, 1, 2, 3, 4, 5, 12, 13, 16, 17, 18, 19], #[0, 1, 2, 3, 8, 9, 12, 13, 17, 18, 20, 21], #[0, 1, 4, 5, 8, 9, 16, 17, 18, 19, 20, 21], #[0, 2, 4, 9, 12, 16, 17, 20], #[1, 3, 5, 8, 13, 18, 19, 21], #[2, 3, 4, 5, 8, 9, 12, 13, 16, 19, 20, 21], #[12, 13, 16, 17, 18, 19, 20, 21]],
    simplices := 20 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_011_before_decode"
  err.flush

theorem decode_geometry_Faces_011 :
    decodeFace geometryFacesJson011 = .ok geometryFacesTyped011 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_011_decoded"
  err.flush

theorem geometry_Faces_chunk_010_push_eq (acc : List SourceJson) :
    faceLedgerChunk010Push00 acc = [geometryFacesJson011] ++ acc := by rfl

noncomputable def geometryFacesJson012 : SourceJson :=
  (faceLedgerChunk011Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped012 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 12, 13, 16, 17, 18, 19],
    dimension := 4, pivot := 19,
    facetSets := #[#[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 12, 13, 17, 18], #[0, 1, 4, 5, 16, 17, 18, 19], #[0, 2, 4, 12, 16, 17], #[1, 3, 5, 13, 18, 19], #[2, 3, 4, 5, 12, 13, 16, 19], #[12, 13, 16, 17, 18, 19]],
    simplices := 12 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_012_before_decode"
  err.flush

theorem decode_geometry_Faces_012 :
    decodeFace geometryFacesJson012 = .ok geometryFacesTyped012 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_012_decoded"
  err.flush

theorem geometry_Faces_chunk_011_push_eq (acc : List SourceJson) :
    faceLedgerChunk011Push00 acc = [geometryFacesJson012] ++ acc := by rfl

noncomputable def geometryFacesJsonBlock002 : List SourceJson := [geometryFacesJson009, geometryFacesJson010, geometryFacesJson011, geometryFacesJson012]
noncomputable def geometryFacesTypedBlock002 : List (FaceRecord) := [geometryFacesTyped009, geometryFacesTyped010, geometryFacesTyped011, geometryFacesTyped012]
noncomputable def geometryFacesBlock002Push (acc : List SourceJson) : List SourceJson := faceLedgerChunk011Push00 (faceLedgerChunk010Push00 (faceLedgerChunk009Push00 (faceLedgerChunk008Push00 (acc))))

theorem geometry_Faces_block_002_push_eq (acc : List SourceJson) :
    geometryFacesBlock002Push acc = [geometryFacesJson012, geometryFacesJson011, geometryFacesJson010, geometryFacesJson009] ++ acc := by rfl

theorem geometry_Faces_block_002_reverse (acc : List SourceJson) :
    (geometryFacesBlock002Push acc).reverse = acc.reverse ++ geometryFacesJsonBlock002 := by
  rw [geometry_Faces_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_002 :
    geometryFacesJsonBlock002.mapM decodeFace = .ok geometryFacesTypedBlock002 := by
  simp only [geometryFacesJsonBlock002, geometryFacesTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_009, decode_geometry_Faces_010, decode_geometry_Faces_011, decode_geometry_Faces_012]
  rfl

noncomputable def geometryFacesTypedThroughBlock002 : List (FaceRecord) := geometryFacesTypedThroughBlock001 ++ geometryFacesTypedBlock002

theorem decode_geometry_Faces_through_block_002 :
    faceLedgerArrayAcc01200.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock002 := by
  change (geometryFacesBlock002Push faceLedgerArrayAcc00800).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_002_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_001, decode_geometry_Faces_block_002]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_block_002_complete"
  err.flush

#print axioms decode_geometry_Faces_009
#print axioms geometry_Faces_chunk_008_push_eq
#print axioms decode_geometry_Faces_010
#print axioms geometry_Faces_chunk_009_push_eq
#print axioms decode_geometry_Faces_011
#print axioms geometry_Faces_chunk_010_push_eq
#print axioms decode_geometry_Faces_012
#print axioms geometry_Faces_chunk_011_push_eq
#print axioms geometry_Faces_block_002_push_eq
#print axioms geometry_Faces_block_002_reverse
#print axioms decode_geometry_Faces_block_002
#print axioms decode_geometry_Faces_through_block_002

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
