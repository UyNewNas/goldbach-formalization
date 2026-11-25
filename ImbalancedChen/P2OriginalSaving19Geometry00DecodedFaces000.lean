import ImbalancedChen.P2OriginalSaving19ArchiveSchema
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00000

/-! Actual original face_ledger typed block 0; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryFacesJson000 : SourceJson :=
  (faceLedgerChunk000Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped000 : FaceRecord :=
  { vertices := #[0, 1],
    dimension := 1, pivot := 1,
    facetSets := #[#[0], #[1]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_000_before_decode"
  err.flush

theorem decode_geometry_Faces_000 :
    decodeFace geometryFacesJson000 = .ok geometryFacesTyped000 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_000_decoded"
  err.flush

noncomputable def geometryFacesJson001 : SourceJson :=
  (faceLedgerChunk000Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped001 : FaceRecord :=
  { vertices := #[0, 1, 2, 3],
    dimension := 2, pivot := 3,
    facetSets := #[#[0, 1], #[0, 2], #[1, 3], #[2, 3]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_001_before_decode"
  err.flush

theorem decode_geometry_Faces_001 :
    decodeFace geometryFacesJson001 = .ok geometryFacesTyped001 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_001_decoded"
  err.flush

theorem geometry_Faces_chunk_000_push_eq (acc : List SourceJson) :
    faceLedgerChunk000Push00 acc = [geometryFacesJson001, geometryFacesJson000] ++ acc := by rfl

noncomputable def geometryFacesJson002 : SourceJson :=
  (faceLedgerChunk001Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped002 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5],
    dimension := 3, pivot := 5,
    facetSets := #[#[0, 1, 2, 3], #[0, 1, 4, 5], #[0, 2, 4], #[1, 3, 5], #[2, 3, 4, 5]],
    simplices := 3 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_002_before_decode"
  err.flush

theorem decode_geometry_Faces_002 :
    decodeFace geometryFacesJson002 = .ok geometryFacesTyped002 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_002_decoded"
  err.flush

theorem geometry_Faces_chunk_001_push_eq (acc : List SourceJson) :
    faceLedgerChunk001Push00 acc = [geometryFacesJson002] ++ acc := by rfl

noncomputable def geometryFacesJson003 : SourceJson :=
  (faceLedgerChunk002Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped003 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7],
    dimension := 4, pivot := 7,
    facetSets := #[#[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 6, 7], #[0, 1, 4, 5, 6, 7], #[0, 2, 4, 7], #[1, 3, 5, 6], #[2, 3, 4, 5, 6, 7]],
    simplices := 4 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_003_before_decode"
  err.flush

theorem decode_geometry_Faces_003 :
    decodeFace geometryFacesJson003 = .ok geometryFacesTyped003 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_003_decoded"
  err.flush

theorem geometry_Faces_chunk_002_push_eq (acc : List SourceJson) :
    faceLedgerChunk002Push00 acc = [geometryFacesJson003] ++ acc := by rfl

noncomputable def geometryFacesJson004 : SourceJson :=
  (faceLedgerChunk003Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped004 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    dimension := 5, pivot := 9,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 8, 9], #[0, 1, 2, 3, 6, 7, 8, 9], #[0, 1, 4, 5, 6, 7, 8, 9], #[0, 2, 4, 7, 9], #[1, 3, 5, 6, 8], #[2, 3, 4, 5, 6, 7, 8, 9]],
    simplices := 5 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_004_before_decode"
  err.flush

theorem decode_geometry_Faces_004 :
    decodeFace geometryFacesJson004 = .ok geometryFacesTyped004 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_004_decoded"
  err.flush

theorem geometry_Faces_chunk_003_push_eq (acc : List SourceJson) :
    faceLedgerChunk003Push00 acc = [geometryFacesJson004] ++ acc := by rfl

noncomputable def geometryFacesJsonBlock000 : List SourceJson := [geometryFacesJson000, geometryFacesJson001, geometryFacesJson002, geometryFacesJson003, geometryFacesJson004]
noncomputable def geometryFacesTypedBlock000 : List (FaceRecord) := [geometryFacesTyped000, geometryFacesTyped001, geometryFacesTyped002, geometryFacesTyped003, geometryFacesTyped004]
noncomputable def geometryFacesBlock000Push (acc : List SourceJson) : List SourceJson := faceLedgerChunk003Push00 (faceLedgerChunk002Push00 (faceLedgerChunk001Push00 (faceLedgerChunk000Push00 (acc))))

theorem geometry_Faces_block_000_push_eq (acc : List SourceJson) :
    geometryFacesBlock000Push acc = [geometryFacesJson004, geometryFacesJson003, geometryFacesJson002, geometryFacesJson001, geometryFacesJson000] ++ acc := by rfl

theorem geometry_Faces_block_000_reverse (acc : List SourceJson) :
    (geometryFacesBlock000Push acc).reverse = acc.reverse ++ geometryFacesJsonBlock000 := by
  rw [geometry_Faces_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_000 :
    geometryFacesJsonBlock000.mapM decodeFace = .ok geometryFacesTypedBlock000 := by
  simp only [geometryFacesJsonBlock000, geometryFacesTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_000, decode_geometry_Faces_001, decode_geometry_Faces_002, decode_geometry_Faces_003, decode_geometry_Faces_004]
  rfl

noncomputable def geometryFacesTypedThroughBlock000 : List (FaceRecord) := geometryFacesTypedBlock000

theorem decode_geometry_Faces_through_block_000 :
    faceLedgerArrayAcc00400.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock000 := by
  change (geometryFacesBlock000Push faceLedgerArrayAcc00000).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_000_reverse]
  exact decode_geometry_Faces_block_000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_block_000_complete"
  err.flush

#print axioms decode_geometry_Faces_000
#print axioms decode_geometry_Faces_001
#print axioms geometry_Faces_chunk_000_push_eq
#print axioms decode_geometry_Faces_002
#print axioms geometry_Faces_chunk_001_push_eq
#print axioms decode_geometry_Faces_003
#print axioms geometry_Faces_chunk_002_push_eq
#print axioms decode_geometry_Faces_004
#print axioms geometry_Faces_chunk_003_push_eq
#print axioms geometry_Faces_block_000_push_eq
#print axioms geometry_Faces_block_000_reverse
#print axioms decode_geometry_Faces_block_000
#print axioms decode_geometry_Faces_through_block_000

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
