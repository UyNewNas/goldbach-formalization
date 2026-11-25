import ImbalancedChen.P2OriginalSaving19Geometry00DecodedFaces006
import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00700

/-! Actual original face_ledger typed block 7; exact original record order and fields.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryFacesJson031 : SourceJson :=
  (faceLedgerChunk028Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped031 : FaceRecord :=
  { vertices := #[1, 3, 5, 13, 18, 19],
    dimension := 3, pivot := 19,
    facetSets := #[#[1, 3, 5], #[1, 3, 13, 18], #[1, 5, 18, 19], #[3, 5, 13, 19], #[13, 18, 19]],
    simplices := 3 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_031_before_decode"
  err.flush

theorem decode_geometry_Faces_031 :
    decodeFace geometryFacesJson031 = .ok geometryFacesTyped031 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_031_decoded"
  err.flush

theorem geometry_Faces_chunk_028_push_eq (acc : List SourceJson) :
    faceLedgerChunk028Push00 acc = [geometryFacesJson031] ++ acc := by rfl

noncomputable def geometryFacesJson032 : SourceJson :=
  (faceLedgerChunk029Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped032 : FaceRecord :=
  { vertices := #[1, 3, 13, 18],
    dimension := 2, pivot := 18,
    facetSets := #[#[1, 3], #[1, 18], #[3, 13], #[13, 18]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_032_before_decode"
  err.flush

theorem decode_geometry_Faces_032 :
    decodeFace geometryFacesJson032 = .ok geometryFacesTyped032 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_032_decoded"
  err.flush

noncomputable def geometryFacesJson033 : SourceJson :=
  (faceLedgerChunk029Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped033 : FaceRecord :=
  { vertices := #[2, 3],
    dimension := 1, pivot := 3,
    facetSets := #[#[2], #[3]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_033_before_decode"
  err.flush

theorem decode_geometry_Faces_033 :
    decodeFace geometryFacesJson033 = .ok geometryFacesTyped033 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_033_decoded"
  err.flush

theorem geometry_Faces_chunk_029_push_eq (acc : List SourceJson) :
    faceLedgerChunk029Push00 acc = [geometryFacesJson033, geometryFacesJson032] ++ acc := by rfl

noncomputable def geometryFacesJson034 : SourceJson :=
  (faceLedgerChunk030Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped034 : FaceRecord :=
  { vertices := #[2, 3, 12, 13],
    dimension := 2, pivot := 13,
    facetSets := #[#[2, 3], #[2, 12], #[3, 13], #[12, 13]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_034_before_decode"
  err.flush

theorem decode_geometry_Faces_034 :
    decodeFace geometryFacesJson034 = .ok geometryFacesTyped034 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_034_decoded"
  err.flush

noncomputable def geometryFacesJson035 : SourceJson :=
  (faceLedgerChunk030Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped035 : FaceRecord :=
  { vertices := #[2, 4],
    dimension := 1, pivot := 4,
    facetSets := #[#[2], #[4]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_035_before_decode"
  err.flush

theorem decode_geometry_Faces_035 :
    decodeFace geometryFacesJson035 = .ok geometryFacesTyped035 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_035_decoded"
  err.flush

theorem geometry_Faces_chunk_030_push_eq (acc : List SourceJson) :
    faceLedgerChunk030Push00 acc = [geometryFacesJson035, geometryFacesJson034] ++ acc := by rfl

noncomputable def geometryFacesJson036 : SourceJson :=
  (faceLedgerChunk031Push00 []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped036 : FaceRecord :=
  { vertices := #[2, 4, 12, 16],
    dimension := 2, pivot := 16,
    facetSets := #[#[2, 4], #[2, 12], #[4, 16], #[12, 16]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_036_before_decode"
  err.flush

theorem decode_geometry_Faces_036 :
    decodeFace geometryFacesJson036 = .ok geometryFacesTyped036 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_036_decoded"
  err.flush

noncomputable def geometryFacesJson037 : SourceJson :=
  (faceLedgerChunk031Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped037 : FaceRecord :=
  { vertices := #[2, 12],
    dimension := 1, pivot := 12,
    facetSets := #[#[2], #[12]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_037_before_decode"
  err.flush

theorem decode_geometry_Faces_037 :
    decodeFace geometryFacesJson037 = .ok geometryFacesTyped037 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_record_037_decoded"
  err.flush

theorem geometry_Faces_chunk_031_push_eq (acc : List SourceJson) :
    faceLedgerChunk031Push00 acc = [geometryFacesJson037, geometryFacesJson036] ++ acc := by rfl

noncomputable def geometryFacesJsonBlock007 : List SourceJson := [geometryFacesJson031, geometryFacesJson032, geometryFacesJson033, geometryFacesJson034, geometryFacesJson035, geometryFacesJson036, geometryFacesJson037]
noncomputable def geometryFacesTypedBlock007 : List (FaceRecord) := [geometryFacesTyped031, geometryFacesTyped032, geometryFacesTyped033, geometryFacesTyped034, geometryFacesTyped035, geometryFacesTyped036, geometryFacesTyped037]
noncomputable def geometryFacesBlock007Push (acc : List SourceJson) : List SourceJson := faceLedgerChunk031Push00 (faceLedgerChunk030Push00 (faceLedgerChunk029Push00 (faceLedgerChunk028Push00 (acc))))

theorem geometry_Faces_block_007_push_eq (acc : List SourceJson) :
    geometryFacesBlock007Push acc = [geometryFacesJson037, geometryFacesJson036, geometryFacesJson035, geometryFacesJson034, geometryFacesJson033, geometryFacesJson032, geometryFacesJson031] ++ acc := by rfl

theorem geometry_Faces_block_007_reverse (acc : List SourceJson) :
    (geometryFacesBlock007Push acc).reverse = acc.reverse ++ geometryFacesJsonBlock007 := by
  rw [geometry_Faces_block_007_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_007 :
    geometryFacesJsonBlock007.mapM decodeFace = .ok geometryFacesTypedBlock007 := by
  simp only [geometryFacesJsonBlock007, geometryFacesTypedBlock007, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_031, decode_geometry_Faces_032, decode_geometry_Faces_033, decode_geometry_Faces_034, decode_geometry_Faces_035, decode_geometry_Faces_036, decode_geometry_Faces_037]
  rfl

noncomputable def geometryFacesTypedThroughBlock007 : List (FaceRecord) := geometryFacesTypedThroughBlock006 ++ geometryFacesTypedBlock007

theorem decode_geometry_Faces_through_block_007 :
    faceLedgerArrayAcc03200.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock007 := by
  change (geometryFacesBlock007Push faceLedgerArrayAcc02800).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_007_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_006, decode_geometry_Faces_block_007]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Faces_block_007_complete"
  err.flush

#print axioms decode_geometry_Faces_031
#print axioms geometry_Faces_chunk_028_push_eq
#print axioms decode_geometry_Faces_032
#print axioms decode_geometry_Faces_033
#print axioms geometry_Faces_chunk_029_push_eq
#print axioms decode_geometry_Faces_034
#print axioms decode_geometry_Faces_035
#print axioms geometry_Faces_chunk_030_push_eq
#print axioms decode_geometry_Faces_036
#print axioms decode_geometry_Faces_037
#print axioms geometry_Faces_chunk_031_push_eq
#print axioms geometry_Faces_block_007_push_eq
#print axioms geometry_Faces_block_007_reverse
#print axioms decode_geometry_Faces_block_007
#print axioms decode_geometry_Faces_through_block_007

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
