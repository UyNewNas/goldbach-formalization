import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces003

/-! Original face_ledger typed block 4, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson006 : SourceJson :=
  (FaceLedgerBlock004.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped006 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 8, 12, 13, 17, 25],
    dimension := 4, pivot := 25,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 12, 13], #[0, 1, 2, 3, 6, 8], #[0, 1, 6, 8, 12, 13, 17, 25], #[0, 2, 4, 6, 12, 17], #[1, 3, 5, 8, 13, 25], #[2, 3, 4, 5, 6, 8, 17, 25], #[4, 5, 12, 13, 17, 25]],
    simplices := 12 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_006_before_decode"
  err.flush

theorem decode_geometry_Faces_006 :
    decodeFace geometryFacesJson006 = .ok geometryFacesTyped006 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_006_decoded"
  err.flush

noncomputable def geometryFacesJson007 : SourceJson :=
  (FaceLedgerBlock004.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped007 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 12, 13],
    dimension := 3, pivot := 13,
    facetSets := #[#[0, 1, 2, 3], #[0, 1, 12, 13], #[0, 2, 4, 12], #[1, 3, 5, 13], #[2, 3, 4, 5], #[4, 5, 12, 13]],
    simplices := 6 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_007_before_decode"
  err.flush

theorem decode_geometry_Faces_007 :
    decodeFace geometryFacesJson007 = .ok geometryFacesTyped007 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_007_decoded"
  err.flush

noncomputable def geometryFacesJson008 : SourceJson :=
  (FaceLedgerBlock004.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped008 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11],
    dimension := 5, pivot := 11,
    facetSets := #[#[0, 1, 2, 3, 6, 7, 8, 10], #[0, 1, 2, 3, 6, 8, 9, 11], #[0, 1, 2, 3, 7, 9, 10, 11], #[0, 1, 6, 7, 8, 9, 10, 11], #[0, 2, 6, 7, 9], #[1, 3, 8, 10, 11], #[2, 3, 6, 7, 8, 9, 10, 11]],
    simplices := 5 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_008_before_decode"
  err.flush

theorem decode_geometry_Faces_008 :
    decodeFace geometryFacesJson008 = .ok geometryFacesTyped008 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_008_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock004 : List SourceJson := [geometryFacesJson006, geometryFacesJson007, geometryFacesJson008]
noncomputable def geometryFacesTypedBlock004 : List (FaceRecord) := [geometryFacesTyped006, geometryFacesTyped007, geometryFacesTyped008]
noncomputable def geometryFacesTypedThroughBlock004 : List (FaceRecord) := geometryFacesTypedThroughBlock003 ++ geometryFacesTypedBlock004

theorem geometry_Faces_block_004_push_eq (acc : List SourceJson) :
    FaceLedgerBlock004.blockPush acc = [geometryFacesJson008, geometryFacesJson007, geometryFacesJson006] ++ acc := by rfl

theorem geometry_Faces_block_004_reverse (acc : List SourceJson) :
    (FaceLedgerBlock004.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock004 := by
  rw [geometry_Faces_block_004_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_004 :
    geometryFacesJsonBlock004.mapM decodeFace = .ok geometryFacesTypedBlock004 := by
  simp only [geometryFacesJsonBlock004, geometryFacesTypedBlock004, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_006, decode_geometry_Faces_007, decode_geometry_Faces_008]
  rfl

theorem decode_geometry_Faces_through_block_004 :
    FaceLedgerValue.arrayAcc005.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock004 := by
  change (FaceLedgerBlock004.blockPush FaceLedgerValue.arrayAcc004).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_004_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_003, decode_geometry_Faces_block_004]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_004_complete"
  err.flush

#print axioms decode_geometry_Faces_006
#print axioms decode_geometry_Faces_007
#print axioms decode_geometry_Faces_008
#print axioms geometry_Faces_block_004_push_eq
#print axioms geometry_Faces_block_004_reverse
#print axioms decode_geometry_Faces_block_004
#print axioms decode_geometry_Faces_through_block_004

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
