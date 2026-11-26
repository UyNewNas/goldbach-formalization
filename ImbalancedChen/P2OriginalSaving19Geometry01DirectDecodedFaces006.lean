import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces005

/-! Original face_ledger typed block 6, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson010 : SourceJson :=
  (FaceLedgerBlock006.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped010 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 30, 31, 36, 37],
    dimension := 7, pivot := 37,
    facetSets := #[#[0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24], #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 36, 37], #[0, 1, 2, 3, 6, 7, 8, 10, 14, 15, 16, 18, 19, 20, 21, 23, 30, 31, 36, 37], #[0, 1, 2, 3, 6, 8, 9, 11, 15, 16, 18, 19, 20, 21, 22, 24, 30, 31, 36, 37], #[0, 1, 2, 3, 7, 9, 10, 11, 14, 15, 16, 19, 20, 22, 23, 24, 30, 31, 36, 37], #[0, 1, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 21, 22, 23, 24, 30, 31, 36, 37], #[0, 2, 6, 7, 9, 14, 15, 18, 19, 22, 31, 37], #[1, 3, 8, 10, 11, 16, 20, 21, 23, 24, 30, 36], #[2, 3, 6, 7, 8, 9, 10, 11, 14, 18, 19, 20, 21, 22, 23, 24, 30, 31, 36, 37], #[14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 30, 31]],
    simplices := 42 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_010_before_decode"
  err.flush

theorem decode_geometry_Faces_010 :
    decodeFace geometryFacesJson010 = .ok geometryFacesTyped010 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_010_decoded"
  err.flush

noncomputable def geometryFacesJson011 : SourceJson :=
  (FaceLedgerBlock006.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped011 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 6, 7, 8, 10],
    dimension := 4, pivot := 10,
    facetSets := #[#[0, 1, 2, 3, 6, 8], #[0, 1, 2, 3, 7, 10], #[0, 1, 6, 7, 8, 10], #[0, 2, 6, 7], #[1, 3, 8, 10], #[2, 3, 6, 7, 8, 10]],
    simplices := 4 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_011_before_decode"
  err.flush

theorem decode_geometry_Faces_011 :
    decodeFace geometryFacesJson011 = .ok geometryFacesTyped011 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_011_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock006 : List SourceJson := [geometryFacesJson010, geometryFacesJson011]
noncomputable def geometryFacesTypedBlock006 : List (FaceRecord) := [geometryFacesTyped010, geometryFacesTyped011]
noncomputable def geometryFacesTypedThroughBlock006 : List (FaceRecord) := geometryFacesTypedThroughBlock005 ++ geometryFacesTypedBlock006

theorem geometry_Faces_block_006_push_eq (acc : List SourceJson) :
    FaceLedgerBlock006.blockPush acc = [geometryFacesJson011, geometryFacesJson010] ++ acc := by rfl

theorem geometry_Faces_block_006_reverse (acc : List SourceJson) :
    (FaceLedgerBlock006.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock006 := by
  rw [geometry_Faces_block_006_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_006 :
    geometryFacesJsonBlock006.mapM decodeFace = .ok geometryFacesTypedBlock006 := by
  simp only [geometryFacesJsonBlock006, geometryFacesTypedBlock006, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_010, decode_geometry_Faces_011]
  rfl

theorem decode_geometry_Faces_through_block_006 :
    FaceLedgerValue.arrayAcc007.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock006 := by
  change (FaceLedgerBlock006.blockPush FaceLedgerValue.arrayAcc006).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_006_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_005, decode_geometry_Faces_block_006]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_006_complete"
  err.flush

#print axioms decode_geometry_Faces_010
#print axioms decode_geometry_Faces_011
#print axioms geometry_Faces_block_006_push_eq
#print axioms geometry_Faces_block_006_reverse
#print axioms decode_geometry_Faces_block_006
#print axioms decode_geometry_Faces_through_block_006

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
