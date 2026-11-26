import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces004

/-! Original face_ledger typed block 5, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson009 : SourceJson :=
  (FaceLedgerBlock005.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped009 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24],
    dimension := 6, pivot := 24,
    facetSets := #[#[0, 1, 2, 3, 6, 7, 8, 9, 10, 11], #[0, 1, 2, 3, 6, 7, 8, 10, 14, 15, 16, 18, 19, 20, 21, 23], #[0, 1, 2, 3, 6, 8, 9, 11, 15, 16, 18, 19, 20, 21, 22, 24], #[0, 1, 2, 3, 7, 9, 10, 11, 14, 15, 16, 19, 20, 22, 23, 24], #[0, 1, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 21, 22, 23, 24], #[0, 2, 6, 7, 9, 14, 15, 18, 19, 22], #[1, 3, 8, 10, 11, 16, 20, 21, 23, 24], #[2, 3, 6, 7, 8, 9, 10, 11, 14, 18, 19, 20, 21, 22, 23, 24], #[14, 15, 16, 18, 19, 20, 21, 22, 23, 24]],
    simplices := 30 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_009_before_decode"
  err.flush

theorem decode_geometry_Faces_009 :
    decodeFace geometryFacesJson009 = .ok geometryFacesTyped009 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_009_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock005 : List SourceJson := [geometryFacesJson009]
noncomputable def geometryFacesTypedBlock005 : List (FaceRecord) := [geometryFacesTyped009]
noncomputable def geometryFacesTypedThroughBlock005 : List (FaceRecord) := geometryFacesTypedThroughBlock004 ++ geometryFacesTypedBlock005

theorem geometry_Faces_block_005_push_eq (acc : List SourceJson) :
    FaceLedgerBlock005.blockPush acc = [geometryFacesJson009] ++ acc := by rfl

theorem geometry_Faces_block_005_reverse (acc : List SourceJson) :
    (FaceLedgerBlock005.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock005 := by
  rw [geometry_Faces_block_005_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_005 :
    geometryFacesJsonBlock005.mapM decodeFace = .ok geometryFacesTypedBlock005 := by
  simp only [geometryFacesJsonBlock005, geometryFacesTypedBlock005, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_009]
  rfl

theorem decode_geometry_Faces_through_block_005 :
    FaceLedgerValue.arrayAcc006.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock005 := by
  change (FaceLedgerBlock005.blockPush FaceLedgerValue.arrayAcc005).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_005_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_004, decode_geometry_Faces_block_005]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_005_complete"
  err.flush

#print axioms decode_geometry_Faces_009
#print axioms geometry_Faces_block_005_push_eq
#print axioms geometry_Faces_block_005_reverse
#print axioms decode_geometry_Faces_block_005
#print axioms decode_geometry_Faces_through_block_005

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
