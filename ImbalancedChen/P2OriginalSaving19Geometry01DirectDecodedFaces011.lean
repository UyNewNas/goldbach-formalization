import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces010

/-! Original face_ledger typed block 11, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson037 : SourceJson :=
  (FaceLedgerBlock011.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped037 : FaceRecord :=
  { vertices := #[1, 3, 5, 8, 10, 11, 13, 16, 20, 21, 23, 24, 25, 28, 29, 30, 32, 34, 36, 38],
    dimension := 7, pivot := 38,
    facetSets := #[#[1, 3, 5, 8, 10, 11, 13, 16, 20, 21, 23, 24, 25, 28, 29, 32, 34], #[1, 3, 5, 8, 10, 11, 13, 25, 28, 29, 36, 38], #[1, 3, 5, 8, 10, 13, 16, 20, 21, 23, 25, 28, 30, 32, 34, 36, 38], #[1, 3, 5, 8, 11, 13, 16, 20, 21, 24, 25, 29, 30, 32, 34, 36, 38], #[1, 3, 5, 10, 11, 13, 16, 20, 23, 24, 28, 29, 30, 32, 34, 36, 38], #[1, 3, 8, 10, 11, 16, 20, 21, 23, 24, 30, 36], #[1, 8, 10, 11, 13, 16, 21, 23, 24, 25, 28, 29, 30, 32, 34, 36, 38], #[3, 5, 8, 10, 11, 20, 21, 23, 24, 25, 28, 29, 30, 32, 34, 36, 38], #[5, 13, 25, 28, 29, 34, 38], #[16, 20, 21, 23, 24, 30, 32]],
    simplices := 18 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_037_before_decode"
  err.flush

theorem decode_geometry_Faces_037 :
    decodeFace geometryFacesJson037 = .ok geometryFacesTyped037 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_037_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock011 : List SourceJson := [geometryFacesJson037]
noncomputable def geometryFacesTypedBlock011 : List (FaceRecord) := [geometryFacesTyped037]
noncomputable def geometryFacesTypedThroughBlock011 : List (FaceRecord) := geometryFacesTypedThroughBlock010 ++ geometryFacesTypedBlock011

theorem geometry_Faces_block_011_push_eq (acc : List SourceJson) :
    FaceLedgerBlock011.blockPush acc = [geometryFacesJson037] ++ acc := by rfl

theorem geometry_Faces_block_011_reverse (acc : List SourceJson) :
    (FaceLedgerBlock011.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock011 := by
  rw [geometry_Faces_block_011_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_011 :
    geometryFacesJsonBlock011.mapM decodeFace = .ok geometryFacesTypedBlock011 := by
  simp only [geometryFacesJsonBlock011, geometryFacesTypedBlock011, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_037]
  rfl

theorem decode_geometry_Faces_through_block_011 :
    FaceLedgerValue.arrayAcc012.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock011 := by
  change (FaceLedgerBlock011.blockPush FaceLedgerValue.arrayAcc011).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_011_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_010, decode_geometry_Faces_block_011]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_011_complete"
  err.flush

#print axioms decode_geometry_Faces_037
#print axioms geometry_Faces_block_011_push_eq
#print axioms geometry_Faces_block_011_reverse
#print axioms decode_geometry_Faces_block_011
#print axioms decode_geometry_Faces_through_block_011

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
