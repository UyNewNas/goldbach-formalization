import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces001

/-! Original face_ledger typed block 2, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson003 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped003 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35],
    dimension := 7, pivot := 35,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 25, 26, 27, 28, 29], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 25, 26, 28, 32, 33, 34, 35], #[0, 1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27, 29, 32, 33, 34, 35], #[0, 1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 22, 23, 24, 26, 27, 28, 29, 32, 33, 34, 35], #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24], #[0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 21, 22, 23, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35], #[0, 2, 4, 6, 7, 9, 12, 14, 15, 17, 18, 19, 22, 26, 27, 33, 35], #[1, 3, 5, 8, 10, 11, 13, 16, 20, 21, 23, 24, 25, 28, 29, 32, 34], #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35], #[4, 5, 12, 13, 17, 25, 26, 27, 28, 29, 34, 35], #[14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 32, 33]],
    simplices := 77 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_003_before_decode"
  err.flush

theorem decode_geometry_Faces_003 :
    decodeFace geometryFacesJson003 = .ok geometryFacesTyped003 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_003_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock002 : List SourceJson := [geometryFacesJson003]
noncomputable def geometryFacesTypedBlock002 : List (FaceRecord) := [geometryFacesTyped003]
noncomputable def geometryFacesTypedThroughBlock002 : List (FaceRecord) := geometryFacesTypedThroughBlock001 ++ geometryFacesTypedBlock002

theorem geometry_Faces_block_002_push_eq (acc : List SourceJson) :
    FaceLedgerBlock002.blockPush acc = [geometryFacesJson003] ++ acc := by rfl

theorem geometry_Faces_block_002_reverse (acc : List SourceJson) :
    (FaceLedgerBlock002.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock002 := by
  rw [geometry_Faces_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_002 :
    geometryFacesJsonBlock002.mapM decodeFace = .ok geometryFacesTypedBlock002 := by
  simp only [geometryFacesJsonBlock002, geometryFacesTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_003]
  rfl

theorem decode_geometry_Faces_through_block_002 :
    FaceLedgerValue.arrayAcc003.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock002 := by
  change (FaceLedgerBlock002.blockPush FaceLedgerValue.arrayAcc002).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_002_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_001, decode_geometry_Faces_block_002]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_002_complete"
  err.flush

#print axioms decode_geometry_Faces_003
#print axioms geometry_Faces_block_002_push_eq
#print axioms geometry_Faces_block_002_reverse
#print axioms decode_geometry_Faces_block_002
#print axioms decode_geometry_Faces_through_block_002

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
