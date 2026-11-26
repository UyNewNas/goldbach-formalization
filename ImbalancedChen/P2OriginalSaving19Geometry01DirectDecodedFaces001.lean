import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces000

/-! Original face_ledger typed block 1, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson002 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped002 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39],
    dimension := 8, pivot := 39,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 25, 26, 27, 28, 29, 36, 37, 38, 39], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 25, 26, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39], #[0, 1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39], #[0, 1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39], #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 30, 31, 36, 37], #[0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39], #[0, 2, 4, 6, 7, 9, 12, 14, 15, 17, 18, 19, 22, 26, 27, 31, 33, 35, 37, 39], #[1, 3, 5, 8, 10, 11, 13, 16, 20, 21, 23, 24, 25, 28, 29, 30, 32, 34, 36, 38], #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39], #[4, 5, 12, 13, 17, 25, 26, 27, 28, 29, 34, 35, 38, 39], #[14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 30, 31, 32, 33]],
    simplices := 144 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_002_before_decode"
  err.flush

theorem decode_geometry_Faces_002 :
    decodeFace geometryFacesJson002 = .ok geometryFacesTyped002 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_002_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock001 : List SourceJson := [geometryFacesJson002]
noncomputable def geometryFacesTypedBlock001 : List (FaceRecord) := [geometryFacesTyped002]
noncomputable def geometryFacesTypedThroughBlock001 : List (FaceRecord) := geometryFacesTypedThroughBlock000 ++ geometryFacesTypedBlock001

theorem geometry_Faces_block_001_push_eq (acc : List SourceJson) :
    FaceLedgerBlock001.blockPush acc = [geometryFacesJson002] ++ acc := by rfl

theorem geometry_Faces_block_001_reverse (acc : List SourceJson) :
    (FaceLedgerBlock001.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock001 := by
  rw [geometry_Faces_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_001 :
    geometryFacesJsonBlock001.mapM decodeFace = .ok geometryFacesTypedBlock001 := by
  simp only [geometryFacesJsonBlock001, geometryFacesTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_002]
  rfl

theorem decode_geometry_Faces_through_block_001 :
    FaceLedgerValue.arrayAcc002.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock001 := by
  change (FaceLedgerBlock001.blockPush FaceLedgerValue.arrayAcc001).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_001_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_000, decode_geometry_Faces_block_001]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_001_complete"
  err.flush

#print axioms decode_geometry_Faces_002
#print axioms geometry_Faces_block_001_push_eq
#print axioms geometry_Faces_block_001_reverse
#print axioms decode_geometry_Faces_block_001
#print axioms decode_geometry_Faces_through_block_001

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
