import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces002

/-! Original face_ledger typed block 3, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson004 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped004 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 25, 26, 27, 28, 29],
    dimension := 6, pivot := 29,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 17, 25, 26, 28], #[0, 1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 13, 17, 25, 27, 29], #[0, 1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 26, 27, 28, 29], #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11], #[0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 17, 25, 26, 27, 28, 29], #[0, 2, 4, 6, 7, 9, 12, 17, 26, 27], #[1, 3, 5, 8, 10, 11, 13, 25, 28, 29], #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 17, 25, 26, 27, 28, 29], #[4, 5, 12, 13, 17, 25, 26, 27, 28, 29]],
    simplices := 30 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_004_before_decode"
  err.flush

theorem decode_geometry_Faces_004 :
    decodeFace geometryFacesJson004 = .ok geometryFacesTyped004 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_004_decoded"
  err.flush

noncomputable def geometryFacesJson005 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped005 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 17, 25, 26, 28],
    dimension := 5, pivot := 28,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 8, 12, 13, 17, 25], #[0, 1, 2, 3, 4, 5, 7, 10, 12, 13, 26, 28], #[0, 1, 2, 3, 6, 7, 8, 10], #[0, 1, 6, 7, 8, 10, 12, 13, 17, 25, 26, 28], #[0, 2, 4, 6, 7, 12, 17, 26], #[1, 3, 5, 8, 10, 13, 25, 28], #[2, 3, 4, 5, 6, 7, 8, 10, 17, 25, 26, 28], #[4, 5, 12, 13, 17, 25, 26, 28]],
    simplices := 20 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_005_before_decode"
  err.flush

theorem decode_geometry_Faces_005 :
    decodeFace geometryFacesJson005 = .ok geometryFacesTyped005 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_005_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock003 : List SourceJson := [geometryFacesJson004, geometryFacesJson005]
noncomputable def geometryFacesTypedBlock003 : List (FaceRecord) := [geometryFacesTyped004, geometryFacesTyped005]
noncomputable def geometryFacesTypedThroughBlock003 : List (FaceRecord) := geometryFacesTypedThroughBlock002 ++ geometryFacesTypedBlock003

theorem geometry_Faces_block_003_push_eq (acc : List SourceJson) :
    FaceLedgerBlock003.blockPush acc = [geometryFacesJson005, geometryFacesJson004] ++ acc := by rfl

theorem geometry_Faces_block_003_reverse (acc : List SourceJson) :
    (FaceLedgerBlock003.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock003 := by
  rw [geometry_Faces_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_003 :
    geometryFacesJsonBlock003.mapM decodeFace = .ok geometryFacesTypedBlock003 := by
  simp only [geometryFacesJsonBlock003, geometryFacesTypedBlock003, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_004, decode_geometry_Faces_005]
  rfl

theorem decode_geometry_Faces_through_block_003 :
    FaceLedgerValue.arrayAcc004.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock003 := by
  change (FaceLedgerBlock003.blockPush FaceLedgerValue.arrayAcc003).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_003_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_002, decode_geometry_Faces_block_003]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_003_complete"
  err.flush

#print axioms decode_geometry_Faces_004
#print axioms decode_geometry_Faces_005
#print axioms geometry_Faces_block_003_push_eq
#print axioms geometry_Faces_block_003_reverse
#print axioms decode_geometry_Faces_block_003
#print axioms decode_geometry_Faces_through_block_003

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
