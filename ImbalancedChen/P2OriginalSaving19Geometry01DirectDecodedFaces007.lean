import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces006

/-! Original face_ledger typed block 7, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson012 : SourceJson :=
  (FaceLedgerBlock007.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped012 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 6, 7, 8, 10, 14, 15, 16, 18, 19, 20, 21, 23],
    dimension := 5, pivot := 23,
    facetSets := #[#[0, 1, 2, 3, 6, 7, 8, 10], #[0, 1, 2, 3, 6, 8, 15, 16, 18, 19, 20, 21], #[0, 1, 2, 3, 7, 10, 14, 15, 16, 19, 20, 23], #[0, 1, 6, 7, 8, 10, 14, 15, 16, 18, 21, 23], #[0, 2, 6, 7, 14, 15, 18, 19], #[1, 3, 8, 10, 16, 20, 21, 23], #[2, 3, 6, 7, 8, 10, 14, 18, 19, 20, 21, 23], #[14, 15, 16, 18, 19, 20, 21, 23]],
    simplices := 20 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_012_before_decode"
  err.flush

theorem decode_geometry_Faces_012 :
    decodeFace geometryFacesJson012 = .ok geometryFacesTyped012 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_012_decoded"
  err.flush

noncomputable def geometryFacesJson013 : SourceJson :=
  (FaceLedgerBlock007.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped013 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 6, 8],
    dimension := 3, pivot := 8,
    facetSets := #[#[0, 1, 2, 3], #[0, 1, 6, 8], #[0, 2, 6], #[1, 3, 8], #[2, 3, 6, 8]],
    simplices := 3 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_013_before_decode"
  err.flush

theorem decode_geometry_Faces_013 :
    decodeFace geometryFacesJson013 = .ok geometryFacesTyped013 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_013_decoded"
  err.flush

noncomputable def geometryFacesJson014 : SourceJson :=
  (FaceLedgerBlock007.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped014 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 6, 8, 15, 16, 18, 19, 20, 21],
    dimension := 4, pivot := 21,
    facetSets := #[#[0, 1, 2, 3, 6, 8], #[0, 1, 2, 3, 15, 16, 19, 20], #[0, 1, 6, 8, 15, 16, 18, 21], #[0, 2, 6, 15, 18, 19], #[1, 3, 8, 16, 20, 21], #[2, 3, 6, 8, 18, 19, 20, 21], #[15, 16, 18, 19, 20, 21]],
    simplices := 12 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_014_before_decode"
  err.flush

theorem decode_geometry_Faces_014 :
    decodeFace geometryFacesJson014 = .ok geometryFacesTyped014 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_014_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock007 : List SourceJson := [geometryFacesJson012, geometryFacesJson013, geometryFacesJson014]
noncomputable def geometryFacesTypedBlock007 : List (FaceRecord) := [geometryFacesTyped012, geometryFacesTyped013, geometryFacesTyped014]
noncomputable def geometryFacesTypedThroughBlock007 : List (FaceRecord) := geometryFacesTypedThroughBlock006 ++ geometryFacesTypedBlock007

theorem geometry_Faces_block_007_push_eq (acc : List SourceJson) :
    FaceLedgerBlock007.blockPush acc = [geometryFacesJson014, geometryFacesJson013, geometryFacesJson012] ++ acc := by rfl

theorem geometry_Faces_block_007_reverse (acc : List SourceJson) :
    (FaceLedgerBlock007.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock007 := by
  rw [geometry_Faces_block_007_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_007 :
    geometryFacesJsonBlock007.mapM decodeFace = .ok geometryFacesTypedBlock007 := by
  simp only [geometryFacesJsonBlock007, geometryFacesTypedBlock007, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_012, decode_geometry_Faces_013, decode_geometry_Faces_014]
  rfl

theorem decode_geometry_Faces_through_block_007 :
    FaceLedgerValue.arrayAcc008.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock007 := by
  change (FaceLedgerBlock007.blockPush FaceLedgerValue.arrayAcc007).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_007_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_006, decode_geometry_Faces_block_007]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_007_complete"
  err.flush

#print axioms decode_geometry_Faces_012
#print axioms decode_geometry_Faces_013
#print axioms decode_geometry_Faces_014
#print axioms geometry_Faces_block_007_push_eq
#print axioms geometry_Faces_block_007_reverse
#print axioms decode_geometry_Faces_block_007
#print axioms decode_geometry_Faces_through_block_007

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
