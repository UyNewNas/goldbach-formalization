import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces011

/-! Original face_ledger typed block 12, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson038 : SourceJson :=
  (FaceLedgerBlock012.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped038 : FaceRecord :=
  { vertices := #[1, 3, 5, 8, 10, 11, 13, 16, 20, 21, 23, 24, 25, 28, 29, 32, 34],
    dimension := 6, pivot := 34,
    facetSets := #[#[1, 3, 5, 8, 10, 11, 13, 25, 28, 29], #[1, 3, 5, 8, 10, 13, 16, 20, 21, 23, 25, 28, 32, 34], #[1, 3, 5, 8, 11, 13, 16, 20, 21, 24, 25, 29, 32, 34], #[1, 3, 5, 10, 11, 13, 16, 20, 23, 24, 28, 29, 32, 34], #[1, 3, 8, 10, 11, 16, 20, 21, 23, 24], #[1, 8, 10, 11, 13, 16, 21, 23, 24, 25, 28, 29, 32, 34], #[3, 5, 8, 10, 11, 20, 21, 23, 24, 25, 28, 29, 32, 34], #[5, 13, 25, 28, 29, 34], #[16, 20, 21, 23, 24, 32]],
    simplices := 11 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_038_before_decode"
  err.flush

theorem decode_geometry_Faces_038 :
    decodeFace geometryFacesJson038 = .ok geometryFacesTyped038 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_038_decoded"
  err.flush

noncomputable def geometryFacesJson039 : SourceJson :=
  (FaceLedgerBlock012.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped039 : FaceRecord :=
  { vertices := #[1, 3, 5, 8, 10, 11, 13, 25, 28, 29],
    dimension := 5, pivot := 29,
    facetSets := #[#[1, 3, 5, 8, 10, 13, 25, 28], #[1, 3, 5, 8, 11, 13, 25, 29], #[1, 3, 5, 10, 11, 13, 28, 29], #[1, 3, 8, 10, 11], #[1, 8, 10, 11, 13, 25, 28, 29], #[3, 5, 8, 10, 11, 25, 28, 29], #[5, 13, 25, 28, 29]],
    simplices := 5 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_039_before_decode"
  err.flush

theorem decode_geometry_Faces_039 :
    decodeFace geometryFacesJson039 = .ok geometryFacesTyped039 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_039_decoded"
  err.flush

noncomputable def geometryFacesJson040 : SourceJson :=
  (FaceLedgerBlock012.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped040 : FaceRecord :=
  { vertices := #[1, 3, 5, 8, 10, 13, 25, 28],
    dimension := 4, pivot := 28,
    facetSets := #[#[1, 3, 5, 8, 13, 25], #[1, 3, 5, 10, 13, 28], #[1, 3, 8, 10], #[1, 8, 10, 13, 25, 28], #[3, 5, 8, 10, 25, 28], #[5, 13, 25, 28]],
    simplices := 4 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_040_before_decode"
  err.flush

theorem decode_geometry_Faces_040 :
    decodeFace geometryFacesJson040 = .ok geometryFacesTyped040 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_040_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock012 : List SourceJson := [geometryFacesJson038, geometryFacesJson039, geometryFacesJson040]
noncomputable def geometryFacesTypedBlock012 : List (FaceRecord) := [geometryFacesTyped038, geometryFacesTyped039, geometryFacesTyped040]
noncomputable def geometryFacesTypedThroughBlock012 : List (FaceRecord) := geometryFacesTypedThroughBlock011 ++ geometryFacesTypedBlock012

theorem geometry_Faces_block_012_push_eq (acc : List SourceJson) :
    FaceLedgerBlock012.blockPush acc = [geometryFacesJson040, geometryFacesJson039, geometryFacesJson038] ++ acc := by rfl

theorem geometry_Faces_block_012_reverse (acc : List SourceJson) :
    (FaceLedgerBlock012.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock012 := by
  rw [geometry_Faces_block_012_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_012 :
    geometryFacesJsonBlock012.mapM decodeFace = .ok geometryFacesTypedBlock012 := by
  simp only [geometryFacesJsonBlock012, geometryFacesTypedBlock012, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_038, decode_geometry_Faces_039, decode_geometry_Faces_040]
  rfl

theorem decode_geometry_Faces_through_block_012 :
    FaceLedgerValue.arrayAcc013.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock012 := by
  change (FaceLedgerBlock012.blockPush FaceLedgerValue.arrayAcc012).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_012_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_011, decode_geometry_Faces_block_012]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_012_complete"
  err.flush

#print axioms decode_geometry_Faces_038
#print axioms decode_geometry_Faces_039
#print axioms decode_geometry_Faces_040
#print axioms geometry_Faces_block_012_push_eq
#print axioms geometry_Faces_block_012_reverse
#print axioms decode_geometry_Faces_block_012
#print axioms decode_geometry_Faces_through_block_012

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
