import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces018

/-! Original face_ledger typed block 19, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson076 : SourceJson :=
  (FaceLedgerBlock019.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped076 : FaceRecord :=
  { vertices := #[16, 20, 21, 23, 24, 30],
    dimension := 5, pivot := 30,
    facetSets := #[#[16, 20, 21, 23, 24], #[16, 20, 21, 23, 30], #[16, 20, 21, 24, 30], #[16, 20, 23, 24, 30], #[16, 21, 23, 24, 30], #[20, 21, 23, 24, 30]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_076_before_decode"
  err.flush

theorem decode_geometry_Faces_076 :
    decodeFace geometryFacesJson076 = .ok geometryFacesTyped076 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_076_decoded"
  err.flush

noncomputable def geometryFacesJson077 : SourceJson :=
  (FaceLedgerBlock019.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped077 : FaceRecord :=
  { vertices := #[16, 20, 21, 23, 24, 30, 32],
    dimension := 6, pivot := 32,
    facetSets := #[#[16, 20, 21, 23, 24, 30], #[16, 20, 21, 23, 24, 32], #[16, 20, 21, 23, 30, 32], #[16, 20, 21, 24, 30, 32], #[16, 20, 23, 24, 30, 32], #[16, 21, 23, 24, 30, 32], #[20, 21, 23, 24, 30, 32]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_077_before_decode"
  err.flush

theorem decode_geometry_Faces_077 :
    decodeFace geometryFacesJson077 = .ok geometryFacesTyped077 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_077_decoded"
  err.flush

noncomputable def geometryFacesJson078 : SourceJson :=
  (FaceLedgerBlock019.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped078 : FaceRecord :=
  { vertices := #[16, 20, 21, 23, 24, 32],
    dimension := 5, pivot := 32,
    facetSets := #[#[16, 20, 21, 23, 24], #[16, 20, 21, 23, 32], #[16, 20, 21, 24, 32], #[16, 20, 23, 24, 32], #[16, 21, 23, 24, 32], #[20, 21, 23, 24, 32]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_078_before_decode"
  err.flush

theorem decode_geometry_Faces_078 :
    decodeFace geometryFacesJson078 = .ok geometryFacesTyped078 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_078_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock019 : List SourceJson := [geometryFacesJson076, geometryFacesJson077, geometryFacesJson078]
noncomputable def geometryFacesTypedBlock019 : List (FaceRecord) := [geometryFacesTyped076, geometryFacesTyped077, geometryFacesTyped078]
noncomputable def geometryFacesTypedThroughBlock019 : List (FaceRecord) := geometryFacesTypedThroughBlock018 ++ geometryFacesTypedBlock019

theorem geometry_Faces_block_019_push_eq (acc : List SourceJson) :
    FaceLedgerBlock019.blockPush acc = [geometryFacesJson078, geometryFacesJson077, geometryFacesJson076] ++ acc := by rfl

theorem geometry_Faces_block_019_reverse (acc : List SourceJson) :
    (FaceLedgerBlock019.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock019 := by
  rw [geometry_Faces_block_019_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_019 :
    geometryFacesJsonBlock019.mapM decodeFace = .ok geometryFacesTypedBlock019 := by
  simp only [geometryFacesJsonBlock019, geometryFacesTypedBlock019, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_076, decode_geometry_Faces_077, decode_geometry_Faces_078]
  rfl

theorem decode_geometry_Faces_through_block_019 :
    FaceLedgerValue.arrayAcc020.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock019 := by
  change (FaceLedgerBlock019.blockPush FaceLedgerValue.arrayAcc019).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_019_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_018, decode_geometry_Faces_block_019]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_019_complete"
  err.flush

#print axioms decode_geometry_Faces_076
#print axioms decode_geometry_Faces_077
#print axioms decode_geometry_Faces_078
#print axioms geometry_Faces_block_019_push_eq
#print axioms geometry_Faces_block_019_reverse
#print axioms decode_geometry_Faces_block_019
#print axioms decode_geometry_Faces_through_block_019

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
