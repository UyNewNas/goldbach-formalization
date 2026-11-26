import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces015

/-! Original face_ledger typed block 16, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson059 : SourceJson :=
  (FaceLedgerBlock016.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped059 : FaceRecord :=
  { vertices := #[14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 30, 31],
    dimension := 6, pivot := 31,
    facetSets := #[#[14, 15, 16, 18, 19, 20, 21, 22, 23, 24], #[14, 15, 16, 18, 19, 20, 21, 23, 30, 31], #[14, 15, 16, 18, 21, 22, 23, 24, 30, 31], #[14, 15, 16, 19, 20, 22, 23, 24, 30, 31], #[14, 15, 18, 19, 22, 31], #[14, 18, 19, 20, 21, 22, 23, 24, 30, 31], #[15, 16, 18, 19, 20, 21, 22, 24, 30, 31], #[16, 20, 21, 23, 24, 30]],
    simplices := 6 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_059_before_decode"
  err.flush

theorem decode_geometry_Faces_059 :
    decodeFace geometryFacesJson059 = .ok geometryFacesTyped059 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_059_decoded"
  err.flush

noncomputable def geometryFacesJson060 : SourceJson :=
  (FaceLedgerBlock016.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped060 : FaceRecord :=
  { vertices := #[14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 30, 31, 32, 33],
    dimension := 7, pivot := 33,
    facetSets := #[#[14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 30, 31], #[14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 32, 33], #[14, 15, 16, 18, 19, 20, 21, 23, 30, 31, 32, 33], #[14, 15, 16, 18, 21, 22, 23, 24, 30, 31, 32, 33], #[14, 15, 16, 19, 20, 22, 23, 24, 30, 31, 32, 33], #[14, 15, 18, 19, 22, 31, 33], #[14, 18, 19, 20, 21, 22, 23, 24, 30, 31, 32, 33], #[15, 16, 18, 19, 20, 21, 22, 24, 30, 31, 32, 33], #[16, 20, 21, 23, 24, 30, 32]],
    simplices := 7 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_060_before_decode"
  err.flush

theorem decode_geometry_Faces_060 :
    decodeFace geometryFacesJson060 = .ok geometryFacesTyped060 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_060_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock016 : List SourceJson := [geometryFacesJson059, geometryFacesJson060]
noncomputable def geometryFacesTypedBlock016 : List (FaceRecord) := [geometryFacesTyped059, geometryFacesTyped060]
noncomputable def geometryFacesTypedThroughBlock016 : List (FaceRecord) := geometryFacesTypedThroughBlock015 ++ geometryFacesTypedBlock016

theorem geometry_Faces_block_016_push_eq (acc : List SourceJson) :
    FaceLedgerBlock016.blockPush acc = [geometryFacesJson060, geometryFacesJson059] ++ acc := by rfl

theorem geometry_Faces_block_016_reverse (acc : List SourceJson) :
    (FaceLedgerBlock016.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock016 := by
  rw [geometry_Faces_block_016_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_016 :
    geometryFacesJsonBlock016.mapM decodeFace = .ok geometryFacesTypedBlock016 := by
  simp only [geometryFacesJsonBlock016, geometryFacesTypedBlock016, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_059, decode_geometry_Faces_060]
  rfl

theorem decode_geometry_Faces_through_block_016 :
    FaceLedgerValue.arrayAcc017.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock016 := by
  change (FaceLedgerBlock016.blockPush FaceLedgerValue.arrayAcc016).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_016_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_015, decode_geometry_Faces_block_016]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_016_complete"
  err.flush

#print axioms decode_geometry_Faces_059
#print axioms decode_geometry_Faces_060
#print axioms geometry_Faces_block_016_push_eq
#print axioms geometry_Faces_block_016_reverse
#print axioms decode_geometry_Faces_block_016
#print axioms decode_geometry_Faces_through_block_016

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
