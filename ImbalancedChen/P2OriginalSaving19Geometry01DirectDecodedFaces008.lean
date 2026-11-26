import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces007

/-! Original face_ledger typed block 8, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson015 : SourceJson :=
  (FaceLedgerBlock008.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped015 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 15, 16, 19, 20],
    dimension := 3, pivot := 20,
    facetSets := #[#[0, 1, 2, 3], #[0, 1, 15, 16], #[0, 2, 15, 19], #[1, 3, 16, 20], #[2, 3, 19, 20], #[15, 16, 19, 20]],
    simplices := 6 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_015_before_decode"
  err.flush

theorem decode_geometry_Faces_015 :
    decodeFace geometryFacesJson015 = .ok geometryFacesTyped015 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_015_decoded"
  err.flush

noncomputable def geometryFacesJson016 : SourceJson :=
  (FaceLedgerBlock008.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped016 : FaceRecord :=
  { vertices := #[0, 1, 15, 16],
    dimension := 2, pivot := 16,
    facetSets := #[#[0, 1], #[0, 15], #[1, 16], #[15, 16]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_016_before_decode"
  err.flush

theorem decode_geometry_Faces_016 :
    decodeFace geometryFacesJson016 = .ok geometryFacesTyped016 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_016_decoded"
  err.flush

noncomputable def geometryFacesJson017 : SourceJson :=
  (FaceLedgerBlock008.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped017 : FaceRecord :=
  { vertices := #[0, 2],
    dimension := 1, pivot := 2,
    facetSets := #[#[0], #[2]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_017_before_decode"
  err.flush

theorem decode_geometry_Faces_017 :
    decodeFace geometryFacesJson017 = .ok geometryFacesTyped017 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_017_decoded"
  err.flush

noncomputable def geometryFacesJson018 : SourceJson :=
  (FaceLedgerBlock008.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped018 : FaceRecord :=
  { vertices := #[0, 2, 4, 6, 7, 9, 12, 17, 26, 27],
    dimension := 5, pivot := 27,
    facetSets := #[#[0, 2, 4, 6, 7, 12, 17, 26], #[0, 2, 4, 6, 9, 12, 17, 27], #[0, 2, 4, 7, 9, 12, 26, 27], #[0, 2, 6, 7, 9], #[0, 6, 7, 9, 12, 17, 26, 27], #[2, 4, 6, 7, 9, 17, 26, 27], #[4, 12, 17, 26, 27]],
    simplices := 5 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_018_before_decode"
  err.flush

theorem decode_geometry_Faces_018 :
    decodeFace geometryFacesJson018 = .ok geometryFacesTyped018 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_018_decoded"
  err.flush

noncomputable def geometryFacesJson019 : SourceJson :=
  (FaceLedgerBlock008.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped019 : FaceRecord :=
  { vertices := #[0, 2, 4, 6, 7, 12, 17, 26],
    dimension := 4, pivot := 26,
    facetSets := #[#[0, 2, 4, 6, 12, 17], #[0, 2, 4, 7, 12, 26], #[0, 2, 6, 7], #[0, 6, 7, 12, 17, 26], #[2, 4, 6, 7, 17, 26], #[4, 12, 17, 26]],
    simplices := 4 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_019_before_decode"
  err.flush

theorem decode_geometry_Faces_019 :
    decodeFace geometryFacesJson019 = .ok geometryFacesTyped019 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_019_decoded"
  err.flush

noncomputable def geometryFacesJson020 : SourceJson :=
  (FaceLedgerBlock008.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped020 : FaceRecord :=
  { vertices := #[0, 2, 4, 6, 12, 17],
    dimension := 3, pivot := 17,
    facetSets := #[#[0, 2, 4, 12], #[0, 2, 6], #[0, 6, 12, 17], #[2, 4, 6, 17], #[4, 12, 17]],
    simplices := 3 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_020_before_decode"
  err.flush

theorem decode_geometry_Faces_020 :
    decodeFace geometryFacesJson020 = .ok geometryFacesTyped020 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_020_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock008 : List SourceJson := [geometryFacesJson015, geometryFacesJson016, geometryFacesJson017, geometryFacesJson018, geometryFacesJson019, geometryFacesJson020]
noncomputable def geometryFacesTypedBlock008 : List (FaceRecord) := [geometryFacesTyped015, geometryFacesTyped016, geometryFacesTyped017, geometryFacesTyped018, geometryFacesTyped019, geometryFacesTyped020]
noncomputable def geometryFacesTypedThroughBlock008 : List (FaceRecord) := geometryFacesTypedThroughBlock007 ++ geometryFacesTypedBlock008

theorem geometry_Faces_block_008_push_eq (acc : List SourceJson) :
    FaceLedgerBlock008.blockPush acc = [geometryFacesJson020, geometryFacesJson019, geometryFacesJson018, geometryFacesJson017, geometryFacesJson016, geometryFacesJson015] ++ acc := by rfl

theorem geometry_Faces_block_008_reverse (acc : List SourceJson) :
    (FaceLedgerBlock008.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock008 := by
  rw [geometry_Faces_block_008_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_008 :
    geometryFacesJsonBlock008.mapM decodeFace = .ok geometryFacesTypedBlock008 := by
  simp only [geometryFacesJsonBlock008, geometryFacesTypedBlock008, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_015, decode_geometry_Faces_016, decode_geometry_Faces_017, decode_geometry_Faces_018, decode_geometry_Faces_019, decode_geometry_Faces_020]
  rfl

theorem decode_geometry_Faces_through_block_008 :
    FaceLedgerValue.arrayAcc009.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock008 := by
  change (FaceLedgerBlock008.blockPush FaceLedgerValue.arrayAcc008).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_008_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_007, decode_geometry_Faces_block_008]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_008_complete"
  err.flush

#print axioms decode_geometry_Faces_015
#print axioms decode_geometry_Faces_016
#print axioms decode_geometry_Faces_017
#print axioms decode_geometry_Faces_018
#print axioms decode_geometry_Faces_019
#print axioms decode_geometry_Faces_020
#print axioms geometry_Faces_block_008_push_eq
#print axioms geometry_Faces_block_008_reverse
#print axioms decode_geometry_Faces_block_008
#print axioms decode_geometry_Faces_through_block_008

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
