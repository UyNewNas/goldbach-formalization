import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces012

/-! Original face_ledger typed block 13, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson041 : SourceJson :=
  (FaceLedgerBlock013.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped041 : FaceRecord :=
  { vertices := #[1, 3, 5, 8, 13, 25],
    dimension := 3, pivot := 25,
    facetSets := #[#[1, 3, 5, 13], #[1, 3, 8], #[1, 8, 13, 25], #[3, 5, 8, 25], #[5, 13, 25]],
    simplices := 3 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_041_before_decode"
  err.flush

theorem decode_geometry_Faces_041 :
    decodeFace geometryFacesJson041 = .ok geometryFacesTyped041 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_041_decoded"
  err.flush

noncomputable def geometryFacesJson042 : SourceJson :=
  (FaceLedgerBlock013.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped042 : FaceRecord :=
  { vertices := #[1, 3, 5, 13],
    dimension := 2, pivot := 13,
    facetSets := #[#[1, 3], #[1, 13], #[3, 5], #[5, 13]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_042_before_decode"
  err.flush

theorem decode_geometry_Faces_042 :
    decodeFace geometryFacesJson042 = .ok geometryFacesTyped042 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_042_decoded"
  err.flush

noncomputable def geometryFacesJson043 : SourceJson :=
  (FaceLedgerBlock013.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped043 : FaceRecord :=
  { vertices := #[1, 3, 8],
    dimension := 2, pivot := 8,
    facetSets := #[#[1, 3], #[1, 8], #[3, 8]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_043_before_decode"
  err.flush

theorem decode_geometry_Faces_043 :
    decodeFace geometryFacesJson043 = .ok geometryFacesTyped043 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_043_decoded"
  err.flush

noncomputable def geometryFacesJson044 : SourceJson :=
  (FaceLedgerBlock013.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped044 : FaceRecord :=
  { vertices := #[1, 3, 8, 10],
    dimension := 3, pivot := 10,
    facetSets := #[#[1, 3, 8], #[1, 3, 10], #[1, 8, 10], #[3, 8, 10]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_044_before_decode"
  err.flush

theorem decode_geometry_Faces_044 :
    decodeFace geometryFacesJson044 = .ok geometryFacesTyped044 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_044_decoded"
  err.flush

noncomputable def geometryFacesJson045 : SourceJson :=
  (FaceLedgerBlock013.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped045 : FaceRecord :=
  { vertices := #[1, 3, 8, 10, 11],
    dimension := 4, pivot := 11,
    facetSets := #[#[1, 3, 8, 10], #[1, 3, 8, 11], #[1, 3, 10, 11], #[1, 8, 10, 11], #[3, 8, 10, 11]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_045_before_decode"
  err.flush

theorem decode_geometry_Faces_045 :
    decodeFace geometryFacesJson045 = .ok geometryFacesTyped045 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_045_decoded"
  err.flush

noncomputable def geometryFacesJson046 : SourceJson :=
  (FaceLedgerBlock013.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped046 : FaceRecord :=
  { vertices := #[1, 3, 8, 10, 11, 16, 20, 21, 23, 24],
    dimension := 5, pivot := 24,
    facetSets := #[#[1, 3, 8, 10, 11], #[1, 3, 8, 10, 16, 20, 21, 23], #[1, 3, 8, 11, 16, 20, 21, 24], #[1, 3, 10, 11, 16, 20, 23, 24], #[1, 8, 10, 11, 16, 21, 23, 24], #[3, 8, 10, 11, 20, 21, 23, 24], #[16, 20, 21, 23, 24]],
    simplices := 5 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_046_before_decode"
  err.flush

theorem decode_geometry_Faces_046 :
    decodeFace geometryFacesJson046 = .ok geometryFacesTyped046 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_046_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock013 : List SourceJson := [geometryFacesJson041, geometryFacesJson042, geometryFacesJson043, geometryFacesJson044, geometryFacesJson045, geometryFacesJson046]
noncomputable def geometryFacesTypedBlock013 : List (FaceRecord) := [geometryFacesTyped041, geometryFacesTyped042, geometryFacesTyped043, geometryFacesTyped044, geometryFacesTyped045, geometryFacesTyped046]
noncomputable def geometryFacesTypedThroughBlock013 : List (FaceRecord) := geometryFacesTypedThroughBlock012 ++ geometryFacesTypedBlock013

theorem geometry_Faces_block_013_push_eq (acc : List SourceJson) :
    FaceLedgerBlock013.blockPush acc = [geometryFacesJson046, geometryFacesJson045, geometryFacesJson044, geometryFacesJson043, geometryFacesJson042, geometryFacesJson041] ++ acc := by rfl

theorem geometry_Faces_block_013_reverse (acc : List SourceJson) :
    (FaceLedgerBlock013.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock013 := by
  rw [geometry_Faces_block_013_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_013 :
    geometryFacesJsonBlock013.mapM decodeFace = .ok geometryFacesTypedBlock013 := by
  simp only [geometryFacesJsonBlock013, geometryFacesTypedBlock013, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_041, decode_geometry_Faces_042, decode_geometry_Faces_043, decode_geometry_Faces_044, decode_geometry_Faces_045, decode_geometry_Faces_046]
  rfl

theorem decode_geometry_Faces_through_block_013 :
    FaceLedgerValue.arrayAcc014.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock013 := by
  change (FaceLedgerBlock013.blockPush FaceLedgerValue.arrayAcc013).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_013_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_012, decode_geometry_Faces_block_013]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_013_complete"
  err.flush

#print axioms decode_geometry_Faces_041
#print axioms decode_geometry_Faces_042
#print axioms decode_geometry_Faces_043
#print axioms decode_geometry_Faces_044
#print axioms decode_geometry_Faces_045
#print axioms decode_geometry_Faces_046
#print axioms geometry_Faces_block_013_push_eq
#print axioms geometry_Faces_block_013_reverse
#print axioms decode_geometry_Faces_block_013
#print axioms decode_geometry_Faces_through_block_013

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
