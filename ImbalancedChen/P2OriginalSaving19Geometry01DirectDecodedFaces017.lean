import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces016

/-! Original face_ledger typed block 17, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson061 : SourceJson :=
  (FaceLedgerBlock017.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped061 : FaceRecord :=
  { vertices := #[14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 32, 33],
    dimension := 6, pivot := 33,
    facetSets := #[#[14, 15, 16, 18, 19, 20, 21, 22, 23, 24], #[14, 15, 16, 18, 19, 20, 21, 23, 32, 33], #[14, 15, 16, 18, 21, 22, 23, 24, 32, 33], #[14, 15, 16, 19, 20, 22, 23, 24, 32, 33], #[14, 15, 18, 19, 22, 33], #[14, 18, 19, 20, 21, 22, 23, 24, 32, 33], #[15, 16, 18, 19, 20, 21, 22, 24, 32, 33], #[16, 20, 21, 23, 24, 32]],
    simplices := 6 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_061_before_decode"
  err.flush

theorem decode_geometry_Faces_061 :
    decodeFace geometryFacesJson061 = .ok geometryFacesTyped061 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_061_decoded"
  err.flush

noncomputable def geometryFacesJson062 : SourceJson :=
  (FaceLedgerBlock017.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped062 : FaceRecord :=
  { vertices := #[14, 15, 16, 18, 19, 20, 21, 23],
    dimension := 4, pivot := 23,
    facetSets := #[#[14, 15, 16, 18, 21, 23], #[14, 15, 16, 19, 20, 23], #[14, 15, 18, 19], #[14, 18, 19, 20, 21, 23], #[15, 16, 18, 19, 20, 21], #[16, 20, 21, 23]],
    simplices := 4 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_062_before_decode"
  err.flush

theorem decode_geometry_Faces_062 :
    decodeFace geometryFacesJson062 = .ok geometryFacesTyped062 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_062_decoded"
  err.flush

noncomputable def geometryFacesJson063 : SourceJson :=
  (FaceLedgerBlock017.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped063 : FaceRecord :=
  { vertices := #[14, 15, 18],
    dimension := 2, pivot := 18,
    facetSets := #[#[14, 15], #[14, 18], #[15, 18]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_063_before_decode"
  err.flush

theorem decode_geometry_Faces_063 :
    decodeFace geometryFacesJson063 = .ok geometryFacesTyped063 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_063_decoded"
  err.flush

noncomputable def geometryFacesJson064 : SourceJson :=
  (FaceLedgerBlock017.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped064 : FaceRecord :=
  { vertices := #[14, 15, 18, 19],
    dimension := 3, pivot := 19,
    facetSets := #[#[14, 15, 18], #[14, 15, 19], #[14, 18, 19], #[15, 18, 19]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_064_before_decode"
  err.flush

theorem decode_geometry_Faces_064 :
    decodeFace geometryFacesJson064 = .ok geometryFacesTyped064 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_064_decoded"
  err.flush

noncomputable def geometryFacesJson065 : SourceJson :=
  (FaceLedgerBlock017.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped065 : FaceRecord :=
  { vertices := #[14, 15, 18, 19, 22],
    dimension := 4, pivot := 22,
    facetSets := #[#[14, 15, 18, 19], #[14, 15, 18, 22], #[14, 15, 19, 22], #[14, 18, 19, 22], #[15, 18, 19, 22]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_065_before_decode"
  err.flush

theorem decode_geometry_Faces_065 :
    decodeFace geometryFacesJson065 = .ok geometryFacesTyped065 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_065_decoded"
  err.flush

noncomputable def geometryFacesJson066 : SourceJson :=
  (FaceLedgerBlock017.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped066 : FaceRecord :=
  { vertices := #[15, 16],
    dimension := 1, pivot := 16,
    facetSets := #[#[15], #[16]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_066_before_decode"
  err.flush

theorem decode_geometry_Faces_066 :
    decodeFace geometryFacesJson066 = .ok geometryFacesTyped066 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_066_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock017 : List SourceJson := [geometryFacesJson061, geometryFacesJson062, geometryFacesJson063, geometryFacesJson064, geometryFacesJson065, geometryFacesJson066]
noncomputable def geometryFacesTypedBlock017 : List (FaceRecord) := [geometryFacesTyped061, geometryFacesTyped062, geometryFacesTyped063, geometryFacesTyped064, geometryFacesTyped065, geometryFacesTyped066]
noncomputable def geometryFacesTypedThroughBlock017 : List (FaceRecord) := geometryFacesTypedThroughBlock016 ++ geometryFacesTypedBlock017

theorem geometry_Faces_block_017_push_eq (acc : List SourceJson) :
    FaceLedgerBlock017.blockPush acc = [geometryFacesJson066, geometryFacesJson065, geometryFacesJson064, geometryFacesJson063, geometryFacesJson062, geometryFacesJson061] ++ acc := by rfl

theorem geometry_Faces_block_017_reverse (acc : List SourceJson) :
    (FaceLedgerBlock017.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock017 := by
  rw [geometry_Faces_block_017_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_017 :
    geometryFacesJsonBlock017.mapM decodeFace = .ok geometryFacesTypedBlock017 := by
  simp only [geometryFacesJsonBlock017, geometryFacesTypedBlock017, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_061, decode_geometry_Faces_062, decode_geometry_Faces_063, decode_geometry_Faces_064, decode_geometry_Faces_065, decode_geometry_Faces_066]
  rfl

theorem decode_geometry_Faces_through_block_017 :
    FaceLedgerValue.arrayAcc018.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock017 := by
  change (FaceLedgerBlock017.blockPush FaceLedgerValue.arrayAcc017).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_017_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_016, decode_geometry_Faces_block_017]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_017_complete"
  err.flush

#print axioms decode_geometry_Faces_061
#print axioms decode_geometry_Faces_062
#print axioms decode_geometry_Faces_063
#print axioms decode_geometry_Faces_064
#print axioms decode_geometry_Faces_065
#print axioms decode_geometry_Faces_066
#print axioms geometry_Faces_block_017_push_eq
#print axioms geometry_Faces_block_017_reverse
#print axioms decode_geometry_Faces_block_017
#print axioms decode_geometry_Faces_through_block_017

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
