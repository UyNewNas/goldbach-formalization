import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces017

/-! Original face_ledger typed block 18, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson067 : SourceJson :=
  (FaceLedgerBlock018.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryFacesTyped067 : FaceRecord :=
  { vertices := #[15, 16, 18, 19, 20, 21],
    dimension := 3, pivot := 21,
    facetSets := #[#[15, 16, 18, 21], #[15, 16, 19, 20], #[15, 18, 19], #[16, 20, 21], #[18, 19, 20, 21]],
    simplices := 3 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_067_before_decode"
  err.flush

theorem decode_geometry_Faces_067 :
    decodeFace geometryFacesJson067 = .ok geometryFacesTyped067 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_067_decoded"
  err.flush

noncomputable def geometryFacesJson068 : SourceJson :=
  (FaceLedgerBlock018.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryFacesTyped068 : FaceRecord :=
  { vertices := #[15, 16, 19, 20],
    dimension := 2, pivot := 20,
    facetSets := #[#[15, 16], #[15, 19], #[16, 20], #[19, 20]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_068_before_decode"
  err.flush

theorem decode_geometry_Faces_068 :
    decodeFace geometryFacesJson068 = .ok geometryFacesTyped068 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_068_decoded"
  err.flush

noncomputable def geometryFacesJson069 : SourceJson :=
  (FaceLedgerBlock018.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacesTyped069 : FaceRecord :=
  { vertices := #[15, 18],
    dimension := 1, pivot := 18,
    facetSets := #[#[15], #[18]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_069_before_decode"
  err.flush

theorem decode_geometry_Faces_069 :
    decodeFace geometryFacesJson069 = .ok geometryFacesTyped069 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_069_decoded"
  err.flush

noncomputable def geometryFacesJson070 : SourceJson :=
  (FaceLedgerBlock018.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped070 : FaceRecord :=
  { vertices := #[15, 18, 19],
    dimension := 2, pivot := 19,
    facetSets := #[#[15, 18], #[15, 19], #[18, 19]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_070_before_decode"
  err.flush

theorem decode_geometry_Faces_070 :
    decodeFace geometryFacesJson070 = .ok geometryFacesTyped070 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_070_decoded"
  err.flush

noncomputable def geometryFacesJson071 : SourceJson :=
  (FaceLedgerBlock018.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped071 : FaceRecord :=
  { vertices := #[15, 19],
    dimension := 1, pivot := 19,
    facetSets := #[#[15], #[19]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_071_before_decode"
  err.flush

theorem decode_geometry_Faces_071 :
    decodeFace geometryFacesJson071 = .ok geometryFacesTyped071 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_071_decoded"
  err.flush

noncomputable def geometryFacesJson072 : SourceJson :=
  (FaceLedgerBlock018.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped072 : FaceRecord :=
  { vertices := #[16, 20],
    dimension := 1, pivot := 20,
    facetSets := #[#[16], #[20]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_072_before_decode"
  err.flush

theorem decode_geometry_Faces_072 :
    decodeFace geometryFacesJson072 = .ok geometryFacesTyped072 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_072_decoded"
  err.flush

noncomputable def geometryFacesJson073 : SourceJson :=
  (FaceLedgerBlock018.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped073 : FaceRecord :=
  { vertices := #[16, 20, 21],
    dimension := 2, pivot := 21,
    facetSets := #[#[16, 20], #[16, 21], #[20, 21]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_073_before_decode"
  err.flush

theorem decode_geometry_Faces_073 :
    decodeFace geometryFacesJson073 = .ok geometryFacesTyped073 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_073_decoded"
  err.flush

noncomputable def geometryFacesJson074 : SourceJson :=
  (FaceLedgerBlock018.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped074 : FaceRecord :=
  { vertices := #[16, 20, 21, 23],
    dimension := 3, pivot := 23,
    facetSets := #[#[16, 20, 21], #[16, 20, 23], #[16, 21, 23], #[20, 21, 23]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_074_before_decode"
  err.flush

theorem decode_geometry_Faces_074 :
    decodeFace geometryFacesJson074 = .ok geometryFacesTyped074 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_074_decoded"
  err.flush

noncomputable def geometryFacesJson075 : SourceJson :=
  (FaceLedgerBlock018.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped075 : FaceRecord :=
  { vertices := #[16, 20, 21, 23, 24],
    dimension := 4, pivot := 24,
    facetSets := #[#[16, 20, 21, 23], #[16, 20, 21, 24], #[16, 20, 23, 24], #[16, 21, 23, 24], #[20, 21, 23, 24]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_075_before_decode"
  err.flush

theorem decode_geometry_Faces_075 :
    decodeFace geometryFacesJson075 = .ok geometryFacesTyped075 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_075_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock018 : List SourceJson := [geometryFacesJson067, geometryFacesJson068, geometryFacesJson069, geometryFacesJson070, geometryFacesJson071, geometryFacesJson072, geometryFacesJson073, geometryFacesJson074, geometryFacesJson075]
noncomputable def geometryFacesTypedBlock018 : List (FaceRecord) := [geometryFacesTyped067, geometryFacesTyped068, geometryFacesTyped069, geometryFacesTyped070, geometryFacesTyped071, geometryFacesTyped072, geometryFacesTyped073, geometryFacesTyped074, geometryFacesTyped075]
noncomputable def geometryFacesTypedThroughBlock018 : List (FaceRecord) := geometryFacesTypedThroughBlock017 ++ geometryFacesTypedBlock018

theorem geometry_Faces_block_018_push_eq (acc : List SourceJson) :
    FaceLedgerBlock018.blockPush acc = [geometryFacesJson075, geometryFacesJson074, geometryFacesJson073, geometryFacesJson072, geometryFacesJson071, geometryFacesJson070, geometryFacesJson069, geometryFacesJson068, geometryFacesJson067] ++ acc := by rfl

theorem geometry_Faces_block_018_reverse (acc : List SourceJson) :
    (FaceLedgerBlock018.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock018 := by
  rw [geometry_Faces_block_018_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_018 :
    geometryFacesJsonBlock018.mapM decodeFace = .ok geometryFacesTypedBlock018 := by
  simp only [geometryFacesJsonBlock018, geometryFacesTypedBlock018, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_067, decode_geometry_Faces_068, decode_geometry_Faces_069, decode_geometry_Faces_070, decode_geometry_Faces_071, decode_geometry_Faces_072, decode_geometry_Faces_073, decode_geometry_Faces_074, decode_geometry_Faces_075]
  rfl

theorem decode_geometry_Faces_through_block_018 :
    FaceLedgerValue.arrayAcc019.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock018 := by
  change (FaceLedgerBlock018.blockPush FaceLedgerValue.arrayAcc018).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_018_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_017, decode_geometry_Faces_block_018]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_018_complete"
  err.flush

#print axioms decode_geometry_Faces_067
#print axioms decode_geometry_Faces_068
#print axioms decode_geometry_Faces_069
#print axioms decode_geometry_Faces_070
#print axioms decode_geometry_Faces_071
#print axioms decode_geometry_Faces_072
#print axioms decode_geometry_Faces_073
#print axioms decode_geometry_Faces_074
#print axioms decode_geometry_Faces_075
#print axioms geometry_Faces_block_018_push_eq
#print axioms geometry_Faces_block_018_reverse
#print axioms decode_geometry_Faces_block_018
#print axioms decode_geometry_Faces_through_block_018

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
