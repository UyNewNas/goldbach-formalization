import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces014

/-! Original face_ledger typed block 15, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson052 : SourceJson :=
  (FaceLedgerBlock015.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacesTyped052 : FaceRecord :=
  { vertices := #[2, 3],
    dimension := 1, pivot := 3,
    facetSets := #[#[2], #[3]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_052_before_decode"
  err.flush

theorem decode_geometry_Faces_052 :
    decodeFace geometryFacesJson052 = .ok geometryFacesTyped052 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_052_decoded"
  err.flush

noncomputable def geometryFacesJson053 : SourceJson :=
  (FaceLedgerBlock015.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped053 : FaceRecord :=
  { vertices := #[2, 3, 4, 5],
    dimension := 2, pivot := 5,
    facetSets := #[#[2, 3], #[2, 4], #[3, 5], #[4, 5]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_053_before_decode"
  err.flush

theorem decode_geometry_Faces_053 :
    decodeFace geometryFacesJson053 = .ok geometryFacesTyped053 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_053_decoded"
  err.flush

noncomputable def geometryFacesJson054 : SourceJson :=
  (FaceLedgerBlock015.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped054 : FaceRecord :=
  { vertices := #[2, 4],
    dimension := 1, pivot := 4,
    facetSets := #[#[2], #[4]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_054_before_decode"
  err.flush

theorem decode_geometry_Faces_054 :
    decodeFace geometryFacesJson054 = .ok geometryFacesTyped054 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_054_decoded"
  err.flush

noncomputable def geometryFacesJson055 : SourceJson :=
  (FaceLedgerBlock015.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped055 : FaceRecord :=
  { vertices := #[3, 5],
    dimension := 1, pivot := 5,
    facetSets := #[#[3], #[5]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_055_before_decode"
  err.flush

theorem decode_geometry_Faces_055 :
    decodeFace geometryFacesJson055 = .ok geometryFacesTyped055 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_055_decoded"
  err.flush

noncomputable def geometryFacesJson056 : SourceJson :=
  (FaceLedgerBlock015.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped056 : FaceRecord :=
  { vertices := #[7, 14],
    dimension := 1, pivot := 14,
    facetSets := #[#[7], #[14]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_056_before_decode"
  err.flush

theorem decode_geometry_Faces_056 :
    decodeFace geometryFacesJson056 = .ok geometryFacesTyped056 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_056_decoded"
  err.flush

noncomputable def geometryFacesJson057 : SourceJson :=
  (FaceLedgerBlock015.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped057 : FaceRecord :=
  { vertices := #[14, 15],
    dimension := 1, pivot := 15,
    facetSets := #[#[14], #[15]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_057_before_decode"
  err.flush

theorem decode_geometry_Faces_057 :
    decodeFace geometryFacesJson057 = .ok geometryFacesTyped057 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_057_decoded"
  err.flush

noncomputable def geometryFacesJson058 : SourceJson :=
  (FaceLedgerBlock015.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped058 : FaceRecord :=
  { vertices := #[14, 15, 16, 18, 19, 20, 21, 22, 23, 24],
    dimension := 5, pivot := 24,
    facetSets := #[#[14, 15, 16, 18, 19, 20, 21, 23], #[14, 15, 16, 18, 21, 22, 23, 24], #[14, 15, 16, 19, 20, 22, 23, 24], #[14, 15, 18, 19, 22], #[14, 18, 19, 20, 21, 22, 23, 24], #[15, 16, 18, 19, 20, 21, 22, 24], #[16, 20, 21, 23, 24]],
    simplices := 5 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_058_before_decode"
  err.flush

theorem decode_geometry_Faces_058 :
    decodeFace geometryFacesJson058 = .ok geometryFacesTyped058 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_058_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock015 : List SourceJson := [geometryFacesJson052, geometryFacesJson053, geometryFacesJson054, geometryFacesJson055, geometryFacesJson056, geometryFacesJson057, geometryFacesJson058]
noncomputable def geometryFacesTypedBlock015 : List (FaceRecord) := [geometryFacesTyped052, geometryFacesTyped053, geometryFacesTyped054, geometryFacesTyped055, geometryFacesTyped056, geometryFacesTyped057, geometryFacesTyped058]
noncomputable def geometryFacesTypedThroughBlock015 : List (FaceRecord) := geometryFacesTypedThroughBlock014 ++ geometryFacesTypedBlock015

theorem geometry_Faces_block_015_push_eq (acc : List SourceJson) :
    FaceLedgerBlock015.blockPush acc = [geometryFacesJson058, geometryFacesJson057, geometryFacesJson056, geometryFacesJson055, geometryFacesJson054, geometryFacesJson053, geometryFacesJson052] ++ acc := by rfl

theorem geometry_Faces_block_015_reverse (acc : List SourceJson) :
    (FaceLedgerBlock015.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock015 := by
  rw [geometry_Faces_block_015_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_015 :
    geometryFacesJsonBlock015.mapM decodeFace = .ok geometryFacesTypedBlock015 := by
  simp only [geometryFacesJsonBlock015, geometryFacesTypedBlock015, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_052, decode_geometry_Faces_053, decode_geometry_Faces_054, decode_geometry_Faces_055, decode_geometry_Faces_056, decode_geometry_Faces_057, decode_geometry_Faces_058]
  rfl

theorem decode_geometry_Faces_through_block_015 :
    FaceLedgerValue.arrayAcc016.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock015 := by
  change (FaceLedgerBlock015.blockPush FaceLedgerValue.arrayAcc015).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_015_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_014, decode_geometry_Faces_block_015]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_015_complete"
  err.flush

#print axioms decode_geometry_Faces_052
#print axioms decode_geometry_Faces_053
#print axioms decode_geometry_Faces_054
#print axioms decode_geometry_Faces_055
#print axioms decode_geometry_Faces_056
#print axioms decode_geometry_Faces_057
#print axioms decode_geometry_Faces_058
#print axioms geometry_Faces_block_015_push_eq
#print axioms geometry_Faces_block_015_reverse
#print axioms decode_geometry_Faces_block_015
#print axioms decode_geometry_Faces_through_block_015

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
