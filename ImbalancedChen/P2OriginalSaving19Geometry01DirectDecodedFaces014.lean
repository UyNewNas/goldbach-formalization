import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces013

/-! Original face_ledger typed block 14, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson047 : SourceJson :=
  (FaceLedgerBlock014.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped047 : FaceRecord :=
  { vertices := #[1, 3, 8, 10, 11, 16, 20, 21, 23, 24, 30, 36],
    dimension := 6, pivot := 36,
    facetSets := #[#[1, 3, 8, 10, 11, 16, 20, 21, 23, 24], #[1, 3, 8, 10, 11, 36], #[1, 3, 8, 10, 16, 20, 21, 23, 30, 36], #[1, 3, 8, 11, 16, 20, 21, 24, 30, 36], #[1, 3, 10, 11, 16, 20, 23, 24, 30, 36], #[1, 8, 10, 11, 16, 21, 23, 24, 30, 36], #[3, 8, 10, 11, 20, 21, 23, 24, 30, 36], #[16, 20, 21, 23, 24, 30]],
    simplices := 6 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_047_before_decode"
  err.flush

theorem decode_geometry_Faces_047 :
    decodeFace geometryFacesJson047 = .ok geometryFacesTyped047 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_047_decoded"
  err.flush

noncomputable def geometryFacesJson048 : SourceJson :=
  (FaceLedgerBlock014.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped048 : FaceRecord :=
  { vertices := #[1, 3, 8, 10, 16, 20, 21, 23],
    dimension := 4, pivot := 23,
    facetSets := #[#[1, 3, 8, 10], #[1, 3, 8, 16, 20, 21], #[1, 3, 10, 16, 20, 23], #[1, 8, 10, 16, 21, 23], #[3, 8, 10, 20, 21, 23], #[16, 20, 21, 23]],
    simplices := 4 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_048_before_decode"
  err.flush

theorem decode_geometry_Faces_048 :
    decodeFace geometryFacesJson048 = .ok geometryFacesTyped048 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_048_decoded"
  err.flush

noncomputable def geometryFacesJson049 : SourceJson :=
  (FaceLedgerBlock014.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped049 : FaceRecord :=
  { vertices := #[1, 3, 8, 16, 20, 21],
    dimension := 3, pivot := 21,
    facetSets := #[#[1, 3, 8], #[1, 3, 16, 20], #[1, 8, 16, 21], #[3, 8, 20, 21], #[16, 20, 21]],
    simplices := 3 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_049_before_decode"
  err.flush

theorem decode_geometry_Faces_049 :
    decodeFace geometryFacesJson049 = .ok geometryFacesTyped049 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_049_decoded"
  err.flush

noncomputable def geometryFacesJson050 : SourceJson :=
  (FaceLedgerBlock014.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped050 : FaceRecord :=
  { vertices := #[1, 3, 16, 20],
    dimension := 2, pivot := 20,
    facetSets := #[#[1, 3], #[1, 16], #[3, 20], #[16, 20]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_050_before_decode"
  err.flush

theorem decode_geometry_Faces_050 :
    decodeFace geometryFacesJson050 = .ok geometryFacesTyped050 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_050_decoded"
  err.flush

noncomputable def geometryFacesJson051 : SourceJson :=
  (FaceLedgerBlock014.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped051 : FaceRecord :=
  { vertices := #[1, 16],
    dimension := 1, pivot := 16,
    facetSets := #[#[1], #[16]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_051_before_decode"
  err.flush

theorem decode_geometry_Faces_051 :
    decodeFace geometryFacesJson051 = .ok geometryFacesTyped051 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_051_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock014 : List SourceJson := [geometryFacesJson047, geometryFacesJson048, geometryFacesJson049, geometryFacesJson050, geometryFacesJson051]
noncomputable def geometryFacesTypedBlock014 : List (FaceRecord) := [geometryFacesTyped047, geometryFacesTyped048, geometryFacesTyped049, geometryFacesTyped050, geometryFacesTyped051]
noncomputable def geometryFacesTypedThroughBlock014 : List (FaceRecord) := geometryFacesTypedThroughBlock013 ++ geometryFacesTypedBlock014

theorem geometry_Faces_block_014_push_eq (acc : List SourceJson) :
    FaceLedgerBlock014.blockPush acc = [geometryFacesJson051, geometryFacesJson050, geometryFacesJson049, geometryFacesJson048, geometryFacesJson047] ++ acc := by rfl

theorem geometry_Faces_block_014_reverse (acc : List SourceJson) :
    (FaceLedgerBlock014.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock014 := by
  rw [geometry_Faces_block_014_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_014 :
    geometryFacesJsonBlock014.mapM decodeFace = .ok geometryFacesTypedBlock014 := by
  simp only [geometryFacesJsonBlock014, geometryFacesTypedBlock014, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_047, decode_geometry_Faces_048, decode_geometry_Faces_049, decode_geometry_Faces_050, decode_geometry_Faces_051]
  rfl

theorem decode_geometry_Faces_through_block_014 :
    FaceLedgerValue.arrayAcc015.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock014 := by
  change (FaceLedgerBlock014.blockPush FaceLedgerValue.arrayAcc014).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_014_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_013, decode_geometry_Faces_block_014]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_014_complete"
  err.flush

#print axioms decode_geometry_Faces_047
#print axioms decode_geometry_Faces_048
#print axioms decode_geometry_Faces_049
#print axioms decode_geometry_Faces_050
#print axioms decode_geometry_Faces_051
#print axioms geometry_Faces_block_014_push_eq
#print axioms geometry_Faces_block_014_reverse
#print axioms decode_geometry_Faces_block_014
#print axioms decode_geometry_Faces_through_block_014

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
