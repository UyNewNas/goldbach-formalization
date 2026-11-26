import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces009

/-! Original face_ledger typed block 10, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson027 : SourceJson :=
  (FaceLedgerBlock010.blockPush []).get ⟨9, by decide +kernel⟩

noncomputable def geometryFacesTyped027 : FaceRecord :=
  { vertices := #[0, 2, 6, 15, 18, 19],
    dimension := 3, pivot := 19,
    facetSets := #[#[0, 2, 6], #[0, 2, 15, 19], #[0, 6, 15, 18], #[2, 6, 18, 19], #[15, 18, 19]],
    simplices := 3 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_027_before_decode"
  err.flush

theorem decode_geometry_Faces_027 :
    decodeFace geometryFacesJson027 = .ok geometryFacesTyped027 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_027_decoded"
  err.flush

noncomputable def geometryFacesJson028 : SourceJson :=
  (FaceLedgerBlock010.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryFacesTyped028 : FaceRecord :=
  { vertices := #[0, 2, 15, 19],
    dimension := 2, pivot := 19,
    facetSets := #[#[0, 2], #[0, 15], #[2, 19], #[15, 19]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_028_before_decode"
  err.flush

theorem decode_geometry_Faces_028 :
    decodeFace geometryFacesJson028 = .ok geometryFacesTyped028 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_028_decoded"
  err.flush

noncomputable def geometryFacesJson029 : SourceJson :=
  (FaceLedgerBlock010.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryFacesTyped029 : FaceRecord :=
  { vertices := #[0, 6],
    dimension := 1, pivot := 6,
    facetSets := #[#[0], #[6]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_029_before_decode"
  err.flush

theorem decode_geometry_Faces_029 :
    decodeFace geometryFacesJson029 = .ok geometryFacesTyped029 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_029_decoded"
  err.flush

noncomputable def geometryFacesJson030 : SourceJson :=
  (FaceLedgerBlock010.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacesTyped030 : FaceRecord :=
  { vertices := #[0, 6, 7],
    dimension := 2, pivot := 7,
    facetSets := #[#[0, 6], #[0, 7], #[6, 7]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_030_before_decode"
  err.flush

theorem decode_geometry_Faces_030 :
    decodeFace geometryFacesJson030 = .ok geometryFacesTyped030 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_030_decoded"
  err.flush

noncomputable def geometryFacesJson031 : SourceJson :=
  (FaceLedgerBlock010.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped031 : FaceRecord :=
  { vertices := #[0, 6, 7, 14, 15, 18],
    dimension := 3, pivot := 18,
    facetSets := #[#[0, 6, 7], #[0, 6, 15, 18], #[0, 7, 14, 15], #[6, 7, 14, 18], #[14, 15, 18]],
    simplices := 3 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_031_before_decode"
  err.flush

theorem decode_geometry_Faces_031 :
    decodeFace geometryFacesJson031 = .ok geometryFacesTyped031 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_031_decoded"
  err.flush

noncomputable def geometryFacesJson032 : SourceJson :=
  (FaceLedgerBlock010.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped032 : FaceRecord :=
  { vertices := #[0, 6, 15, 18],
    dimension := 2, pivot := 18,
    facetSets := #[#[0, 6], #[0, 15], #[6, 18], #[15, 18]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_032_before_decode"
  err.flush

theorem decode_geometry_Faces_032 :
    decodeFace geometryFacesJson032 = .ok geometryFacesTyped032 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_032_decoded"
  err.flush

noncomputable def geometryFacesJson033 : SourceJson :=
  (FaceLedgerBlock010.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped033 : FaceRecord :=
  { vertices := #[0, 7],
    dimension := 1, pivot := 7,
    facetSets := #[#[0], #[7]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_033_before_decode"
  err.flush

theorem decode_geometry_Faces_033 :
    decodeFace geometryFacesJson033 = .ok geometryFacesTyped033 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_033_decoded"
  err.flush

noncomputable def geometryFacesJson034 : SourceJson :=
  (FaceLedgerBlock010.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped034 : FaceRecord :=
  { vertices := #[0, 7, 14, 15],
    dimension := 2, pivot := 15,
    facetSets := #[#[0, 7], #[0, 15], #[7, 14], #[14, 15]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_034_before_decode"
  err.flush

theorem decode_geometry_Faces_034 :
    decodeFace geometryFacesJson034 = .ok geometryFacesTyped034 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_034_decoded"
  err.flush

noncomputable def geometryFacesJson035 : SourceJson :=
  (FaceLedgerBlock010.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped035 : FaceRecord :=
  { vertices := #[0, 15],
    dimension := 1, pivot := 15,
    facetSets := #[#[0], #[15]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_035_before_decode"
  err.flush

theorem decode_geometry_Faces_035 :
    decodeFace geometryFacesJson035 = .ok geometryFacesTyped035 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_035_decoded"
  err.flush

noncomputable def geometryFacesJson036 : SourceJson :=
  (FaceLedgerBlock010.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped036 : FaceRecord :=
  { vertices := #[1, 3],
    dimension := 1, pivot := 3,
    facetSets := #[#[1], #[3]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_036_before_decode"
  err.flush

theorem decode_geometry_Faces_036 :
    decodeFace geometryFacesJson036 = .ok geometryFacesTyped036 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_036_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock010 : List SourceJson := [geometryFacesJson027, geometryFacesJson028, geometryFacesJson029, geometryFacesJson030, geometryFacesJson031, geometryFacesJson032, geometryFacesJson033, geometryFacesJson034, geometryFacesJson035, geometryFacesJson036]
noncomputable def geometryFacesTypedBlock010 : List (FaceRecord) := [geometryFacesTyped027, geometryFacesTyped028, geometryFacesTyped029, geometryFacesTyped030, geometryFacesTyped031, geometryFacesTyped032, geometryFacesTyped033, geometryFacesTyped034, geometryFacesTyped035, geometryFacesTyped036]
noncomputable def geometryFacesTypedThroughBlock010 : List (FaceRecord) := geometryFacesTypedThroughBlock009 ++ geometryFacesTypedBlock010

theorem geometry_Faces_block_010_push_eq (acc : List SourceJson) :
    FaceLedgerBlock010.blockPush acc = [geometryFacesJson036, geometryFacesJson035, geometryFacesJson034, geometryFacesJson033, geometryFacesJson032, geometryFacesJson031, geometryFacesJson030, geometryFacesJson029, geometryFacesJson028, geometryFacesJson027] ++ acc := by rfl

theorem geometry_Faces_block_010_reverse (acc : List SourceJson) :
    (FaceLedgerBlock010.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock010 := by
  rw [geometry_Faces_block_010_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_010 :
    geometryFacesJsonBlock010.mapM decodeFace = .ok geometryFacesTypedBlock010 := by
  simp only [geometryFacesJsonBlock010, geometryFacesTypedBlock010, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_027, decode_geometry_Faces_028, decode_geometry_Faces_029, decode_geometry_Faces_030, decode_geometry_Faces_031, decode_geometry_Faces_032, decode_geometry_Faces_033, decode_geometry_Faces_034, decode_geometry_Faces_035, decode_geometry_Faces_036]
  rfl

theorem decode_geometry_Faces_through_block_010 :
    FaceLedgerValue.arrayAcc011.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock010 := by
  change (FaceLedgerBlock010.blockPush FaceLedgerValue.arrayAcc010).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_010_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_009, decode_geometry_Faces_block_010]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_010_complete"
  err.flush

#print axioms decode_geometry_Faces_027
#print axioms decode_geometry_Faces_028
#print axioms decode_geometry_Faces_029
#print axioms decode_geometry_Faces_030
#print axioms decode_geometry_Faces_031
#print axioms decode_geometry_Faces_032
#print axioms decode_geometry_Faces_033
#print axioms decode_geometry_Faces_034
#print axioms decode_geometry_Faces_035
#print axioms decode_geometry_Faces_036
#print axioms geometry_Faces_block_010_push_eq
#print axioms geometry_Faces_block_010_reverse
#print axioms decode_geometry_Faces_block_010
#print axioms decode_geometry_Faces_through_block_010

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
