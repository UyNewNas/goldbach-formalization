import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces008

/-! Original face_ledger typed block 9, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson021 : SourceJson :=
  (FaceLedgerBlock009.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped021 : FaceRecord :=
  { vertices := #[0, 2, 4, 12],
    dimension := 2, pivot := 12,
    facetSets := #[#[0, 2], #[0, 12], #[2, 4], #[4, 12]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_021_before_decode"
  err.flush

theorem decode_geometry_Faces_021 :
    decodeFace geometryFacesJson021 = .ok geometryFacesTyped021 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_021_decoded"
  err.flush

noncomputable def geometryFacesJson022 : SourceJson :=
  (FaceLedgerBlock009.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped022 : FaceRecord :=
  { vertices := #[0, 2, 6],
    dimension := 2, pivot := 6,
    facetSets := #[#[0, 2], #[0, 6], #[2, 6]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_022_before_decode"
  err.flush

theorem decode_geometry_Faces_022 :
    decodeFace geometryFacesJson022 = .ok geometryFacesTyped022 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_022_decoded"
  err.flush

noncomputable def geometryFacesJson023 : SourceJson :=
  (FaceLedgerBlock009.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped023 : FaceRecord :=
  { vertices := #[0, 2, 6, 7],
    dimension := 3, pivot := 7,
    facetSets := #[#[0, 2, 6], #[0, 2, 7], #[0, 6, 7], #[2, 6, 7]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_023_before_decode"
  err.flush

theorem decode_geometry_Faces_023 :
    decodeFace geometryFacesJson023 = .ok geometryFacesTyped023 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_023_decoded"
  err.flush

noncomputable def geometryFacesJson024 : SourceJson :=
  (FaceLedgerBlock009.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped024 : FaceRecord :=
  { vertices := #[0, 2, 6, 7, 9],
    dimension := 4, pivot := 9,
    facetSets := #[#[0, 2, 6, 7], #[0, 2, 6, 9], #[0, 2, 7, 9], #[0, 6, 7, 9], #[2, 6, 7, 9]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_024_before_decode"
  err.flush

theorem decode_geometry_Faces_024 :
    decodeFace geometryFacesJson024 = .ok geometryFacesTyped024 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_024_decoded"
  err.flush

noncomputable def geometryFacesJson025 : SourceJson :=
  (FaceLedgerBlock009.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped025 : FaceRecord :=
  { vertices := #[0, 2, 6, 7, 9, 14, 15, 18, 19, 22],
    dimension := 5, pivot := 22,
    facetSets := #[#[0, 2, 6, 7, 9], #[0, 2, 6, 7, 14, 15, 18, 19], #[0, 2, 6, 9, 15, 18, 19, 22], #[0, 2, 7, 9, 14, 15, 19, 22], #[0, 6, 7, 9, 14, 15, 18, 22], #[2, 6, 7, 9, 14, 18, 19, 22], #[14, 15, 18, 19, 22]],
    simplices := 5 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_025_before_decode"
  err.flush

theorem decode_geometry_Faces_025 :
    decodeFace geometryFacesJson025 = .ok geometryFacesTyped025 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_025_decoded"
  err.flush

noncomputable def geometryFacesJson026 : SourceJson :=
  (FaceLedgerBlock009.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped026 : FaceRecord :=
  { vertices := #[0, 2, 6, 7, 14, 15, 18, 19],
    dimension := 4, pivot := 19,
    facetSets := #[#[0, 2, 6, 7], #[0, 2, 6, 15, 18, 19], #[0, 2, 7, 14, 15, 19], #[0, 6, 7, 14, 15, 18], #[2, 6, 7, 14, 18, 19], #[14, 15, 18, 19]],
    simplices := 4 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_026_before_decode"
  err.flush

theorem decode_geometry_Faces_026 :
    decodeFace geometryFacesJson026 = .ok geometryFacesTyped026 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_026_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock009 : List SourceJson := [geometryFacesJson021, geometryFacesJson022, geometryFacesJson023, geometryFacesJson024, geometryFacesJson025, geometryFacesJson026]
noncomputable def geometryFacesTypedBlock009 : List (FaceRecord) := [geometryFacesTyped021, geometryFacesTyped022, geometryFacesTyped023, geometryFacesTyped024, geometryFacesTyped025, geometryFacesTyped026]
noncomputable def geometryFacesTypedThroughBlock009 : List (FaceRecord) := geometryFacesTypedThroughBlock008 ++ geometryFacesTypedBlock009

theorem geometry_Faces_block_009_push_eq (acc : List SourceJson) :
    FaceLedgerBlock009.blockPush acc = [geometryFacesJson026, geometryFacesJson025, geometryFacesJson024, geometryFacesJson023, geometryFacesJson022, geometryFacesJson021] ++ acc := by rfl

theorem geometry_Faces_block_009_reverse (acc : List SourceJson) :
    (FaceLedgerBlock009.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock009 := by
  rw [geometry_Faces_block_009_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_009 :
    geometryFacesJsonBlock009.mapM decodeFace = .ok geometryFacesTypedBlock009 := by
  simp only [geometryFacesJsonBlock009, geometryFacesTypedBlock009, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_021, decode_geometry_Faces_022, decode_geometry_Faces_023, decode_geometry_Faces_024, decode_geometry_Faces_025, decode_geometry_Faces_026]
  rfl

theorem decode_geometry_Faces_through_block_009 :
    FaceLedgerValue.arrayAcc010.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock009 := by
  change (FaceLedgerBlock009.blockPush FaceLedgerValue.arrayAcc009).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_009_reverse]
  rw [List.mapM_append, decode_geometry_Faces_through_block_008, decode_geometry_Faces_block_009]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_009_complete"
  err.flush

#print axioms decode_geometry_Faces_021
#print axioms decode_geometry_Faces_022
#print axioms decode_geometry_Faces_023
#print axioms decode_geometry_Faces_024
#print axioms decode_geometry_Faces_025
#print axioms decode_geometry_Faces_026
#print axioms geometry_Faces_block_009_push_eq
#print axioms geometry_Faces_block_009_reverse
#print axioms decode_geometry_Faces_block_009
#print axioms decode_geometry_Faces_through_block_009

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
