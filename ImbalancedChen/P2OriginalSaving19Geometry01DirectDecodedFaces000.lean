import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFaceLedgerValue

/-! Original face_ledger typed block 0, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson000 : SourceJson :=
  (FaceLedgerBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped000 : FaceRecord :=
  { vertices := #[0, 1],
    dimension := 1, pivot := 1,
    facetSets := #[#[0], #[1]],
    simplices := 1 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_000_before_decode"
  err.flush

theorem decode_geometry_Faces_000 :
    decodeFace geometryFacesJson000 = .ok geometryFacesTyped000 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_000_decoded"
  err.flush

noncomputable def geometryFacesJson001 : SourceJson :=
  (FaceLedgerBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped001 : FaceRecord :=
  { vertices := #[0, 1, 2, 3],
    dimension := 2, pivot := 3,
    facetSets := #[#[0, 1], #[0, 2], #[1, 3], #[2, 3]],
    simplices := 2 }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_001_before_decode"
  err.flush

theorem decode_geometry_Faces_001 :
    decodeFace geometryFacesJson001 = .ok geometryFacesTyped001 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_001_decoded"
  err.flush

noncomputable def geometryFacesJsonBlock000 : List SourceJson := [geometryFacesJson000, geometryFacesJson001]
noncomputable def geometryFacesTypedBlock000 : List (FaceRecord) := [geometryFacesTyped000, geometryFacesTyped001]
noncomputable def geometryFacesTypedThroughBlock000 : List (FaceRecord) := geometryFacesTypedBlock000

theorem geometry_Faces_block_000_push_eq (acc : List SourceJson) :
    FaceLedgerBlock000.blockPush acc = [geometryFacesJson001, geometryFacesJson000] ++ acc := by rfl

theorem geometry_Faces_block_000_reverse (acc : List SourceJson) :
    (FaceLedgerBlock000.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock000 := by
  rw [geometry_Faces_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_000 :
    geometryFacesJsonBlock000.mapM decodeFace = .ok geometryFacesTypedBlock000 := by
  simp only [geometryFacesJsonBlock000, geometryFacesTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_000, decode_geometry_Faces_001]
  rfl

theorem decode_geometry_Faces_through_block_000 :
    FaceLedgerValue.arrayAcc001.reverse.mapM decodeFace = .ok geometryFacesTypedThroughBlock000 := by
  change (FaceLedgerBlock000.blockPush FaceLedgerValue.arrayAcc000).reverse.mapM decodeFace = _
  rw [geometry_Faces_block_000_reverse]
  exact decode_geometry_Faces_block_000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Faces_block_000_complete"
  err.flush

#print axioms decode_geometry_Faces_000
#print axioms decode_geometry_Faces_001
#print axioms geometry_Faces_block_000_push_eq
#print axioms geometry_Faces_block_000_reverse
#print axioms decode_geometry_Faces_block_000
#print axioms decode_geometry_Faces_through_block_000

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
