import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedFaces004
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedFaces005

/-! Balanced original face_ledger composition, leaf interval 4 through 5. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To005
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.FaceLedgerBlock005.blockPush (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.FaceLedgerBlock004.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 45) (SourceJson.white (sourceRest 108331)) acc =
      SourceJson.array (fuel + 24) (SourceJson.white (sourceRest 120220)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.FaceLedgerBlock004.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.FaceLedgerBlock005.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.FaceLedgerBlock004.blockPush acc))

noncomputable def jsonItems : List SourceJson := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryFacesJsonBlock004 ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryFacesJsonBlock005
noncomputable def typedItems : List (FaceRecord) := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryFacesTypedBlock004 ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryFacesTypedBlock005

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonItems := by
  unfold blockPush jsonItems
  rw [ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Faces_block_005_reverse, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Faces_block_004_reverse, List.append_assoc]

theorem original_items_decode : jsonItems.mapM decodeFace = .ok typedItems := by
  simp only [jsonItems, typedItems, List.mapM_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.decode_geometry_Faces_block_004, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.decode_geometry_Faces_block_005]
  rfl

theorem items_length : typedItems.length = 21 := by
  simp only [typedItems, List.length_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Faces_block_004_length, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Faces_block_005_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_items_decode
#print axioms items_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To005
