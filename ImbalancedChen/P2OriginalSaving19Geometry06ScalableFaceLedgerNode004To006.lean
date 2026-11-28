import ImbalancedChen.P2OriginalSaving19Geometry06ScalableFaceLedgerNode004To005
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedFaces006

/-! Balanced original face_ledger composition, leaf interval 4 through 6. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To006
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.FaceLedgerBlock006.blockPush (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To005.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 45) (SourceJson.white (sourceRest 108331)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 124012) :=
  (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To005.array_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.FaceLedgerBlock006.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To005.blockPush acc))

noncomputable def jsonItems : List SourceJson := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To005.jsonItems ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryFacesJsonBlock006
noncomputable def typedItems : List (FaceRecord) := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To005.typedItems ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryFacesTypedBlock006

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonItems := by
  unfold blockPush jsonItems
  rw [ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Faces_block_006_reverse, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To005.blockPush_reverse, List.append_assoc]

theorem original_items_decode : jsonItems.mapM decodeFace = .ok typedItems := by
  simp only [jsonItems, typedItems, List.mapM_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To005.original_items_decode, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.decode_geometry_Faces_block_006]
  rfl

theorem items_length : typedItems.length = 27 := by
  simp only [typedItems, List.length_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To005.items_length, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Faces_block_006_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_items_decode
#print axioms items_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To006
