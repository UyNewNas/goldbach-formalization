import ImbalancedChen.P2OriginalSaving19Geometry05ScalableTypedFaces003
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableTypedFaces004

/-! Balanced original face_ledger composition, leaf interval 3 through 4. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode003To004
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.FaceLedgerBlock004.blockPush (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.FaceLedgerBlock003.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 33) (SourceJson.white (sourceRest 92965)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 104478) :=
  (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.FaceLedgerBlock003.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.FaceLedgerBlock004.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.FaceLedgerBlock003.blockPush acc))

noncomputable def jsonItems : List SourceJson := ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryFacesJsonBlock003 ++ ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryFacesJsonBlock004
noncomputable def typedItems : List (FaceRecord) := ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryFacesTypedBlock003 ++ ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryFacesTypedBlock004

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonItems := by
  unfold blockPush jsonItems
  rw [ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_Faces_block_004_reverse, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_Faces_block_003_reverse, List.append_assoc]

theorem original_items_decode : jsonItems.mapM decodeFace = .ok typedItems := by
  simp only [jsonItems, typedItems, List.mapM_append, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.decode_geometry_Faces_block_003, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.decode_geometry_Faces_block_004]
  rfl

theorem items_length : typedItems.length = 17 := by
  simp only [typedItems, List.length_append, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_Faces_block_003_length, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_Faces_block_004_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_items_decode
#print axioms items_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode003To004
