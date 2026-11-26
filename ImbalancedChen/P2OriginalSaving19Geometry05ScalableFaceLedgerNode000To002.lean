import ImbalancedChen.P2OriginalSaving19Geometry05ScalableFaceLedgerNode000To001
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableTypedFaces002

/-! Balanced original face_ledger composition, leaf interval 0 through 2. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode000To002
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.FaceLedgerBlock002.blockPush (ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode000To001.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 61) (SourceJson.white (sourceRest 65613)) acc =
      SourceJson.array (fuel + 33) (SourceJson.white (sourceRest 92965)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode000To001.array_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.FaceLedgerBlock002.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode000To001.blockPush acc))

noncomputable def jsonItems : List SourceJson := ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode000To001.jsonItems ++ ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryFacesJsonBlock002
noncomputable def typedItems : List (FaceRecord) := ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode000To001.typedItems ++ ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryFacesTypedBlock002

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonItems := by
  unfold blockPush jsonItems
  rw [ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_Faces_block_002_reverse, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode000To001.blockPush_reverse, List.append_assoc]

theorem original_items_decode : jsonItems.mapM decodeFace = .ok typedItems := by
  simp only [jsonItems, typedItems, List.mapM_append, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode000To001.original_items_decode, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.decode_geometry_Faces_block_002]
  rfl

theorem items_length : typedItems.length = 28 := by
  simp only [typedItems, List.length_append, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode000To001.items_length, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_Faces_block_002_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_items_decode
#print axioms items_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode000To002
