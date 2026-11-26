import ImbalancedChen.P2OriginalSaving19Geometry05ScalableTypedFaces000
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableTypedFaces001

/-! Balanced original face_ledger composition, leaf interval 0 through 1. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode000To001
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.FaceLedgerBlock001.blockPush (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.FaceLedgerBlock000.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 61) (SourceJson.white (sourceRest 65613)) acc =
      SourceJson.array (fuel + 43) (SourceJson.white (sourceRest 87821)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.FaceLedgerBlock000.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.FaceLedgerBlock001.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.FaceLedgerBlock000.blockPush acc))

noncomputable def jsonItems : List SourceJson := ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryFacesJsonBlock000 ++ ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryFacesJsonBlock001
noncomputable def typedItems : List (FaceRecord) := ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryFacesTypedBlock000 ++ ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryFacesTypedBlock001

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonItems := by
  unfold blockPush jsonItems
  rw [ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_Faces_block_001_reverse, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_Faces_block_000_reverse, List.append_assoc]

theorem original_items_decode : jsonItems.mapM decodeFace = .ok typedItems := by
  simp only [jsonItems, typedItems, List.mapM_append, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.decode_geometry_Faces_block_000, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.decode_geometry_Faces_block_001]
  rfl

theorem items_length : typedItems.length = 18 := by
  simp only [typedItems, List.length_append, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_Faces_block_000_length, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_Faces_block_001_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_items_decode
#print axioms items_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.FaceLedgerNode000To001
