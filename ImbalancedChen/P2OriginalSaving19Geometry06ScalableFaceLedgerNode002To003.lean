import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedFaces002
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedFaces003

/-! Balanced original face_ledger composition, leaf interval 2 through 3. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode002To003
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.FaceLedgerBlock003.blockPush (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.FaceLedgerBlock002.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 63) (SourceJson.white (sourceRest 94527)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white (sourceRest 108331)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.FaceLedgerBlock002.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.FaceLedgerBlock003.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.FaceLedgerBlock002.blockPush acc))

noncomputable def jsonItems : List SourceJson := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryFacesJsonBlock002 ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryFacesJsonBlock003
noncomputable def typedItems : List (FaceRecord) := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryFacesTypedBlock002 ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryFacesTypedBlock003

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonItems := by
  unfold blockPush jsonItems
  rw [ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Faces_block_003_reverse, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Faces_block_002_reverse, List.append_assoc]

theorem original_items_decode : jsonItems.mapM decodeFace = .ok typedItems := by
  simp only [jsonItems, typedItems, List.mapM_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.decode_geometry_Faces_block_002, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.decode_geometry_Faces_block_003]
  rfl

theorem items_length : typedItems.length = 18 := by
  simp only [typedItems, List.length_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Faces_block_002_length, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Faces_block_003_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_items_decode
#print axioms items_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode002To003
