import ImbalancedChen.P2OriginalSaving19Geometry06ScalableFaceLedgerNode000To003
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableFaceLedgerNode004To006

/-! Balanced original face_ledger composition, leaf interval 0 through 6. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode000To006
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To006.blockPush (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode000To003.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 80) (SourceJson.white (sourceRest 69088)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 124012) :=
  (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode000To003.array_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To006.array_original fuel (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode000To003.blockPush acc))

noncomputable def jsonItems : List SourceJson := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode000To003.jsonItems ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To006.jsonItems
noncomputable def typedItems : List (FaceRecord) := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode000To003.typedItems ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To006.typedItems

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonItems := by
  unfold blockPush jsonItems
  rw [ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To006.blockPush_reverse, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode000To003.blockPush_reverse, List.append_assoc]

theorem original_items_decode : jsonItems.mapM decodeFace = .ok typedItems := by
  simp only [jsonItems, typedItems, List.mapM_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode000To003.original_items_decode, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To006.original_items_decode]
  rfl

theorem items_length : typedItems.length = 62 := by
  simp only [typedItems, List.length_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode000To003.items_length, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode004To006.items_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_items_decode
#print axioms items_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode000To006
