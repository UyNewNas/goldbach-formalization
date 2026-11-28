import ImbalancedChen.P2OriginalSaving19Geometry06ScalableVertexValuesNode000To002
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableVertexValuesNode003To004

/-! Balanced original vertex_values composition, leaf interval 0 through 4. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode000To004
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode003To004.blockPush (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode000To002.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 69) (SourceJson.white (sourceRest 48363)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 63938) :=
  (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode000To002.array_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode003To004.array_original fuel (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode000To002.blockPush acc))

noncomputable def jsonItems : List SourceJson := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode000To002.jsonItems ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode003To004.jsonItems
noncomputable def typedItems : List (VertexValues) := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode000To002.typedItems ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode003To004.typedItems

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonItems := by
  unfold blockPush jsonItems
  rw [ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode003To004.blockPush_reverse, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode000To002.blockPush_reverse, List.append_assoc]

theorem original_items_decode : jsonItems.mapM decodeVertexValues = .ok typedItems := by
  simp only [jsonItems, typedItems, List.mapM_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode000To002.original_items_decode, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode003To004.original_items_decode]
  rfl

theorem items_length : typedItems.length = 33 := by
  simp only [typedItems, List.length_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode000To002.items_length, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode003To004.items_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_items_decode
#print axioms items_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode000To004
