import ImbalancedChen.P2OriginalSaving19Geometry05ScalableTypedVertexValues002
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableTypedVertexValues003

/-! Balanced original vertex_values composition, leaf interval 2 through 3. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.VertexValuesNode002To003
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.VertexValuesBlock003.blockPush (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.VertexValuesBlock002.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 49) (SourceJson.white (sourceRest 55106)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 60862) :=
  (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.VertexValuesBlock002.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.VertexValuesBlock003.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.VertexValuesBlock002.blockPush acc))

noncomputable def jsonItems : List SourceJson := ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryVertexValuesJsonBlock002 ++ ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryVertexValuesJsonBlock003
noncomputable def typedItems : List (VertexValues) := ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryVertexValuesTypedBlock002 ++ ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryVertexValuesTypedBlock003

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonItems := by
  unfold blockPush jsonItems
  rw [ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_VertexValues_block_003_reverse, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_VertexValues_block_002_reverse, List.append_assoc]

theorem original_items_decode : jsonItems.mapM decodeVertexValues = .ok typedItems := by
  simp only [jsonItems, typedItems, List.mapM_append, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.decode_geometry_VertexValues_block_002, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.decode_geometry_VertexValues_block_003]
  rfl

theorem items_length : typedItems.length = 12 := by
  simp only [typedItems, List.length_append, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_VertexValues_block_002_length, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_VertexValues_block_003_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_items_decode
#print axioms items_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.VertexValuesNode002To003
