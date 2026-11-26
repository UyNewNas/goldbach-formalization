import ImbalancedChen.P2OriginalSaving19Geometry05ScalableTypedVertexValues000
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableTypedVertexValues001

/-! Balanced original vertex_values composition, leaf interval 0 through 1. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.VertexValuesNode000To001
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.VertexValuesBlock001.blockPush (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.VertexValuesBlock000.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 65) (SourceJson.white (sourceRest 47434)) acc =
      SourceJson.array (fuel + 49) (SourceJson.white (sourceRest 55106)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.VertexValuesBlock000.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.VertexValuesBlock001.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing.VertexValuesBlock000.blockPush acc))

noncomputable def jsonItems : List SourceJson := ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryVertexValuesJsonBlock000 ++ ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryVertexValuesJsonBlock001
noncomputable def typedItems : List (VertexValues) := ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryVertexValuesTypedBlock000 ++ ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometryVertexValuesTypedBlock001

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonItems := by
  unfold blockPush jsonItems
  rw [ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_VertexValues_block_001_reverse, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_VertexValues_block_000_reverse, List.append_assoc]

theorem original_items_decode : jsonItems.mapM decodeVertexValues = .ok typedItems := by
  simp only [jsonItems, typedItems, List.mapM_append, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.decode_geometry_VertexValues_block_000, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.decode_geometry_VertexValues_block_001]
  rfl

theorem items_length : typedItems.length = 16 := by
  simp only [typedItems, List.length_append, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_VertexValues_block_000_length, ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.geometry_VertexValues_block_001_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_items_decode
#print axioms items_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.VertexValuesNode000To001
