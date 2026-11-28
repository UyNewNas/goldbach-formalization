import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedVertices000
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedVertices001

/-! Balanced original vertices composition, leaf interval 0 through 1. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VerticesNode000To001
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.VerticesBlock001.blockPush (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.VerticesBlock000.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 60) (SourceJson.white (sourceRest 41119)) acc =
      SourceJson.array (fuel + 28) (SourceJson.white (sourceRest 48119)) (blockPush acc) :=
  (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.VerticesBlock000.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.VerticesBlock001.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.VerticesBlock000.blockPush acc))

noncomputable def jsonItems : List SourceJson := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryVerticesJsonBlock000 ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryVerticesJsonBlock001
noncomputable def typedItems : List (Array ℚ) := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryVerticesTypedBlock000 ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryVerticesTypedBlock001

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonItems := by
  unfold blockPush jsonItems
  rw [ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Vertices_block_001_reverse, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Vertices_block_000_reverse, List.append_assoc]

theorem original_items_decode : jsonItems.mapM rationalArray = .ok typedItems := by
  simp only [jsonItems, typedItems, List.mapM_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.decode_geometry_Vertices_block_000, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.decode_geometry_Vertices_block_001]
  rfl

theorem items_length : typedItems.length = 32 := by
  simp only [typedItems, List.length_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Vertices_block_000_length, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_Vertices_block_001_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_items_decode
#print axioms items_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VerticesNode000To001
