import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedVertexValues003
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedVertexValues004

/-! Balanced original vertex_values composition, leaf interval 3 through 4. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode003To004
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.VertexValuesBlock004.blockPush (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.VertexValuesBlock003.blockPush acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 45) (SourceJson.white (sourceRest 59698)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 63938) :=
  (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.VertexValuesBlock003.array_block_original fuel acc).trans
    (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.VertexValuesBlock004.array_block_original fuel (ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.VertexValuesBlock003.blockPush acc))

noncomputable def jsonItems : List SourceJson := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryVertexValuesJsonBlock003 ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryVertexValuesJsonBlock004
noncomputable def typedItems : List (VertexValues) := ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryVertexValuesTypedBlock003 ++ ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometryVertexValuesTypedBlock004

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonItems := by
  unfold blockPush jsonItems
  rw [ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_VertexValues_block_004_reverse, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_VertexValues_block_003_reverse, List.append_assoc]

theorem original_items_decode : jsonItems.mapM decodeVertexValues = .ok typedItems := by
  simp only [jsonItems, typedItems, List.mapM_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.decode_geometry_VertexValues_block_003, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.decode_geometry_VertexValues_block_004]
  rfl

theorem items_length : typedItems.length = 9 := by
  simp only [typedItems, List.length_append, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_VertexValues_block_003_length, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.geometry_VertexValues_block_004_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_items_decode
#print axioms items_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.VertexValuesNode003To004
