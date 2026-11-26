import ImbalancedChen.P2OriginalSaving19Geometry05ScalableRowsNode004To005
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableTypedRows006

/-! Balanced original cell 05 row parser and typed-list composition.
Only the original simplices array is assembled here; whole geometry decoding
and all geometric or integral claims remain outside this owner. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.Node004To006
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  SimplicesBlock006.blockPush (Node004To005.blockPush acc)
noncomputable def jsonRows : List SourceJson := Node004To005.jsonRows ++ geometryRowsJsonBlock006
noncomputable def typedRows : List GeometryRow := Node004To005.typedRows ++ geometryRowsTypedBlock006

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 441) (SourceJson.white (sourceRest 159861)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 200699) :=
  (Node004To005.array_original fuel acc).trans
    (SimplicesBlock006.array_block_original fuel (Node004To005.blockPush acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [geometry_Rows_block_006_reverse, Node004To005.blockPush_reverse, List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append, Node004To005.original_rows_decode, decode_geometry_Rows_block_006]
  rfl

theorem rows_length : typedRows.length = 24 := by
  simp only [typedRows, List.length_append, Node004To005.rows_length, geometry_Rows_block_006_length]

theorem array_empty_original (fuel : Nat) :
    SourceJson.array (fuel + 441) (SourceJson.white (sourceRest 159861)) [] =
      .ok (.arr jsonRows, sourceRest 200699) := by
  rw [array_original, blockPush_reverse, List.reverse_nil, List.nil_append]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_rows_decode
#print axioms rows_length
#print axioms array_empty_original
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.Node004To006
