import ImbalancedChen.P2OriginalSaving19Geometry06ScalableRowsNode012To013
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedRows014

/-! Balanced original cell 06 row parser and typed-list composition.
Only the original simplices array is assembled here; whole geometry decoding
and all geometric or integral claims remain outside this owner. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node012To014
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  SimplicesBlock014.blockPush (Node012To013.blockPush acc)
noncomputable def jsonRows : List SourceJson := Node012To013.jsonRows ++ geometryRowsJsonBlock014
noncomputable def typedRows : List GeometryRow := Node012To013.typedRows ++ geometryRowsTypedBlock014

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 561) (SourceJson.white (sourceRest 305248)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 335468) :=
  (Node012To013.array_original fuel acc).trans
    (SimplicesBlock014.array_block_original fuel (Node012To013.blockPush acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [geometry_Rows_block_014_reverse, Node012To013.blockPush_reverse, List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append, Node012To013.original_rows_decode, decode_geometry_Rows_block_014]
  rfl

theorem rows_length : typedRows.length = 17 := by
  simp only [typedRows, List.length_append, Node012To013.rows_length, geometry_Rows_block_014_length]

theorem array_empty_original (fuel : Nat) :
    SourceJson.array (fuel + 561) (SourceJson.white (sourceRest 305248)) [] =
      .ok (.arr jsonRows, sourceRest 335468) := by
  rw [array_original, blockPush_reverse, List.reverse_nil, List.nil_append]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_rows_decode
#print axioms rows_length
#print axioms array_empty_original
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node012To014
