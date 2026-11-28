import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedRows012
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedRows013

/-! Balanced original cell 06 row parser and typed-list composition.
Only the original simplices array is assembled here; whole geometry decoding
and all geometric or integral claims remain outside this owner. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node012To013
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  SimplicesBlock013.blockPush (SimplicesBlock012.blockPush acc)
noncomputable def jsonRows : List SourceJson := geometryRowsJsonBlock012 ++ geometryRowsJsonBlock013
noncomputable def typedRows : List GeometryRow := geometryRowsTypedBlock012 ++ geometryRowsTypedBlock013

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 561) (SourceJson.white (sourceRest 305248)) acc =
      SourceJson.array (fuel + 545) (SourceJson.white (sourceRest 333878)) (blockPush acc) :=
  (SimplicesBlock012.array_block_original fuel acc).trans
    (SimplicesBlock013.array_block_original fuel (SimplicesBlock012.blockPush acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [geometry_Rows_block_013_reverse, geometry_Rows_block_012_reverse, List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append, decode_geometry_Rows_block_012, decode_geometry_Rows_block_013]
  rfl

theorem rows_length : typedRows.length = 16 := by
  simp only [typedRows, List.length_append, geometry_Rows_block_012_length, geometry_Rows_block_013_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_rows_decode
#print axioms rows_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node012To013
