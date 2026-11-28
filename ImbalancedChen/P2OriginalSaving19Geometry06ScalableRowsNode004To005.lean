import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedRows004
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedRows005

/-! Balanced original cell 06 row parser and typed-list composition.
Only the original simplices array is assembled here; whole geometry decoding
and all geometric or integral claims remain outside this owner. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node004To005
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  SimplicesBlock005.blockPush (SimplicesBlock004.blockPush acc)
noncomputable def jsonRows : List SourceJson := geometryRowsJsonBlock004 ++ geometryRowsJsonBlock005
noncomputable def typedRows : List GeometryRow := geometryRowsTypedBlock004 ++ geometryRowsTypedBlock005

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 625) (SourceJson.white (sourceRest 185891)) acc =
      SourceJson.array (fuel + 609) (SourceJson.white (sourceRest 216580)) (blockPush acc) :=
  (SimplicesBlock004.array_block_original fuel acc).trans
    (SimplicesBlock005.array_block_original fuel (SimplicesBlock004.blockPush acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [geometry_Rows_block_005_reverse, geometry_Rows_block_004_reverse, List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append, decode_geometry_Rows_block_004, decode_geometry_Rows_block_005]
  rfl

theorem rows_length : typedRows.length = 16 := by
  simp only [typedRows, List.length_append, geometry_Rows_block_004_length, geometry_Rows_block_005_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_rows_decode
#print axioms rows_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node004To005
