import ImbalancedChen.P2OriginalSaving19Geometry05ScalableTypedRows002
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableTypedRows003

/-! Balanced original cell 05 row parser and typed-list composition.
Only the original simplices array is assembled here; whole geometry decoding
and all geometric or integral claims remain outside this owner. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.Node002To003
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  SimplicesBlock003.blockPush (SimplicesBlock002.blockPush acc)
noncomputable def jsonRows : List SourceJson := geometryRowsJsonBlock002 ++ geometryRowsJsonBlock003
noncomputable def typedRows : List GeometryRow := geometryRowsTypedBlock002 ++ geometryRowsTypedBlock003

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 457) (SourceJson.white (sourceRest 131386)) acc =
      SourceJson.array (fuel + 441) (SourceJson.white (sourceRest 159861)) (blockPush acc) :=
  (SimplicesBlock002.array_block_original fuel acc).trans
    (SimplicesBlock003.array_block_original fuel (SimplicesBlock002.blockPush acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [geometry_Rows_block_003_reverse, geometry_Rows_block_002_reverse, List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append, decode_geometry_Rows_block_002, decode_geometry_Rows_block_003]
  rfl

theorem rows_length : typedRows.length = 16 := by
  simp only [typedRows, List.length_append, geometry_Rows_block_002_length, geometry_Rows_block_003_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_rows_decode
#print axioms rows_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.Node002To003
