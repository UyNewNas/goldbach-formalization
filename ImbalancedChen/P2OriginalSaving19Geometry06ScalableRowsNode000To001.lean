import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedRows000
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedRows001

/-! Balanced original cell 06 row parser and typed-list composition.
Only the original simplices array is assembled here; whole geometry decoding
and all geometric or integral claims remain outside this owner. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node000To001
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  SimplicesBlock001.blockPush (SimplicesBlock000.blockPush acc)
noncomputable def jsonRows : List SourceJson := geometryRowsJsonBlock000 ++ geometryRowsJsonBlock001
noncomputable def typedRows : List GeometryRow := geometryRowsTypedBlock000 ++ geometryRowsTypedBlock001

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 657) (SourceJson.white (sourceRest 124031)) acc =
      SourceJson.array (fuel + 641) (SourceJson.white (sourceRest 155525)) (blockPush acc) :=
  (SimplicesBlock000.array_block_original fuel acc).trans
    (SimplicesBlock001.array_block_original fuel (SimplicesBlock000.blockPush acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [geometry_Rows_block_001_reverse, geometry_Rows_block_000_reverse, List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append, decode_geometry_Rows_block_000, decode_geometry_Rows_block_001]
  rfl

theorem rows_length : typedRows.length = 16 := by
  simp only [typedRows, List.length_append, geometry_Rows_block_000_length, geometry_Rows_block_001_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_rows_decode
#print axioms rows_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node000To001
