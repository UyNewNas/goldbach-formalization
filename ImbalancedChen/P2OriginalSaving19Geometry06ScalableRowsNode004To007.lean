import ImbalancedChen.P2OriginalSaving19Geometry06ScalableRowsNode004To005
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableRowsNode006To007

/-! Balanced original cell 06 row parser and typed-list composition.
Only the original simplices array is assembled here; whole geometry decoding
and all geometric or integral claims remain outside this owner. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node004To007
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  Node006To007.blockPush (Node004To005.blockPush acc)
noncomputable def jsonRows : List SourceJson := Node004To005.jsonRows ++ Node006To007.jsonRows
noncomputable def typedRows : List GeometryRow := Node004To005.typedRows ++ Node006To007.typedRows

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 625) (SourceJson.white (sourceRest 185891)) acc =
      SourceJson.array (fuel + 593) (SourceJson.white (sourceRest 246480)) (blockPush acc) :=
  (Node004To005.array_original fuel acc).trans
    (Node006To007.array_original fuel (Node004To005.blockPush acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [Node006To007.blockPush_reverse, Node004To005.blockPush_reverse, List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append, Node004To005.original_rows_decode, Node006To007.original_rows_decode]
  rfl

theorem rows_length : typedRows.length = 32 := by
  simp only [typedRows, List.length_append, Node004To005.rows_length, Node006To007.rows_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_rows_decode
#print axioms rows_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node004To007
