import ImbalancedChen.P2OriginalSaving19Geometry06ScalableRowsNode008To009
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableRowsNode010To011

/-! Balanced original cell 06 row parser and typed-list composition.
Only the original simplices array is assembled here; whole geometry decoding
and all geometric or integral claims remain outside this owner. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node008To011
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  Node010To011.blockPush (Node008To009.blockPush acc)
noncomputable def jsonRows : List SourceJson := Node008To009.jsonRows ++ Node010To011.jsonRows
noncomputable def typedRows : List GeometryRow := Node008To009.typedRows ++ Node010To011.typedRows

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 593) (SourceJson.white (sourceRest 246480)) acc =
      SourceJson.array (fuel + 561) (SourceJson.white (sourceRest 305248)) (blockPush acc) :=
  (Node008To009.array_original fuel acc).trans
    (Node010To011.array_original fuel (Node008To009.blockPush acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [Node010To011.blockPush_reverse, Node008To009.blockPush_reverse, List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append, Node008To009.original_rows_decode, Node010To011.original_rows_decode]
  rfl

theorem rows_length : typedRows.length = 32 := by
  simp only [typedRows, List.length_append, Node008To009.rows_length, Node010To011.rows_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_rows_decode
#print axioms rows_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node008To011
