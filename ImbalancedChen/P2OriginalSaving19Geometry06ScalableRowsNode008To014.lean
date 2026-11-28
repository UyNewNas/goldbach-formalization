import ImbalancedChen.P2OriginalSaving19Geometry06ScalableRowsNode008To011
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableRowsNode012To014

/-! Balanced original cell 06 row parser and typed-list composition.
Only the original simplices array is assembled here; whole geometry decoding
and all geometric or integral claims remain outside this owner. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node008To014
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  Node012To014.blockPush (Node008To011.blockPush acc)
noncomputable def jsonRows : List SourceJson := Node008To011.jsonRows ++ Node012To014.jsonRows
noncomputable def typedRows : List GeometryRow := Node008To011.typedRows ++ Node012To014.typedRows

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 593) (SourceJson.white (sourceRest 246480)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 335468) :=
  (Node008To011.array_original fuel acc).trans
    (Node012To014.array_original fuel (Node008To011.blockPush acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [Node012To014.blockPush_reverse, Node008To011.blockPush_reverse, List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append, Node008To011.original_rows_decode, Node012To014.original_rows_decode]
  rfl

theorem rows_length : typedRows.length = 49 := by
  simp only [typedRows, List.length_append, Node008To011.rows_length, Node012To014.rows_length]

theorem array_empty_original (fuel : Nat) :
    SourceJson.array (fuel + 593) (SourceJson.white (sourceRest 246480)) [] =
      .ok (.arr jsonRows, sourceRest 335468) := by
  rw [array_original, blockPush_reverse, List.reverse_nil, List.nil_append]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_rows_decode
#print axioms rows_length
#print axioms array_empty_original
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node008To014
