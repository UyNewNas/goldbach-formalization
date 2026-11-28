import ImbalancedChen.P2OriginalSaving19Geometry06ScalableRowsNode000To007
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableRowsNode008To014

/-! Balanced original cell 06 row parser and typed-list composition.
Only the original simplices array is assembled here; whole geometry decoding
and all geometric or integral claims remain outside this owner. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node000To014
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  Node008To014.blockPush (Node000To007.blockPush acc)
noncomputable def jsonRows : List SourceJson := Node000To007.jsonRows ++ Node008To014.jsonRows
noncomputable def typedRows : List GeometryRow := Node000To007.typedRows ++ Node008To014.typedRows

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 657) (SourceJson.white (sourceRest 124031)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 335468) :=
  (Node000To007.array_original fuel acc).trans
    (Node008To014.array_original fuel (Node000To007.blockPush acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [Node008To014.blockPush_reverse, Node000To007.blockPush_reverse, List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append, Node000To007.original_rows_decode, Node008To014.original_rows_decode]
  rfl

theorem rows_length : typedRows.length = 113 := by
  simp only [typedRows, List.length_append, Node000To007.rows_length, Node008To014.rows_length]

theorem array_empty_original (fuel : Nat) :
    SourceJson.array (fuel + 657) (SourceJson.white (sourceRest 124031)) [] =
      .ok (.arr jsonRows, sourceRest 335468) := by
  rw [array_original, blockPush_reverse, List.reverse_nil, List.nil_append]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_rows_decode
#print axioms rows_length
#print axioms array_empty_original
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.Node000To014
