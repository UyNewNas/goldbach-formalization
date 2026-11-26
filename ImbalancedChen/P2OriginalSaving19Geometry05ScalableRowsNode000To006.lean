import ImbalancedChen.P2OriginalSaving19Geometry05ScalableRowsNode000To003
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableRowsNode004To006

/-! Balanced original cell 05 row parser and typed-list composition.
Only the original simplices array is assembled here; whole geometry decoding
and all geometric or integral claims remain outside this owner. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.Node000To006
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  Node004To006.blockPush (Node000To003.blockPush acc)
noncomputable def jsonRows : List SourceJson := Node000To003.jsonRows ++ Node004To006.jsonRows
noncomputable def typedRows : List GeometryRow := Node000To003.typedRows ++ Node004To006.typedRows

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 473) (SourceJson.white (sourceRest 104497)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 200699) :=
  (Node000To003.array_original fuel acc).trans
    (Node004To006.array_original fuel (Node000To003.blockPush acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [Node004To006.blockPush_reverse, Node000To003.blockPush_reverse, List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append, Node000To003.original_rows_decode, Node004To006.original_rows_decode]
  rfl

theorem rows_length : typedRows.length = 56 := by
  simp only [typedRows, List.length_append, Node000To003.rows_length, Node004To006.rows_length]

theorem array_empty_original (fuel : Nat) :
    SourceJson.array (fuel + 473) (SourceJson.white (sourceRest 104497)) [] =
      .ok (.arr jsonRows, sourceRest 200699) := by
  rw [array_original, blockPush_reverse, List.reverse_nil, List.nil_append]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_rows_decode
#print axioms rows_length
#print axioms array_empty_original
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.Node000To006
