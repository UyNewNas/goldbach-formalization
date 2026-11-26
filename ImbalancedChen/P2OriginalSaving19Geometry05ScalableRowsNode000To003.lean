import ImbalancedChen.P2OriginalSaving19Geometry05ScalableRowsNode000To001
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableRowsNode002To003

/-! Balanced original cell 05 row parser and typed-list composition.
Only the original simplices array is assembled here; whole geometry decoding
and all geometric or integral claims remain outside this owner. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.Node000To003
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  Node002To003.blockPush (Node000To001.blockPush acc)
noncomputable def jsonRows : List SourceJson := Node000To001.jsonRows ++ Node002To003.jsonRows
noncomputable def typedRows : List GeometryRow := Node000To001.typedRows ++ Node002To003.typedRows

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 473) (SourceJson.white (sourceRest 104497)) acc =
      SourceJson.array (fuel + 441) (SourceJson.white (sourceRest 159861)) (blockPush acc) :=
  (Node000To001.array_original fuel acc).trans
    (Node002To003.array_original fuel (Node000To001.blockPush acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [Node002To003.blockPush_reverse, Node000To001.blockPush_reverse, List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append, Node000To001.original_rows_decode, Node002To003.original_rows_decode]
  rfl

theorem rows_length : typedRows.length = 32 := by
  simp only [typedRows, List.length_append, Node000To001.rows_length, Node002To003.rows_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_rows_decode
#print axioms rows_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.Node000To003
