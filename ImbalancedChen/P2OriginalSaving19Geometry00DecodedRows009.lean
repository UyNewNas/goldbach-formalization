import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows008
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00900
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow036
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow037
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow038
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow039

/-! Original GeometryRow block 9: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_036_push_eq (acc : List SourceJson) :
    simplicesChunk036Push00 acc = [geometryRowsJson036] ++ acc := by rfl

theorem geometry_Rows_chunk_037_push_eq (acc : List SourceJson) :
    simplicesChunk037Push00 acc = [geometryRowsJson037] ++ acc := by rfl

theorem geometry_Rows_chunk_038_push_eq (acc : List SourceJson) :
    simplicesChunk038Push00 acc = [geometryRowsJson038] ++ acc := by rfl

theorem geometry_Rows_chunk_039_push_eq (acc : List SourceJson) :
    simplicesChunk039Push00 acc = [geometryRowsJson039] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock009 : List SourceJson := [geometryRowsJson036, geometryRowsJson037, geometryRowsJson038, geometryRowsJson039]
noncomputable def geometryRowsTypedBlock009 : List GeometryRow := [geometryRowsTyped036, geometryRowsTyped037, geometryRowsTyped038, geometryRowsTyped039]
noncomputable def geometryRowsBlock009Push (acc : List SourceJson) : List SourceJson := simplicesChunk039Push00 (simplicesChunk038Push00 (simplicesChunk037Push00 (simplicesChunk036Push00 (acc))))

theorem geometry_Rows_block_009_push_eq (acc : List SourceJson) :
    geometryRowsBlock009Push acc = [geometryRowsJson039, geometryRowsJson038, geometryRowsJson037, geometryRowsJson036] ++ acc := by rfl

theorem geometry_Rows_block_009_reverse (acc : List SourceJson) :
    (geometryRowsBlock009Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock009 := by
  rw [geometry_Rows_block_009_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_009 :
    geometryRowsJsonBlock009.mapM decodeGeometryRow = .ok geometryRowsTypedBlock009 := by
  simp only [geometryRowsJsonBlock009, geometryRowsTypedBlock009, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_036, decode_geometry_Rows_037, decode_geometry_Rows_038, decode_geometry_Rows_039]
  rfl

noncomputable def geometryRowsTypedThroughBlock009 : List GeometryRow := geometryRowsTypedThroughBlock008 ++ geometryRowsTypedBlock009

theorem decode_geometry_Rows_through_block_009 :
    simplicesArrayAcc04000.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock009 := by
  change (geometryRowsBlock009Push simplicesArrayAcc03600).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_009_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_008, decode_geometry_Rows_block_009]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_009_composed"
  err.flush

#print axioms geometry_Rows_chunk_036_push_eq
#print axioms geometry_Rows_chunk_037_push_eq
#print axioms geometry_Rows_chunk_038_push_eq
#print axioms geometry_Rows_chunk_039_push_eq
#print axioms geometry_Rows_block_009_push_eq
#print axioms geometry_Rows_block_009_reverse
#print axioms decode_geometry_Rows_block_009
#print axioms decode_geometry_Rows_through_block_009

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
