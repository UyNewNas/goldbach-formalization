import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows005
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00600
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow024
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow025
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow026
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow027

/-! Original GeometryRow block 6: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_024_push_eq (acc : List SourceJson) :
    simplicesChunk024Push00 acc = [geometryRowsJson024] ++ acc := by rfl

theorem geometry_Rows_chunk_025_push_eq (acc : List SourceJson) :
    simplicesChunk025Push00 acc = [geometryRowsJson025] ++ acc := by rfl

theorem geometry_Rows_chunk_026_push_eq (acc : List SourceJson) :
    simplicesChunk026Push00 acc = [geometryRowsJson026] ++ acc := by rfl

theorem geometry_Rows_chunk_027_push_eq (acc : List SourceJson) :
    simplicesChunk027Push00 acc = [geometryRowsJson027] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock006 : List SourceJson := [geometryRowsJson024, geometryRowsJson025, geometryRowsJson026, geometryRowsJson027]
noncomputable def geometryRowsTypedBlock006 : List GeometryRow := [geometryRowsTyped024, geometryRowsTyped025, geometryRowsTyped026, geometryRowsTyped027]
noncomputable def geometryRowsBlock006Push (acc : List SourceJson) : List SourceJson := simplicesChunk027Push00 (simplicesChunk026Push00 (simplicesChunk025Push00 (simplicesChunk024Push00 (acc))))

theorem geometry_Rows_block_006_push_eq (acc : List SourceJson) :
    geometryRowsBlock006Push acc = [geometryRowsJson027, geometryRowsJson026, geometryRowsJson025, geometryRowsJson024] ++ acc := by rfl

theorem geometry_Rows_block_006_reverse (acc : List SourceJson) :
    (geometryRowsBlock006Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock006 := by
  rw [geometry_Rows_block_006_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_006 :
    geometryRowsJsonBlock006.mapM decodeGeometryRow = .ok geometryRowsTypedBlock006 := by
  simp only [geometryRowsJsonBlock006, geometryRowsTypedBlock006, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_024, decode_geometry_Rows_025, decode_geometry_Rows_026, decode_geometry_Rows_027]
  rfl

noncomputable def geometryRowsTypedThroughBlock006 : List GeometryRow := geometryRowsTypedThroughBlock005 ++ geometryRowsTypedBlock006

theorem decode_geometry_Rows_through_block_006 :
    simplicesArrayAcc02800.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock006 := by
  change (geometryRowsBlock006Push simplicesArrayAcc02400).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_006_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_005, decode_geometry_Rows_block_006]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_006_composed"
  err.flush

#print axioms geometry_Rows_chunk_024_push_eq
#print axioms geometry_Rows_chunk_025_push_eq
#print axioms geometry_Rows_chunk_026_push_eq
#print axioms geometry_Rows_chunk_027_push_eq
#print axioms geometry_Rows_block_006_push_eq
#print axioms geometry_Rows_block_006_reverse
#print axioms decode_geometry_Rows_block_006
#print axioms decode_geometry_Rows_through_block_006

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
