import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows012
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01300
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow052
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow053
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow054
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow055

/-! Original GeometryRow block 13: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_052_push_eq (acc : List SourceJson) :
    simplicesChunk052Push00 acc = [geometryRowsJson052] ++ acc := by rfl

theorem geometry_Rows_chunk_053_push_eq (acc : List SourceJson) :
    simplicesChunk053Push00 acc = [geometryRowsJson053] ++ acc := by rfl

theorem geometry_Rows_chunk_054_push_eq (acc : List SourceJson) :
    simplicesChunk054Push00 acc = [geometryRowsJson054] ++ acc := by rfl

theorem geometry_Rows_chunk_055_push_eq (acc : List SourceJson) :
    simplicesChunk055Push00 acc = [geometryRowsJson055] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock013 : List SourceJson := [geometryRowsJson052, geometryRowsJson053, geometryRowsJson054, geometryRowsJson055]
noncomputable def geometryRowsTypedBlock013 : List GeometryRow := [geometryRowsTyped052, geometryRowsTyped053, geometryRowsTyped054, geometryRowsTyped055]
noncomputable def geometryRowsBlock013Push (acc : List SourceJson) : List SourceJson := simplicesChunk055Push00 (simplicesChunk054Push00 (simplicesChunk053Push00 (simplicesChunk052Push00 (acc))))

theorem geometry_Rows_block_013_push_eq (acc : List SourceJson) :
    geometryRowsBlock013Push acc = [geometryRowsJson055, geometryRowsJson054, geometryRowsJson053, geometryRowsJson052] ++ acc := by rfl

theorem geometry_Rows_block_013_reverse (acc : List SourceJson) :
    (geometryRowsBlock013Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock013 := by
  rw [geometry_Rows_block_013_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_013 :
    geometryRowsJsonBlock013.mapM decodeGeometryRow = .ok geometryRowsTypedBlock013 := by
  simp only [geometryRowsJsonBlock013, geometryRowsTypedBlock013, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_052, decode_geometry_Rows_053, decode_geometry_Rows_054, decode_geometry_Rows_055]
  rfl

noncomputable def geometryRowsTypedThroughBlock013 : List GeometryRow := geometryRowsTypedThroughBlock012 ++ geometryRowsTypedBlock013

theorem decode_geometry_Rows_through_block_013 :
    simplicesArrayAcc05600.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock013 := by
  change (geometryRowsBlock013Push simplicesArrayAcc05200).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_013_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_012, decode_geometry_Rows_block_013]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_013_composed"
  err.flush

#print axioms geometry_Rows_chunk_052_push_eq
#print axioms geometry_Rows_chunk_053_push_eq
#print axioms geometry_Rows_chunk_054_push_eq
#print axioms geometry_Rows_chunk_055_push_eq
#print axioms geometry_Rows_block_013_push_eq
#print axioms geometry_Rows_block_013_reverse
#print axioms decode_geometry_Rows_block_013
#print axioms decode_geometry_Rows_through_block_013

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
