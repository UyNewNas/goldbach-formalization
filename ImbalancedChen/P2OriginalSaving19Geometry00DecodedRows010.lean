import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows009
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01000
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow040
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow041
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow042
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow043

/-! Original GeometryRow block 10: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_040_push_eq (acc : List SourceJson) :
    simplicesChunk040Push00 acc = [geometryRowsJson040] ++ acc := by rfl

theorem geometry_Rows_chunk_041_push_eq (acc : List SourceJson) :
    simplicesChunk041Push00 acc = [geometryRowsJson041] ++ acc := by rfl

theorem geometry_Rows_chunk_042_push_eq (acc : List SourceJson) :
    simplicesChunk042Push00 acc = [geometryRowsJson042] ++ acc := by rfl

theorem geometry_Rows_chunk_043_push_eq (acc : List SourceJson) :
    simplicesChunk043Push00 acc = [geometryRowsJson043] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock010 : List SourceJson := [geometryRowsJson040, geometryRowsJson041, geometryRowsJson042, geometryRowsJson043]
noncomputable def geometryRowsTypedBlock010 : List GeometryRow := [geometryRowsTyped040, geometryRowsTyped041, geometryRowsTyped042, geometryRowsTyped043]
noncomputable def geometryRowsBlock010Push (acc : List SourceJson) : List SourceJson := simplicesChunk043Push00 (simplicesChunk042Push00 (simplicesChunk041Push00 (simplicesChunk040Push00 (acc))))

theorem geometry_Rows_block_010_push_eq (acc : List SourceJson) :
    geometryRowsBlock010Push acc = [geometryRowsJson043, geometryRowsJson042, geometryRowsJson041, geometryRowsJson040] ++ acc := by rfl

theorem geometry_Rows_block_010_reverse (acc : List SourceJson) :
    (geometryRowsBlock010Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock010 := by
  rw [geometry_Rows_block_010_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_010 :
    geometryRowsJsonBlock010.mapM decodeGeometryRow = .ok geometryRowsTypedBlock010 := by
  simp only [geometryRowsJsonBlock010, geometryRowsTypedBlock010, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_040, decode_geometry_Rows_041, decode_geometry_Rows_042, decode_geometry_Rows_043]
  rfl

noncomputable def geometryRowsTypedThroughBlock010 : List GeometryRow := geometryRowsTypedThroughBlock009 ++ geometryRowsTypedBlock010

theorem decode_geometry_Rows_through_block_010 :
    simplicesArrayAcc04400.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock010 := by
  change (geometryRowsBlock010Push simplicesArrayAcc04000).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_010_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_009, decode_geometry_Rows_block_010]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_010_composed"
  err.flush

#print axioms geometry_Rows_chunk_040_push_eq
#print axioms geometry_Rows_chunk_041_push_eq
#print axioms geometry_Rows_chunk_042_push_eq
#print axioms geometry_Rows_chunk_043_push_eq
#print axioms geometry_Rows_block_010_push_eq
#print axioms geometry_Rows_block_010_reverse
#print axioms decode_geometry_Rows_block_010
#print axioms decode_geometry_Rows_through_block_010

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
