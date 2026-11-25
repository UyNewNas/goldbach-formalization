import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows010
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01100
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow044
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow045
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow046
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow047

/-! Original GeometryRow block 11: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_044_push_eq (acc : List SourceJson) :
    simplicesChunk044Push00 acc = [geometryRowsJson044] ++ acc := by rfl

theorem geometry_Rows_chunk_045_push_eq (acc : List SourceJson) :
    simplicesChunk045Push00 acc = [geometryRowsJson045] ++ acc := by rfl

theorem geometry_Rows_chunk_046_push_eq (acc : List SourceJson) :
    simplicesChunk046Push00 acc = [geometryRowsJson046] ++ acc := by rfl

theorem geometry_Rows_chunk_047_push_eq (acc : List SourceJson) :
    simplicesChunk047Push00 acc = [geometryRowsJson047] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock011 : List SourceJson := [geometryRowsJson044, geometryRowsJson045, geometryRowsJson046, geometryRowsJson047]
noncomputable def geometryRowsTypedBlock011 : List GeometryRow := [geometryRowsTyped044, geometryRowsTyped045, geometryRowsTyped046, geometryRowsTyped047]
noncomputable def geometryRowsBlock011Push (acc : List SourceJson) : List SourceJson := simplicesChunk047Push00 (simplicesChunk046Push00 (simplicesChunk045Push00 (simplicesChunk044Push00 (acc))))

theorem geometry_Rows_block_011_push_eq (acc : List SourceJson) :
    geometryRowsBlock011Push acc = [geometryRowsJson047, geometryRowsJson046, geometryRowsJson045, geometryRowsJson044] ++ acc := by rfl

theorem geometry_Rows_block_011_reverse (acc : List SourceJson) :
    (geometryRowsBlock011Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock011 := by
  rw [geometry_Rows_block_011_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_011 :
    geometryRowsJsonBlock011.mapM decodeGeometryRow = .ok geometryRowsTypedBlock011 := by
  simp only [geometryRowsJsonBlock011, geometryRowsTypedBlock011, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_044, decode_geometry_Rows_045, decode_geometry_Rows_046, decode_geometry_Rows_047]
  rfl

noncomputable def geometryRowsTypedThroughBlock011 : List GeometryRow := geometryRowsTypedThroughBlock010 ++ geometryRowsTypedBlock011

theorem decode_geometry_Rows_through_block_011 :
    simplicesArrayAcc04800.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock011 := by
  change (geometryRowsBlock011Push simplicesArrayAcc04400).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_011_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_010, decode_geometry_Rows_block_011]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_011_composed"
  err.flush

#print axioms geometry_Rows_chunk_044_push_eq
#print axioms geometry_Rows_chunk_045_push_eq
#print axioms geometry_Rows_chunk_046_push_eq
#print axioms geometry_Rows_chunk_047_push_eq
#print axioms geometry_Rows_block_011_push_eq
#print axioms geometry_Rows_block_011_reverse
#print axioms decode_geometry_Rows_block_011
#print axioms decode_geometry_Rows_through_block_011

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
