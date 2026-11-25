import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows002
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00300
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow012
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow013
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow014
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow015

/-! Original GeometryRow block 3: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_012_push_eq (acc : List SourceJson) :
    simplicesChunk012Push00 acc = [geometryRowsJson012] ++ acc := by rfl

theorem geometry_Rows_chunk_013_push_eq (acc : List SourceJson) :
    simplicesChunk013Push00 acc = [geometryRowsJson013] ++ acc := by rfl

theorem geometry_Rows_chunk_014_push_eq (acc : List SourceJson) :
    simplicesChunk014Push00 acc = [geometryRowsJson014] ++ acc := by rfl

theorem geometry_Rows_chunk_015_push_eq (acc : List SourceJson) :
    simplicesChunk015Push00 acc = [geometryRowsJson015] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock003 : List SourceJson := [geometryRowsJson012, geometryRowsJson013, geometryRowsJson014, geometryRowsJson015]
noncomputable def geometryRowsTypedBlock003 : List GeometryRow := [geometryRowsTyped012, geometryRowsTyped013, geometryRowsTyped014, geometryRowsTyped015]
noncomputable def geometryRowsBlock003Push (acc : List SourceJson) : List SourceJson := simplicesChunk015Push00 (simplicesChunk014Push00 (simplicesChunk013Push00 (simplicesChunk012Push00 (acc))))

theorem geometry_Rows_block_003_push_eq (acc : List SourceJson) :
    geometryRowsBlock003Push acc = [geometryRowsJson015, geometryRowsJson014, geometryRowsJson013, geometryRowsJson012] ++ acc := by rfl

theorem geometry_Rows_block_003_reverse (acc : List SourceJson) :
    (geometryRowsBlock003Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock003 := by
  rw [geometry_Rows_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_003 :
    geometryRowsJsonBlock003.mapM decodeGeometryRow = .ok geometryRowsTypedBlock003 := by
  simp only [geometryRowsJsonBlock003, geometryRowsTypedBlock003, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_012, decode_geometry_Rows_013, decode_geometry_Rows_014, decode_geometry_Rows_015]
  rfl

noncomputable def geometryRowsTypedThroughBlock003 : List GeometryRow := geometryRowsTypedThroughBlock002 ++ geometryRowsTypedBlock003

theorem decode_geometry_Rows_through_block_003 :
    simplicesArrayAcc01600.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock003 := by
  change (geometryRowsBlock003Push simplicesArrayAcc01200).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_003_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_002, decode_geometry_Rows_block_003]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_003_composed"
  err.flush

#print axioms geometry_Rows_chunk_012_push_eq
#print axioms geometry_Rows_chunk_013_push_eq
#print axioms geometry_Rows_chunk_014_push_eq
#print axioms geometry_Rows_chunk_015_push_eq
#print axioms geometry_Rows_block_003_push_eq
#print axioms geometry_Rows_block_003_reverse
#print axioms decode_geometry_Rows_block_003
#print axioms decode_geometry_Rows_through_block_003

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
