import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows000
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00100
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow004
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow005
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow006
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow007

/-! Original GeometryRow block 1: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_004_push_eq (acc : List SourceJson) :
    simplicesChunk004Push00 acc = [geometryRowsJson004] ++ acc := by rfl

theorem geometry_Rows_chunk_005_push_eq (acc : List SourceJson) :
    simplicesChunk005Push00 acc = [geometryRowsJson005] ++ acc := by rfl

theorem geometry_Rows_chunk_006_push_eq (acc : List SourceJson) :
    simplicesChunk006Push00 acc = [geometryRowsJson006] ++ acc := by rfl

theorem geometry_Rows_chunk_007_push_eq (acc : List SourceJson) :
    simplicesChunk007Push00 acc = [geometryRowsJson007] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock001 : List SourceJson := [geometryRowsJson004, geometryRowsJson005, geometryRowsJson006, geometryRowsJson007]
noncomputable def geometryRowsTypedBlock001 : List GeometryRow := [geometryRowsTyped004, geometryRowsTyped005, geometryRowsTyped006, geometryRowsTyped007]
noncomputable def geometryRowsBlock001Push (acc : List SourceJson) : List SourceJson := simplicesChunk007Push00 (simplicesChunk006Push00 (simplicesChunk005Push00 (simplicesChunk004Push00 (acc))))

theorem geometry_Rows_block_001_push_eq (acc : List SourceJson) :
    geometryRowsBlock001Push acc = [geometryRowsJson007, geometryRowsJson006, geometryRowsJson005, geometryRowsJson004] ++ acc := by rfl

theorem geometry_Rows_block_001_reverse (acc : List SourceJson) :
    (geometryRowsBlock001Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock001 := by
  rw [geometry_Rows_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_001 :
    geometryRowsJsonBlock001.mapM decodeGeometryRow = .ok geometryRowsTypedBlock001 := by
  simp only [geometryRowsJsonBlock001, geometryRowsTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_004, decode_geometry_Rows_005, decode_geometry_Rows_006, decode_geometry_Rows_007]
  rfl

noncomputable def geometryRowsTypedThroughBlock001 : List GeometryRow := geometryRowsTypedThroughBlock000 ++ geometryRowsTypedBlock001

theorem decode_geometry_Rows_through_block_001 :
    simplicesArrayAcc00800.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock001 := by
  change (geometryRowsBlock001Push simplicesArrayAcc00400).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_001_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_000, decode_geometry_Rows_block_001]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_001_composed"
  err.flush

#print axioms geometry_Rows_chunk_004_push_eq
#print axioms geometry_Rows_chunk_005_push_eq
#print axioms geometry_Rows_chunk_006_push_eq
#print axioms geometry_Rows_chunk_007_push_eq
#print axioms geometry_Rows_block_001_push_eq
#print axioms geometry_Rows_block_001_reverse
#print axioms decode_geometry_Rows_block_001
#print axioms decode_geometry_Rows_through_block_001

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
