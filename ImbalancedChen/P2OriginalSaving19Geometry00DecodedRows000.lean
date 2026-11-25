import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00000
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow000
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow001
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow002
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow003

/-! Original GeometryRow block 0: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_000_push_eq (acc : List SourceJson) :
    simplicesChunk000Push00 acc = [geometryRowsJson000] ++ acc := by rfl

theorem geometry_Rows_chunk_001_push_eq (acc : List SourceJson) :
    simplicesChunk001Push00 acc = [geometryRowsJson001] ++ acc := by rfl

theorem geometry_Rows_chunk_002_push_eq (acc : List SourceJson) :
    simplicesChunk002Push00 acc = [geometryRowsJson002] ++ acc := by rfl

theorem geometry_Rows_chunk_003_push_eq (acc : List SourceJson) :
    simplicesChunk003Push00 acc = [geometryRowsJson003] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock000 : List SourceJson := [geometryRowsJson000, geometryRowsJson001, geometryRowsJson002, geometryRowsJson003]
noncomputable def geometryRowsTypedBlock000 : List GeometryRow := [geometryRowsTyped000, geometryRowsTyped001, geometryRowsTyped002, geometryRowsTyped003]
noncomputable def geometryRowsBlock000Push (acc : List SourceJson) : List SourceJson := simplicesChunk003Push00 (simplicesChunk002Push00 (simplicesChunk001Push00 (simplicesChunk000Push00 (acc))))

theorem geometry_Rows_block_000_push_eq (acc : List SourceJson) :
    geometryRowsBlock000Push acc = [geometryRowsJson003, geometryRowsJson002, geometryRowsJson001, geometryRowsJson000] ++ acc := by rfl

theorem geometry_Rows_block_000_reverse (acc : List SourceJson) :
    (geometryRowsBlock000Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock000 := by
  rw [geometry_Rows_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_000 :
    geometryRowsJsonBlock000.mapM decodeGeometryRow = .ok geometryRowsTypedBlock000 := by
  simp only [geometryRowsJsonBlock000, geometryRowsTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_000, decode_geometry_Rows_001, decode_geometry_Rows_002, decode_geometry_Rows_003]
  rfl

noncomputable def geometryRowsTypedThroughBlock000 : List GeometryRow := geometryRowsTypedBlock000

theorem decode_geometry_Rows_through_block_000 :
    simplicesArrayAcc00400.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock000 := by
  change (geometryRowsBlock000Push simplicesArrayAcc00000).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_000_reverse]
  exact decode_geometry_Rows_block_000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_000_composed"
  err.flush

#print axioms geometry_Rows_chunk_000_push_eq
#print axioms geometry_Rows_chunk_001_push_eq
#print axioms geometry_Rows_chunk_002_push_eq
#print axioms geometry_Rows_chunk_003_push_eq
#print axioms geometry_Rows_block_000_push_eq
#print axioms geometry_Rows_block_000_reverse
#print axioms decode_geometry_Rows_block_000
#print axioms decode_geometry_Rows_through_block_000

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
