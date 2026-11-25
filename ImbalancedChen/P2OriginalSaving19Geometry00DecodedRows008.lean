import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows007
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00800
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow032
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow033
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow034
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow035

/-! Original GeometryRow block 8: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_032_push_eq (acc : List SourceJson) :
    simplicesChunk032Push00 acc = [geometryRowsJson032] ++ acc := by rfl

theorem geometry_Rows_chunk_033_push_eq (acc : List SourceJson) :
    simplicesChunk033Push00 acc = [geometryRowsJson033] ++ acc := by rfl

theorem geometry_Rows_chunk_034_push_eq (acc : List SourceJson) :
    simplicesChunk034Push00 acc = [geometryRowsJson034] ++ acc := by rfl

theorem geometry_Rows_chunk_035_push_eq (acc : List SourceJson) :
    simplicesChunk035Push00 acc = [geometryRowsJson035] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock008 : List SourceJson := [geometryRowsJson032, geometryRowsJson033, geometryRowsJson034, geometryRowsJson035]
noncomputable def geometryRowsTypedBlock008 : List GeometryRow := [geometryRowsTyped032, geometryRowsTyped033, geometryRowsTyped034, geometryRowsTyped035]
noncomputable def geometryRowsBlock008Push (acc : List SourceJson) : List SourceJson := simplicesChunk035Push00 (simplicesChunk034Push00 (simplicesChunk033Push00 (simplicesChunk032Push00 (acc))))

theorem geometry_Rows_block_008_push_eq (acc : List SourceJson) :
    geometryRowsBlock008Push acc = [geometryRowsJson035, geometryRowsJson034, geometryRowsJson033, geometryRowsJson032] ++ acc := by rfl

theorem geometry_Rows_block_008_reverse (acc : List SourceJson) :
    (geometryRowsBlock008Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock008 := by
  rw [geometry_Rows_block_008_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_008 :
    geometryRowsJsonBlock008.mapM decodeGeometryRow = .ok geometryRowsTypedBlock008 := by
  simp only [geometryRowsJsonBlock008, geometryRowsTypedBlock008, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_032, decode_geometry_Rows_033, decode_geometry_Rows_034, decode_geometry_Rows_035]
  rfl

noncomputable def geometryRowsTypedThroughBlock008 : List GeometryRow := geometryRowsTypedThroughBlock007 ++ geometryRowsTypedBlock008

theorem decode_geometry_Rows_through_block_008 :
    simplicesArrayAcc03600.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock008 := by
  change (geometryRowsBlock008Push simplicesArrayAcc03200).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_008_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_007, decode_geometry_Rows_block_008]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_008_composed"
  err.flush

#print axioms geometry_Rows_chunk_032_push_eq
#print axioms geometry_Rows_chunk_033_push_eq
#print axioms geometry_Rows_chunk_034_push_eq
#print axioms geometry_Rows_chunk_035_push_eq
#print axioms geometry_Rows_block_008_push_eq
#print axioms geometry_Rows_block_008_reverse
#print axioms decode_geometry_Rows_block_008
#print axioms decode_geometry_Rows_through_block_008

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
