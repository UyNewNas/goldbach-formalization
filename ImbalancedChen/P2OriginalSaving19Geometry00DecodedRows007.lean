import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows006
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00700
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow028
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow029
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow030
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow031

/-! Original GeometryRow block 7: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_028_push_eq (acc : List SourceJson) :
    simplicesChunk028Push00 acc = [geometryRowsJson028] ++ acc := by rfl

theorem geometry_Rows_chunk_029_push_eq (acc : List SourceJson) :
    simplicesChunk029Push00 acc = [geometryRowsJson029] ++ acc := by rfl

theorem geometry_Rows_chunk_030_push_eq (acc : List SourceJson) :
    simplicesChunk030Push00 acc = [geometryRowsJson030] ++ acc := by rfl

theorem geometry_Rows_chunk_031_push_eq (acc : List SourceJson) :
    simplicesChunk031Push00 acc = [geometryRowsJson031] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock007 : List SourceJson := [geometryRowsJson028, geometryRowsJson029, geometryRowsJson030, geometryRowsJson031]
noncomputable def geometryRowsTypedBlock007 : List GeometryRow := [geometryRowsTyped028, geometryRowsTyped029, geometryRowsTyped030, geometryRowsTyped031]
noncomputable def geometryRowsBlock007Push (acc : List SourceJson) : List SourceJson := simplicesChunk031Push00 (simplicesChunk030Push00 (simplicesChunk029Push00 (simplicesChunk028Push00 (acc))))

theorem geometry_Rows_block_007_push_eq (acc : List SourceJson) :
    geometryRowsBlock007Push acc = [geometryRowsJson031, geometryRowsJson030, geometryRowsJson029, geometryRowsJson028] ++ acc := by rfl

theorem geometry_Rows_block_007_reverse (acc : List SourceJson) :
    (geometryRowsBlock007Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock007 := by
  rw [geometry_Rows_block_007_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_007 :
    geometryRowsJsonBlock007.mapM decodeGeometryRow = .ok geometryRowsTypedBlock007 := by
  simp only [geometryRowsJsonBlock007, geometryRowsTypedBlock007, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_028, decode_geometry_Rows_029, decode_geometry_Rows_030, decode_geometry_Rows_031]
  rfl

noncomputable def geometryRowsTypedThroughBlock007 : List GeometryRow := geometryRowsTypedThroughBlock006 ++ geometryRowsTypedBlock007

theorem decode_geometry_Rows_through_block_007 :
    simplicesArrayAcc03200.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock007 := by
  change (geometryRowsBlock007Push simplicesArrayAcc02800).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_007_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_006, decode_geometry_Rows_block_007]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_007_composed"
  err.flush

#print axioms geometry_Rows_chunk_028_push_eq
#print axioms geometry_Rows_chunk_029_push_eq
#print axioms geometry_Rows_chunk_030_push_eq
#print axioms geometry_Rows_chunk_031_push_eq
#print axioms geometry_Rows_block_007_push_eq
#print axioms geometry_Rows_block_007_reverse
#print axioms decode_geometry_Rows_block_007
#print axioms decode_geometry_Rows_through_block_007

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
