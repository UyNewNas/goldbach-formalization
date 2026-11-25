import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows004
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00500
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow020
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow021
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow022
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow023

/-! Original GeometryRow block 5: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_020_push_eq (acc : List SourceJson) :
    simplicesChunk020Push00 acc = [geometryRowsJson020] ++ acc := by rfl

theorem geometry_Rows_chunk_021_push_eq (acc : List SourceJson) :
    simplicesChunk021Push00 acc = [geometryRowsJson021] ++ acc := by rfl

theorem geometry_Rows_chunk_022_push_eq (acc : List SourceJson) :
    simplicesChunk022Push00 acc = [geometryRowsJson022] ++ acc := by rfl

theorem geometry_Rows_chunk_023_push_eq (acc : List SourceJson) :
    simplicesChunk023Push00 acc = [geometryRowsJson023] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock005 : List SourceJson := [geometryRowsJson020, geometryRowsJson021, geometryRowsJson022, geometryRowsJson023]
noncomputable def geometryRowsTypedBlock005 : List GeometryRow := [geometryRowsTyped020, geometryRowsTyped021, geometryRowsTyped022, geometryRowsTyped023]
noncomputable def geometryRowsBlock005Push (acc : List SourceJson) : List SourceJson := simplicesChunk023Push00 (simplicesChunk022Push00 (simplicesChunk021Push00 (simplicesChunk020Push00 (acc))))

theorem geometry_Rows_block_005_push_eq (acc : List SourceJson) :
    geometryRowsBlock005Push acc = [geometryRowsJson023, geometryRowsJson022, geometryRowsJson021, geometryRowsJson020] ++ acc := by rfl

theorem geometry_Rows_block_005_reverse (acc : List SourceJson) :
    (geometryRowsBlock005Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock005 := by
  rw [geometry_Rows_block_005_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_005 :
    geometryRowsJsonBlock005.mapM decodeGeometryRow = .ok geometryRowsTypedBlock005 := by
  simp only [geometryRowsJsonBlock005, geometryRowsTypedBlock005, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_020, decode_geometry_Rows_021, decode_geometry_Rows_022, decode_geometry_Rows_023]
  rfl

noncomputable def geometryRowsTypedThroughBlock005 : List GeometryRow := geometryRowsTypedThroughBlock004 ++ geometryRowsTypedBlock005

theorem decode_geometry_Rows_through_block_005 :
    simplicesArrayAcc02400.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock005 := by
  change (geometryRowsBlock005Push simplicesArrayAcc02000).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_005_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_004, decode_geometry_Rows_block_005]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_005_composed"
  err.flush

#print axioms geometry_Rows_chunk_020_push_eq
#print axioms geometry_Rows_chunk_021_push_eq
#print axioms geometry_Rows_chunk_022_push_eq
#print axioms geometry_Rows_chunk_023_push_eq
#print axioms geometry_Rows_block_005_push_eq
#print axioms geometry_Rows_block_005_reverse
#print axioms decode_geometry_Rows_block_005
#print axioms decode_geometry_Rows_through_block_005

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
