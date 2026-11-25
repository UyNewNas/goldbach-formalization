import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows003
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00400
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow016
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow017
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow018
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow019

/-! Original GeometryRow block 4: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_016_push_eq (acc : List SourceJson) :
    simplicesChunk016Push00 acc = [geometryRowsJson016] ++ acc := by rfl

theorem geometry_Rows_chunk_017_push_eq (acc : List SourceJson) :
    simplicesChunk017Push00 acc = [geometryRowsJson017] ++ acc := by rfl

theorem geometry_Rows_chunk_018_push_eq (acc : List SourceJson) :
    simplicesChunk018Push00 acc = [geometryRowsJson018] ++ acc := by rfl

theorem geometry_Rows_chunk_019_push_eq (acc : List SourceJson) :
    simplicesChunk019Push00 acc = [geometryRowsJson019] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock004 : List SourceJson := [geometryRowsJson016, geometryRowsJson017, geometryRowsJson018, geometryRowsJson019]
noncomputable def geometryRowsTypedBlock004 : List GeometryRow := [geometryRowsTyped016, geometryRowsTyped017, geometryRowsTyped018, geometryRowsTyped019]
noncomputable def geometryRowsBlock004Push (acc : List SourceJson) : List SourceJson := simplicesChunk019Push00 (simplicesChunk018Push00 (simplicesChunk017Push00 (simplicesChunk016Push00 (acc))))

theorem geometry_Rows_block_004_push_eq (acc : List SourceJson) :
    geometryRowsBlock004Push acc = [geometryRowsJson019, geometryRowsJson018, geometryRowsJson017, geometryRowsJson016] ++ acc := by rfl

theorem geometry_Rows_block_004_reverse (acc : List SourceJson) :
    (geometryRowsBlock004Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock004 := by
  rw [geometry_Rows_block_004_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_004 :
    geometryRowsJsonBlock004.mapM decodeGeometryRow = .ok geometryRowsTypedBlock004 := by
  simp only [geometryRowsJsonBlock004, geometryRowsTypedBlock004, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_016, decode_geometry_Rows_017, decode_geometry_Rows_018, decode_geometry_Rows_019]
  rfl

noncomputable def geometryRowsTypedThroughBlock004 : List GeometryRow := geometryRowsTypedThroughBlock003 ++ geometryRowsTypedBlock004

theorem decode_geometry_Rows_through_block_004 :
    simplicesArrayAcc02000.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock004 := by
  change (geometryRowsBlock004Push simplicesArrayAcc01600).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_004_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_003, decode_geometry_Rows_block_004]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_004_composed"
  err.flush

#print axioms geometry_Rows_chunk_016_push_eq
#print axioms geometry_Rows_chunk_017_push_eq
#print axioms geometry_Rows_chunk_018_push_eq
#print axioms geometry_Rows_chunk_019_push_eq
#print axioms geometry_Rows_block_004_push_eq
#print axioms geometry_Rows_block_004_reverse
#print axioms decode_geometry_Rows_block_004
#print axioms decode_geometry_Rows_through_block_004

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
