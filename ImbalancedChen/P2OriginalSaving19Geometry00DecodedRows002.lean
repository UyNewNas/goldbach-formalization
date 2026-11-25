import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows001
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00200
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow008
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow009
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow010
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow011

/-! Original GeometryRow block 2: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_008_push_eq (acc : List SourceJson) :
    simplicesChunk008Push00 acc = [geometryRowsJson008] ++ acc := by rfl

theorem geometry_Rows_chunk_009_push_eq (acc : List SourceJson) :
    simplicesChunk009Push00 acc = [geometryRowsJson009] ++ acc := by rfl

theorem geometry_Rows_chunk_010_push_eq (acc : List SourceJson) :
    simplicesChunk010Push00 acc = [geometryRowsJson010] ++ acc := by rfl

theorem geometry_Rows_chunk_011_push_eq (acc : List SourceJson) :
    simplicesChunk011Push00 acc = [geometryRowsJson011] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock002 : List SourceJson := [geometryRowsJson008, geometryRowsJson009, geometryRowsJson010, geometryRowsJson011]
noncomputable def geometryRowsTypedBlock002 : List GeometryRow := [geometryRowsTyped008, geometryRowsTyped009, geometryRowsTyped010, geometryRowsTyped011]
noncomputable def geometryRowsBlock002Push (acc : List SourceJson) : List SourceJson := simplicesChunk011Push00 (simplicesChunk010Push00 (simplicesChunk009Push00 (simplicesChunk008Push00 (acc))))

theorem geometry_Rows_block_002_push_eq (acc : List SourceJson) :
    geometryRowsBlock002Push acc = [geometryRowsJson011, geometryRowsJson010, geometryRowsJson009, geometryRowsJson008] ++ acc := by rfl

theorem geometry_Rows_block_002_reverse (acc : List SourceJson) :
    (geometryRowsBlock002Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock002 := by
  rw [geometry_Rows_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_002 :
    geometryRowsJsonBlock002.mapM decodeGeometryRow = .ok geometryRowsTypedBlock002 := by
  simp only [geometryRowsJsonBlock002, geometryRowsTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_008, decode_geometry_Rows_009, decode_geometry_Rows_010, decode_geometry_Rows_011]
  rfl

noncomputable def geometryRowsTypedThroughBlock002 : List GeometryRow := geometryRowsTypedThroughBlock001 ++ geometryRowsTypedBlock002

theorem decode_geometry_Rows_through_block_002 :
    simplicesArrayAcc01200.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock002 := by
  change (geometryRowsBlock002Push simplicesArrayAcc00800).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_002_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_001, decode_geometry_Rows_block_002]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_002_composed"
  err.flush

#print axioms geometry_Rows_chunk_008_push_eq
#print axioms geometry_Rows_chunk_009_push_eq
#print axioms geometry_Rows_chunk_010_push_eq
#print axioms geometry_Rows_chunk_011_push_eq
#print axioms geometry_Rows_block_002_push_eq
#print axioms geometry_Rows_block_002_reverse
#print axioms decode_geometry_Rows_block_002
#print axioms decode_geometry_Rows_through_block_002

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
