import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows011
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01200
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow048
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow049
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow050
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRow051

/-! Original GeometryRow block 12: opaque individual row certificates in original order.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

theorem geometry_Rows_chunk_048_push_eq (acc : List SourceJson) :
    simplicesChunk048Push00 acc = [geometryRowsJson048] ++ acc := by rfl

theorem geometry_Rows_chunk_049_push_eq (acc : List SourceJson) :
    simplicesChunk049Push00 acc = [geometryRowsJson049] ++ acc := by rfl

theorem geometry_Rows_chunk_050_push_eq (acc : List SourceJson) :
    simplicesChunk050Push00 acc = [geometryRowsJson050] ++ acc := by rfl

theorem geometry_Rows_chunk_051_push_eq (acc : List SourceJson) :
    simplicesChunk051Push00 acc = [geometryRowsJson051] ++ acc := by rfl

noncomputable def geometryRowsJsonBlock012 : List SourceJson := [geometryRowsJson048, geometryRowsJson049, geometryRowsJson050, geometryRowsJson051]
noncomputable def geometryRowsTypedBlock012 : List GeometryRow := [geometryRowsTyped048, geometryRowsTyped049, geometryRowsTyped050, geometryRowsTyped051]
noncomputable def geometryRowsBlock012Push (acc : List SourceJson) : List SourceJson := simplicesChunk051Push00 (simplicesChunk050Push00 (simplicesChunk049Push00 (simplicesChunk048Push00 (acc))))

theorem geometry_Rows_block_012_push_eq (acc : List SourceJson) :
    geometryRowsBlock012Push acc = [geometryRowsJson051, geometryRowsJson050, geometryRowsJson049, geometryRowsJson048] ++ acc := by rfl

theorem geometry_Rows_block_012_reverse (acc : List SourceJson) :
    (geometryRowsBlock012Push acc).reverse = acc.reverse ++ geometryRowsJsonBlock012 := by
  rw [geometry_Rows_block_012_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_012 :
    geometryRowsJsonBlock012.mapM decodeGeometryRow = .ok geometryRowsTypedBlock012 := by
  simp only [geometryRowsJsonBlock012, geometryRowsTypedBlock012, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_048, decode_geometry_Rows_049, decode_geometry_Rows_050, decode_geometry_Rows_051]
  rfl

noncomputable def geometryRowsTypedThroughBlock012 : List GeometryRow := geometryRowsTypedThroughBlock011 ++ geometryRowsTypedBlock012

theorem decode_geometry_Rows_through_block_012 :
    simplicesArrayAcc05200.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock012 := by
  change (geometryRowsBlock012Push simplicesArrayAcc04800).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_012_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_011, decode_geometry_Rows_block_012]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Rows_block_012_composed"
  err.flush

#print axioms geometry_Rows_chunk_048_push_eq
#print axioms geometry_Rows_chunk_049_push_eq
#print axioms geometry_Rows_chunk_050_push_eq
#print axioms geometry_Rows_chunk_051_push_eq
#print axioms geometry_Rows_block_012_push_eq
#print axioms geometry_Rows_block_012_reverse
#print axioms decode_geometry_Rows_block_012
#print axioms decode_geometry_Rows_through_block_012

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
