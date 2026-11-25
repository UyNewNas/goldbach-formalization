import ImbalancedChen.P2OriginalSaving19Geometry00Decoded
import ImbalancedChen.P2OriginalSaving19GeometryPackedParseTransport00

/-! Production v4 geometryPacked00 parsed and decoded by the original reader and actual original decoder.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

open ImbalancedChen.P2OriginalSaving19GeometryPackedTransport

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED packed_before_opaque_bind_glue"
  err.flush

theorem geometryPacked00_parse_decode :
    (SourceJson.parse (String.ofList geometryPacked00.toList) >>= decodeGeometry) =
      .ok concreteGeometry00 :=
  geometry_parse_decode_of_equalities (String.ofList geometryPacked00.toList)
    originalGeometryJson00 concreteGeometry00 geometryPacked00_original_parse decode_originalGeometryJson00

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED packed_original_geometry_parse_decode_complete"
  err.flush

#print axioms geometryPacked00_parse_decode

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
