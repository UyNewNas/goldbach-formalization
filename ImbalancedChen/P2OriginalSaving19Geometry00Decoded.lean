import ImbalancedChen.P2OriginalSaving19Geometry00DecodeFields
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedVertices003
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedVertexValues006
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedFacetVertices001
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedFaces008
import ImbalancedChen.P2OriginalSaving19Geometry00DecodedRows013

/-! Original complete parsed geometry00 AST decoded into its concrete original Geometry structure.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED whole_before_concrete_geometry"
  err.flush

noncomputable def concreteGeometry00 : Geometry :=
  geometryWithDecodedArrays geometryVerticesTypedThroughBlock003.toArray geometryVertexValuesTypedThroughBlock006.toArray geometryRowsTypedThroughBlock013.toArray geometryFacetVerticesTypedThroughBlock001.toArray geometryFacesTypedThroughBlock008.toArray

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED whole_before_opaque_decoder_application"
  err.flush

theorem decode_originalGeometryJson00 :
    decodeGeometry originalGeometryJson00 = .ok concreteGeometry00 :=
  (congrArg decodeGeometry originalGeometryJson00_eq_object).trans
    (decodeGeometry_of_array_decodes verticesArrayAcc01400.reverse vertexValuesArrayAcc02800.reverse simplicesArrayAcc05600.reverse facetVerticesArrayAcc00600.reverse faceLedgerArrayAcc03300.reverse
      geometryVerticesTypedThroughBlock003.toArray geometryVertexValuesTypedThroughBlock006.toArray geometryRowsTypedThroughBlock013.toArray geometryFacetVerticesTypedThroughBlock001.toArray geometryFacesTypedThroughBlock008.toArray
      (mapM_array_of_list_ok rationalArray verticesArrayAcc01400.reverse
        geometryVerticesTypedThroughBlock003 decode_geometry_Vertices_through_block_003)
      (mapM_array_of_list_ok decodeVertexValues vertexValuesArrayAcc02800.reverse
        geometryVertexValuesTypedThroughBlock006 decode_geometry_VertexValues_through_block_006)
      (mapM_array_of_list_ok decodeGeometryRow simplicesArrayAcc05600.reverse
        geometryRowsTypedThroughBlock013 decode_geometry_Rows_through_block_013)
      (mapM_array_of_list_ok (SourceJson.Decode.read (α := Array Nat)) facetVerticesArrayAcc00600.reverse
        geometryFacetVerticesTypedThroughBlock001 decode_geometry_FacetVertices_through_block_001)
      (mapM_array_of_list_ok decodeFace faceLedgerArrayAcc03300.reverse
        geometryFacesTypedThroughBlock008 decode_geometry_Faces_through_block_008))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED whole_original_Geometry_decode_complete"
  err.flush

#print axioms decode_originalGeometryJson00

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
