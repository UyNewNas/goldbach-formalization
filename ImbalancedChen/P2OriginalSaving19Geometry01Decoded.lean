import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodeFields
import ImbalancedChen.P2OriginalSaving19Geometry01DirectWholeParse
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedVertices002
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedVertexValues004
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows072
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFacetVertices000
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedFaces019

/-! Complete original packed cell01 parsing and actual original Geometry decoding.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding

noncomputable def concreteGeometry01 : Geometry :=
  geometryWithDecodedArrays geometryVerticesTypedThroughBlock002.toArray geometryVertexValuesTypedThroughBlock004.toArray geometryRowsTypedThroughBlock072.toArray geometryFacetVerticesTypedThroughBlock000.toArray geometryFacesTypedThroughBlock019.toArray

theorem decode_originalGeometryJson01 :
    decodeGeometry originalGeometryJson01 = .ok concreteGeometry01 :=
  (congrArg decodeGeometry originalGeometryJson01_eq_object).trans
    (decodeGeometry_of_array_decodes VerticesValue.arrayAcc003.reverse VertexValuesValue.arrayAcc005.reverse SimplicesValue.arrayAcc073.reverse FacetVerticesValue.arrayAcc001.reverse FaceLedgerValue.arrayAcc020.reverse
      geometryVerticesTypedThroughBlock002.toArray geometryVertexValuesTypedThroughBlock004.toArray geometryRowsTypedThroughBlock072.toArray geometryFacetVerticesTypedThroughBlock000.toArray geometryFacesTypedThroughBlock019.toArray
      (mapM_array_of_list_ok rationalArray VerticesValue.arrayAcc003.reverse
        geometryVerticesTypedThroughBlock002 decode_geometry_Vertices_through_block_002)
      (mapM_array_of_list_ok decodeVertexValues VertexValuesValue.arrayAcc005.reverse
        geometryVertexValuesTypedThroughBlock004 decode_geometry_VertexValues_through_block_004)
      (mapM_array_of_list_ok decodeGeometryRow SimplicesValue.arrayAcc073.reverse
        geometryRowsTypedThroughBlock072 decode_geometry_Rows_through_block_072)
      (mapM_array_of_list_ok (SourceJson.Decode.read (α := Array Nat)) FacetVerticesValue.arrayAcc001.reverse
        geometryFacetVerticesTypedThroughBlock000 decode_geometry_FacetVertices_through_block_000)
      (mapM_array_of_list_ok decodeFace FaceLedgerValue.arrayAcc020.reverse
        geometryFacesTypedThroughBlock019 decode_geometry_Faces_through_block_019))

theorem geometryPacked01_parse_decode :
    (SourceJson.parse (String.ofList geometryPacked01.toList) >>= decodeGeometry) =
      .ok concreteGeometry01 :=
  geometry_parse_decode_of_equalities (String.ofList geometryPacked01.toList)
    originalGeometryJson01 concreteGeometry01 geometryPacked01_original_parse decode_originalGeometryJson01

#print axioms decode_originalGeometryJson01
#print axioms geometryPacked01_parse_decode

end ImbalancedChen.P2OriginalSaving19Geometry01Decoding
