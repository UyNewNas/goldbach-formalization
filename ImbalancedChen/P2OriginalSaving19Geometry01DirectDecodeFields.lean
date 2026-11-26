import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectWholeValue

/-! Original metadata and abstract original decoder composition for cell01.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryObjectWithArrays (vertexJson valueJson rowJson facetJson faceJson : List SourceJson) : SourceJson :=
  .obj (Metadata05.metadataAcc.reverse ++ [
    (Active8EnumerationField.fieldKey, Active8EnumerationValue.arrayValue),
    (VerticesField.fieldKey, .arr vertexJson),
    (VertexValuesField.fieldKey, .arr valueJson),
    (AllOriginalConstraintMinimaField.fieldKey, AllOriginalConstraintMinimaValue.arrayValue),
    (FacetVerticesField.fieldKey, .arr facetJson),
    (FaceLedgerField.fieldKey, .arr faceJson),
    (SimplicesField.fieldKey, .arr rowJson),
    (PhysicalVolumeField.fieldKey, PhysicalVolumeField.fieldValue),
    (finalFieldKey, finalFieldValue)])

theorem originalGeometryJson01_eq_object :
    originalGeometryJson01 = geometryObjectWithArrays VerticesValue.arrayAcc003.reverse VertexValuesValue.arrayAcc005.reverse SimplicesValue.arrayAcc073.reverse FacetVerticesValue.arrayAcc001.reverse FaceLedgerValue.arrayAcc020.reverse := by rfl

noncomputable def geometryDecodedDimension : Nat := 8
noncomputable def geometryDecodedPhysicalJacobian : Nat := 1
noncomputable def geometryDecodedFacetOriginalIndices : Array Nat := #[7, 8, 9, 13, 14, 18, 19, 34, 39, 75, 83, 93]

theorem geometry_get_dimension (vertexJson valueJson rowJson facetJson faceJson : List SourceJson) :
    (geometryObjectWithArrays vertexJson valueJson rowJson facetJson faceJson).getObjValAs? (Nat) "dimension" = .ok geometryDecodedDimension := by
  change SourceJson.Decode.read (α := Nat) (.number (String.ofList ['8'])) = .ok geometryDecodedDimension
  decide +kernel

theorem geometry_get_physical_jacobian (vertexJson valueJson rowJson facetJson faceJson : List SourceJson) :
    (geometryObjectWithArrays vertexJson valueJson rowJson facetJson faceJson).getObjValAs? (Nat) "physical_jacobian" = .ok geometryDecodedPhysicalJacobian := by
  change SourceJson.Decode.read (α := Nat) (.number (String.ofList ['1'])) = .ok geometryDecodedPhysicalJacobian
  decide +kernel

theorem geometry_get_facet_original_indices (vertexJson valueJson rowJson facetJson faceJson : List SourceJson) :
    (geometryObjectWithArrays vertexJson valueJson rowJson facetJson faceJson).getObjValAs? (Array Nat) "facet_original_indices" = .ok geometryDecodedFacetOriginalIndices := by
  change SourceJson.Decode.read (α := Array Nat) (.arr [.number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '9']), .number (String.ofList ['7', '5']), .number (String.ofList ['8', '3']), .number (String.ofList ['9', '3'])]) = .ok geometryDecodedFacetOriginalIndices
  decide +kernel

theorem geometry_get_vertices (vertexJson valueJson rowJson facetJson faceJson : List SourceJson) :
    (geometryObjectWithArrays vertexJson valueJson rowJson facetJson faceJson).getObjVal? "vertices" = .ok (.arr vertexJson) := by rfl

theorem geometry_get_vertex_values (vertexJson valueJson rowJson facetJson faceJson : List SourceJson) :
    (geometryObjectWithArrays vertexJson valueJson rowJson facetJson faceJson).getObjVal? "vertex_values" = .ok (.arr valueJson) := by rfl

theorem geometry_get_simplices (vertexJson valueJson rowJson facetJson faceJson : List SourceJson) :
    (geometryObjectWithArrays vertexJson valueJson rowJson facetJson faceJson).getObjVal? "simplices" = .ok (.arr rowJson) := by rfl

theorem geometry_get_face_ledger (vertexJson valueJson rowJson facetJson faceJson : List SourceJson) :
    (geometryObjectWithArrays vertexJson valueJson rowJson facetJson faceJson).getObjVal? "face_ledger" = .ok (.arr faceJson) := by rfl

theorem geometry_get_facet_vertices (vertexJson valueJson rowJson facetJson faceJson : List SourceJson) :
    (geometryObjectWithArrays vertexJson valueJson rowJson facetJson faceJson).getObjValAs? (Array (Array Nat)) "facet_vertices" =
      facetJson.toArray.mapM (SourceJson.Decode.read (α := Array Nat)) := by rfl

noncomputable def geometryWithDecodedArrays
    (vertices : Array (Array ℚ)) (vertexValues : Array VertexValues)
    (rows : Array GeometryRow) (facetVertices : Array (Array Nat))
    (faces : Array FaceRecord) : Geometry := {
  dimension := geometryDecodedDimension
  physicalJacobian := geometryDecodedPhysicalJacobian
  vertices := vertices
  vertexValues := vertexValues
  rows := rows
  facetOriginalIndices := geometryDecodedFacetOriginalIndices
  facetVertices := facetVertices
  faces := faces }

theorem mapM_array_of_list_ok {α β : Type}
    (read : α → Except String β) (source : List α) (target : List β)
    (h : source.mapM read = .ok target) :
    source.toArray.mapM read = .ok target.toArray := by
  rw [List.mapM_toArray, h]
  rfl

theorem decodeGeometry_of_array_decodes
    (vertexJson valueJson rowJson facetJson faceJson : List SourceJson)
    (vertices : Array (Array ℚ)) (vertexValues : Array VertexValues)
    (rows : Array GeometryRow) (facetVertices : Array (Array Nat)) (faces : Array FaceRecord)
    (hvertices : vertexJson.toArray.mapM rationalArray = .ok vertices)
    (hvalues : valueJson.toArray.mapM decodeVertexValues = .ok vertexValues)
    (hrows : rowJson.toArray.mapM decodeGeometryRow = .ok rows)
    (hfacets : facetJson.toArray.mapM (SourceJson.Decode.read (α := Array Nat)) = .ok facetVertices)
    (hfaces : faceJson.toArray.mapM decodeFace = .ok faces) :
    decodeGeometry (geometryObjectWithArrays vertexJson valueJson rowJson facetJson faceJson) =
      .ok (geometryWithDecodedArrays vertices vertexValues rows facetVertices faces) := by
  simp only [decodeGeometry, geometry_get_dimension, geometry_get_physical_jacobian,
    geometry_get_vertices, geometry_get_vertex_values, geometry_get_simplices,
    geometry_get_facet_original_indices, geometry_get_facet_vertices, geometry_get_face_ledger,
    SourceJson.getArr?, hvertices, hvalues, hrows, hfacets, hfaces, bind, Except.bind]
  rfl

theorem geometry_parse_decode_of_equalities
    (text : String) (parsed : SourceJson) (decoded : Geometry)
    (hparse : SourceJson.parse text = .ok parsed)
    (hdecode : decodeGeometry parsed = .ok decoded) :
    (SourceJson.parse text >>= decodeGeometry) = .ok decoded := by
  rw [hparse]
  exact hdecode

#print axioms originalGeometryJson01_eq_object
#print axioms geometry_get_dimension
#print axioms geometry_get_physical_jacobian
#print axioms geometry_get_facet_original_indices
#print axioms geometry_get_vertices
#print axioms geometry_get_vertex_values
#print axioms geometry_get_simplices
#print axioms geometry_get_face_ledger
#print axioms geometry_get_facet_vertices
#print axioms mapM_array_of_list_ok
#print axioms decodeGeometry_of_array_decodes
#print axioms geometry_parse_decode_of_equalities

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
