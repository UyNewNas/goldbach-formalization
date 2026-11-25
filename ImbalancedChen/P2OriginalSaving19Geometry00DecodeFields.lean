import ImbalancedChen.P2OriginalSaving19ArchiveSchema
import ImbalancedChen.P2OriginalSaving19WholeValue00

/-! Original geometry metadata and abstract field-list decoder composition. All original schema fields are retained.
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
  err.putStrLn "P26_GEOMETRY00_TYPED fields_before_original_object"
  err.flush

noncomputable def geometryObjectWithArrays (vertexJson valueJson rowJson facetJson faceJson : List SourceJson) : SourceJson := .obj [
  (dimensionKey00, dimensionValue00),
  (physicalKey00, physicalValue00),
  (facetIndicesKey00, facetIndicesValue00),
  (positiveBalanceKey00, positiveBalanceValue00),
  (normalRankKey00, normalRankValue00),
  (active8FieldKey00, active8ArrayValue00),
  (verticesFieldKey00, .arr vertexJson),
  (vertexValuesFieldKey00, .arr valueJson),
  (constraintMinimaFieldKey00, constraintMinimaArrayValue00),
  (facetVerticesFieldKey00, .arr facetJson),
  (faceLedgerFieldKey00, .arr faceJson),
  (simplicesFieldKey00, .arr rowJson),
  (physicalVolumeKey00, physicalVolumeValue00),
  (integralGapKey00, integralGapValue00)]

theorem originalGeometryJson00_eq_object :
    originalGeometryJson00 = geometryObjectWithArrays verticesArrayAcc01400.reverse vertexValuesArrayAcc02800.reverse simplicesArrayAcc05600.reverse facetVerticesArrayAcc00600.reverse faceLedgerArrayAcc03300.reverse := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED fields_original_object_bound"
  err.flush

noncomputable def geometryDecodedDimension : Nat := 8
noncomputable def geometryDecodedPhysicalJacobian : Nat := 1
noncomputable def geometryDecodedFacetOriginalIndices : Array Nat := #[7, 8, 9, 14, 18, 19, 34, 39, 61, 75, 82]

theorem geometry_get_dimension (vertexJson valueJson rowJson facetJson faceJson : List SourceJson) :
    (geometryObjectWithArrays vertexJson valueJson rowJson facetJson faceJson).getObjValAs? (Nat) "dimension" = .ok geometryDecodedDimension := by
  change SourceJson.Decode.read (α := Nat) dimensionValue00 = .ok geometryDecodedDimension
  decide +kernel

theorem geometry_get_physical_jacobian (vertexJson valueJson rowJson facetJson faceJson : List SourceJson) :
    (geometryObjectWithArrays vertexJson valueJson rowJson facetJson faceJson).getObjValAs? (Nat) "physical_jacobian" = .ok geometryDecodedPhysicalJacobian := by
  change SourceJson.Decode.read (α := Nat) physicalValue00 = .ok geometryDecodedPhysicalJacobian
  decide +kernel

theorem geometry_get_facet_original_indices (vertexJson valueJson rowJson facetJson faceJson : List SourceJson) :
    (geometryObjectWithArrays vertexJson valueJson rowJson facetJson faceJson).getObjValAs? (Array Nat) "facet_original_indices" = .ok geometryDecodedFacetOriginalIndices := by
  change SourceJson.Decode.read (α := Array Nat) facetIndicesValue00 = .ok geometryDecodedFacetOriginalIndices
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

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED fields_all_original_getters_complete"
  err.flush

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

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED fields_abstract_decoder_glue_complete"
  err.flush

#print axioms originalGeometryJson00_eq_object
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

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
