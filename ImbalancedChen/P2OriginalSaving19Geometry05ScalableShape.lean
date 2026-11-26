import ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoded
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableShapeRows
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableShapeArrays

/-! Complete finite shape of the actual original cell05 decoder output.
All input lists come from the original parser-bound typed leaf networks.
This source-only candidate has no geometric or integral interpretation. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableShape
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding

open ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding.Complete
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableShape.Rows
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableShape.Arrays

theorem property_of_list_toArray {α : Type} [Inhabited α]
    (items : List α) (property : α → Prop)
    (h : ∀ item ∈ items, property item) (index : Nat)
    (hi : index < items.toArray.size) : property (items.toArray[index]!) := by
  rw [getElem!_pos items.toArray index hi]
  apply h
  simpa using (Array.getElem_mem_toList hi)

theorem dimension : concreteGeometry05.dimension = 8 := by rfl
theorem physical_jacobian : concreteGeometry05.physicalJacobian = 1 := by rfl
theorem row_count : concreteGeometry05.rows.size = 56 := by rfl
theorem vertex_count : concreteGeometry05.vertices.size = 28 := by rfl
theorem vertex_values_count : concreteGeometry05.vertexValues.size = 28 := by rfl
theorem vertex_values_size : concreteGeometry05.vertexValues.size = concreteGeometry05.vertices.size := by rfl
theorem facet_count : concreteGeometry05.facetOriginalIndices.size = 11 := by rfl
theorem facet_vertices_count : concreteGeometry05.facetVertices.size = 11 := by rfl
theorem face_count : concreteGeometry05.faces.size = 45 := by rfl

theorem facet_original_indices_nodup : concreteGeometry05.facetOriginalIndices.toList.Nodup := by
  decide +kernel

theorem facet_original_indices_bound : ∀ i : Fin 11,
    concreteGeometry05.facetOriginalIndices[i.val]! < 97 := by
  decide +kernel

theorem all_rows : ∀ r : Fin 56,
    let row := concreteGeometry05.rows[r.val]!
    row.simplexId = r.val ∧
    row.vertexIds.size = 9 ∧ row.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, row.vertexIds[i.val]! < concreteGeometry05.vertices.size) ∧
    row.factorMaxima.size = 10 ∧ row.gapWeightedMeans.size = 10 := by
  intro r
  change (Node000To006.typedRows.toArray[r.val]!).simplexId = r.val ∧
    RowShape 28 (Node000To006.typedRows.toArray[r.val]!)
  exact ⟨all_row_identifiers r,
    property_of_list_toArray Node000To006.typedRows (RowShape 28)
      rows_000_to_006_shape r.val (by change r.val < 56; exact r.isLt)⟩

theorem all_vertices : ∀ v : Fin 28,
    (concreteGeometry05.vertices[v.val]!).size = concreteGeometry05.dimension ∧
    (concreteGeometry05.vertexValues[v.val]!).factors.size = 10 := by
  intro v
  change VertexShape 8 (VerticesNode000To001.typedItems.toArray[v.val]!) ∧
    ValueShape (VertexValuesNode000To003.typedItems.toArray[v.val]!)
  exact ⟨property_of_list_toArray VerticesNode000To001.typedItems (VertexShape 8)
      vertices_000_to_001_shape v.val (by change v.val < 28; exact v.isLt),
    property_of_list_toArray VertexValuesNode000To003.typedItems ValueShape
      vertex_values_000_to_003_shape v.val (by change v.val < 28; exact v.isLt)⟩

theorem all_facets : ∀ f : Fin 11,
    let facet := concreteGeometry05.facetVertices[f.val]!
    facet.toList.Nodup ∧
    (∀ i : Fin facet.size, facet[i.val]! < concreteGeometry05.vertices.size) := by
  intro f
  change FacetShape 28 (geometryFacetVerticesTypedBlock000.toArray[f.val]!)
  exact property_of_list_toArray geometryFacetVerticesTypedBlock000 (FacetShape 28)
    facet_vertices_000_to_000_shape f.val (by change f.val < 11; exact f.isLt)

theorem all_faces : ∀ f : Fin 45,
    let face := concreteGeometry05.faces[f.val]!
    face.vertices.toList.Nodup ∧
    (∀ i : Fin face.vertices.size, face.vertices[i.val]! < concreteGeometry05.vertices.size) ∧
    face.pivot < concreteGeometry05.vertices.size ∧ face.dimension ≤ concreteGeometry05.dimension := by
  intro f
  change FaceShape 28 8 (FaceLedgerNode000To004.typedItems.toArray[f.val]!)
  exact property_of_list_toArray FaceLedgerNode000To004.typedItems (FaceShape 28 8)
    face_ledger_000_to_004_shape f.val (by change f.val < 45; exact f.isLt)

structure GeometryShape (geometry : Geometry) : Prop where
  dimension : geometry.dimension = 8
  physicalJacobian : geometry.physicalJacobian = 1
  rowCount : geometry.rows.size = 56
  vertexCount : geometry.vertices.size = 28
  vertexValuesCount : geometry.vertexValues.size = 28
  facetCount : geometry.facetOriginalIndices.size = 11
  facetVerticesCount : geometry.facetVertices.size = 11
  faceCount : geometry.faces.size = 45
  facetIndicesNodup : geometry.facetOriginalIndices.toList.Nodup
  facetIndicesBound : ∀ i : Fin geometry.facetOriginalIndices.size,
    geometry.facetOriginalIndices[i.val]! < 97
  rows : ∀ r : Fin geometry.rows.size,
    let row := geometry.rows[r.val]!
    row.simplexId = r.val ∧ RowShape geometry.vertices.size row
  vertices : ∀ v : Fin geometry.vertices.size,
    (geometry.vertices[v.val]!).size = geometry.dimension ∧
    (geometry.vertexValues[v.val]!).factors.size = 10
  facets : ∀ f : Fin geometry.facetVertices.size,
    FacetShape geometry.vertices.size (geometry.facetVertices[f.val]!)
  faces : ∀ f : Fin geometry.faces.size,
    FaceShape geometry.vertices.size geometry.dimension (geometry.faces[f.val]!)

theorem concreteGeometry05_shape : GeometryShape concreteGeometry05 where
  dimension := dimension
  physicalJacobian := physical_jacobian
  rowCount := row_count
  vertexCount := vertex_count
  vertexValuesCount := vertex_values_count
  facetCount := facet_count
  facetVerticesCount := facet_vertices_count
  faceCount := face_count
  facetIndicesNodup := facet_original_indices_nodup
  facetIndicesBound := by simpa only [facet_count] using facet_original_indices_bound
  rows := by simpa only [row_count, RowShape] using all_rows
  vertices := by simpa only [vertex_count] using all_vertices
  facets := by simpa only [facet_vertices_count, FacetShape] using all_facets
  faces := by simpa only [face_count, FaceShape] using all_faces

theorem geometryPacked05_parse_decode_shape :
    (SourceJson.parse (String.ofList geometryPacked05.toList) >>= decodeGeometry) =
      .ok concreteGeometry05 ∧ GeometryShape concreteGeometry05 :=
  ⟨geometryPacked05_parse_decode, concreteGeometry05_shape⟩

#print axioms property_of_list_toArray
#print axioms dimension
#print axioms physical_jacobian
#print axioms row_count
#print axioms vertex_count
#print axioms vertex_values_count
#print axioms vertex_values_size
#print axioms facet_count
#print axioms facet_vertices_count
#print axioms face_count
#print axioms facet_original_indices_nodup
#print axioms facet_original_indices_bound
#print axioms all_rows
#print axioms all_vertices
#print axioms all_facets
#print axioms all_faces
#print axioms concreteGeometry05_shape
#print axioms geometryPacked05_parse_decode_shape
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableShape
