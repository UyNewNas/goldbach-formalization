import ImbalancedChen.P2OriginalSaving19Geometry01Decoded

/-! Metadata and cardinalities of the complete original typed geometry01.
These claims concern the concrete output of the original cell01 decoder.
Finite checks are split into at most eight records per theorem. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01Shape
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Geometry01Decoding

theorem dimension : concreteGeometry01.dimension = 8 := by rfl

theorem physical_jacobian : concreteGeometry01.physicalJacobian = 1 := by rfl

theorem row_count : concreteGeometry01.rows.size = 144 := by rfl

theorem vertex_count : concreteGeometry01.vertices.size = 40 := by rfl

theorem vertex_values_size : concreteGeometry01.vertexValues.size = concreteGeometry01.vertices.size := by rfl

theorem facet_count : concreteGeometry01.facetOriginalIndices.size = 12 := by rfl

theorem facet_vertices_size : concreteGeometry01.facetVertices.size = 12 := by rfl

theorem face_count : concreteGeometry01.faces.size = 79 := by rfl

#print axioms dimension
#print axioms physical_jacobian
#print axioms row_count
#print axioms vertex_count
#print axioms vertex_values_size
#print axioms facet_count
#print axioms facet_vertices_size
#print axioms face_count
end ImbalancedChen.P2OriginalSaving19Geometry01Shape
