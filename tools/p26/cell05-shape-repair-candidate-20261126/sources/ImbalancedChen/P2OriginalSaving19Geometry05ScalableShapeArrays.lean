import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVerticesNode000To001
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVertexValuesNode000To003
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableTypedFacetVertices000
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableFaceLedgerNode000To004

/-! Finite shape for the original vertices, vertex values, facets and face ledger.
All input lists come from the original parser-bound typed leaf networks.
This source-only candidate has no geometric or integral interpretation. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableShape.Arrays
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding

noncomputable def VertexShape (dimension : Nat) (vertex : Array ℚ) : Prop :=
  vertex.size = dimension

noncomputable def ValueShape (value : VertexValues) : Prop := value.factors.size = 10

noncomputable def FacetShape (vertexCount : Nat) (facet : Array Nat) : Prop :=
  facet.toList.Nodup ∧ (∀ i : Fin facet.size, facet[i.val]! < vertexCount)

noncomputable def FaceShape (vertexCount dimension : Nat) (face : FaceRecord) : Prop :=
  face.vertices.toList.Nodup ∧
  (∀ i : Fin face.vertices.size, face.vertices[i.val]! < vertexCount) ∧
  face.pivot < vertexCount ∧ face.dimension ≤ dimension

theorem facet_shape_of_fixed_size (facet : Array Nat) (n : Nat)
    (h : facet.size = n ∧ facet.toList.Nodup ∧
      (∀ i : Fin n, facet[i.val]! < 28)) : FacetShape 28 facet := by
  refine ⟨h.2.1, ?_⟩
  intro i
  exact h.2.2 ⟨i.val, h.1 ▸ i.isLt⟩

theorem face_shape_of_fixed_size (face : FaceRecord) (n : Nat)
    (h : face.vertices.size = n ∧ face.vertices.toList.Nodup ∧
      (∀ i : Fin n, face.vertices[i.val]! < 28) ∧
      face.pivot < 28 ∧ face.dimension ≤ 8) : FaceShape 28 8 face := by
  refine ⟨h.2.1, ?_, h.2.2.2.1, h.2.2.2.2⟩
  intro i
  exact h.2.2.1 ⟨i.val, h.1 ▸ i.isLt⟩

theorem vertices_000_to_000_shape : ∀ item ∈ geometryVerticesTypedBlock000, VertexShape 8 item := by
  intro item hitem
  simp only [geometryVerticesTypedBlock000, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geometryVertices_000_shape
  · exact geometryVertices_001_shape
  · exact geometryVertices_002_shape
  · exact geometryVertices_003_shape
  · exact geometryVertices_004_shape
  · exact geometryVertices_005_shape
  · exact geometryVertices_006_shape
  · exact geometryVertices_007_shape
  · exact geometryVertices_008_shape
  · exact geometryVertices_009_shape
  · exact geometryVertices_010_shape
  · exact geometryVertices_011_shape
  · exact geometryVertices_012_shape
  · exact geometryVertices_013_shape
  · exact geometryVertices_014_shape
  · exact geometryVertices_015_shape

theorem vertices_001_to_001_shape : ∀ item ∈ geometryVerticesTypedBlock001, VertexShape 8 item := by
  intro item hitem
  simp only [geometryVerticesTypedBlock001, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geometryVertices_016_shape
  · exact geometryVertices_017_shape
  · exact geometryVertices_018_shape
  · exact geometryVertices_019_shape
  · exact geometryVertices_020_shape
  · exact geometryVertices_021_shape
  · exact geometryVertices_022_shape
  · exact geometryVertices_023_shape
  · exact geometryVertices_024_shape
  · exact geometryVertices_025_shape
  · exact geometryVertices_026_shape
  · exact geometryVertices_027_shape

theorem vertices_000_to_001_shape : ∀ item ∈ VerticesNode000To001.typedItems, VertexShape 8 item := by
  intro item hitem
  change item ∈ geometryVerticesTypedBlock000 ++ geometryVerticesTypedBlock001 at hitem
  exact (List.mem_append.mp hitem).elim (vertices_000_to_000_shape item) (vertices_001_to_001_shape item)

theorem vertex_values_000_to_000_shape : ∀ item ∈ geometryVertexValuesTypedBlock000, ValueShape item := by
  intro item hitem
  simp only [geometryVertexValuesTypedBlock000, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geometryVertexValues_000_shape
  · exact geometryVertexValues_001_shape
  · exact geometryVertexValues_002_shape
  · exact geometryVertexValues_003_shape
  · exact geometryVertexValues_004_shape
  · exact geometryVertexValues_005_shape
  · exact geometryVertexValues_006_shape
  · exact geometryVertexValues_007_shape

theorem vertex_values_001_to_001_shape : ∀ item ∈ geometryVertexValuesTypedBlock001, ValueShape item := by
  intro item hitem
  simp only [geometryVertexValuesTypedBlock001, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geometryVertexValues_008_shape
  · exact geometryVertexValues_009_shape
  · exact geometryVertexValues_010_shape
  · exact geometryVertexValues_011_shape
  · exact geometryVertexValues_012_shape
  · exact geometryVertexValues_013_shape
  · exact geometryVertexValues_014_shape
  · exact geometryVertexValues_015_shape

theorem vertex_values_002_to_002_shape : ∀ item ∈ geometryVertexValuesTypedBlock002, ValueShape item := by
  intro item hitem
  simp only [geometryVertexValuesTypedBlock002, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geometryVertexValues_016_shape
  · exact geometryVertexValues_017_shape
  · exact geometryVertexValues_018_shape
  · exact geometryVertexValues_019_shape
  · exact geometryVertexValues_020_shape
  · exact geometryVertexValues_021_shape
  · exact geometryVertexValues_022_shape
  · exact geometryVertexValues_023_shape

theorem vertex_values_003_to_003_shape : ∀ item ∈ geometryVertexValuesTypedBlock003, ValueShape item := by
  intro item hitem
  simp only [geometryVertexValuesTypedBlock003, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl
  · exact geometryVertexValues_024_shape
  · exact geometryVertexValues_025_shape
  · exact geometryVertexValues_026_shape
  · exact geometryVertexValues_027_shape

theorem vertex_values_000_to_001_shape : ∀ item ∈ VertexValuesNode000To001.typedItems, ValueShape item := by
  intro item hitem
  change item ∈ geometryVertexValuesTypedBlock000 ++ geometryVertexValuesTypedBlock001 at hitem
  exact (List.mem_append.mp hitem).elim (vertex_values_000_to_000_shape item) (vertex_values_001_to_001_shape item)

theorem vertex_values_002_to_003_shape : ∀ item ∈ VertexValuesNode002To003.typedItems, ValueShape item := by
  intro item hitem
  change item ∈ geometryVertexValuesTypedBlock002 ++ geometryVertexValuesTypedBlock003 at hitem
  exact (List.mem_append.mp hitem).elim (vertex_values_002_to_002_shape item) (vertex_values_003_to_003_shape item)

theorem vertex_values_000_to_003_shape : ∀ item ∈ VertexValuesNode000To003.typedItems, ValueShape item := by
  intro item hitem
  change item ∈ VertexValuesNode000To001.typedItems ++ VertexValuesNode002To003.typedItems at hitem
  exact (List.mem_append.mp hitem).elim (vertex_values_000_to_001_shape item) (vertex_values_002_to_003_shape item)

theorem facet_vertices_000_to_000_shape : ∀ item ∈ geometryFacetVerticesTypedBlock000, FacetShape 28 item := by
  intro item hitem
  simp only [geometryFacetVerticesTypedBlock000, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact facet_shape_of_fixed_size _ _ geometryFacetVertices_000_shape
  · exact facet_shape_of_fixed_size _ _ geometryFacetVertices_001_shape
  · exact facet_shape_of_fixed_size _ _ geometryFacetVertices_002_shape
  · exact facet_shape_of_fixed_size _ _ geometryFacetVertices_003_shape
  · exact facet_shape_of_fixed_size _ _ geometryFacetVertices_004_shape
  · exact facet_shape_of_fixed_size _ _ geometryFacetVertices_005_shape
  · exact facet_shape_of_fixed_size _ _ geometryFacetVertices_006_shape
  · exact facet_shape_of_fixed_size _ _ geometryFacetVertices_007_shape
  · exact facet_shape_of_fixed_size _ _ geometryFacetVertices_008_shape
  · exact facet_shape_of_fixed_size _ _ geometryFacetVertices_009_shape
  · exact facet_shape_of_fixed_size _ _ geometryFacetVertices_010_shape

theorem face_ledger_000_to_000_shape : ∀ item ∈ geometryFacesTypedBlock000, FaceShape 28 8 item := by
  intro item hitem
  simp only [geometryFacesTypedBlock000, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact face_shape_of_fixed_size _ _ geometryFaces_000_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_001_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_002_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_003_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_004_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_005_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_006_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_007_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_008_shape

theorem face_ledger_001_to_001_shape : ∀ item ∈ geometryFacesTypedBlock001, FaceShape 28 8 item := by
  intro item hitem
  simp only [geometryFacesTypedBlock001, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact face_shape_of_fixed_size _ _ geometryFaces_009_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_010_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_011_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_012_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_013_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_014_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_015_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_016_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_017_shape

theorem face_ledger_002_to_002_shape : ∀ item ∈ geometryFacesTypedBlock002, FaceShape 28 8 item := by
  intro item hitem
  simp only [geometryFacesTypedBlock002, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact face_shape_of_fixed_size _ _ geometryFaces_018_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_019_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_020_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_021_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_022_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_023_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_024_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_025_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_026_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_027_shape

theorem face_ledger_003_to_003_shape : ∀ item ∈ geometryFacesTypedBlock003, FaceShape 28 8 item := by
  intro item hitem
  simp only [geometryFacesTypedBlock003, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact face_shape_of_fixed_size _ _ geometryFaces_028_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_029_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_030_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_031_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_032_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_033_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_034_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_035_shape

theorem face_ledger_004_to_004_shape : ∀ item ∈ geometryFacesTypedBlock004, FaceShape 28 8 item := by
  intro item hitem
  simp only [geometryFacesTypedBlock004, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact face_shape_of_fixed_size _ _ geometryFaces_036_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_037_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_038_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_039_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_040_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_041_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_042_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_043_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_044_shape

theorem face_ledger_000_to_001_shape : ∀ item ∈ FaceLedgerNode000To001.typedItems, FaceShape 28 8 item := by
  intro item hitem
  change item ∈ geometryFacesTypedBlock000 ++ geometryFacesTypedBlock001 at hitem
  exact (List.mem_append.mp hitem).elim (face_ledger_000_to_000_shape item) (face_ledger_001_to_001_shape item)

theorem face_ledger_000_to_002_shape : ∀ item ∈ FaceLedgerNode000To002.typedItems, FaceShape 28 8 item := by
  intro item hitem
  change item ∈ FaceLedgerNode000To001.typedItems ++ geometryFacesTypedBlock002 at hitem
  exact (List.mem_append.mp hitem).elim (face_ledger_000_to_001_shape item) (face_ledger_002_to_002_shape item)

theorem face_ledger_003_to_004_shape : ∀ item ∈ FaceLedgerNode003To004.typedItems, FaceShape 28 8 item := by
  intro item hitem
  change item ∈ geometryFacesTypedBlock003 ++ geometryFacesTypedBlock004 at hitem
  exact (List.mem_append.mp hitem).elim (face_ledger_003_to_003_shape item) (face_ledger_004_to_004_shape item)

theorem face_ledger_000_to_004_shape : ∀ item ∈ FaceLedgerNode000To004.typedItems, FaceShape 28 8 item := by
  intro item hitem
  change item ∈ FaceLedgerNode000To002.typedItems ++ FaceLedgerNode003To004.typedItems at hitem
  exact (List.mem_append.mp hitem).elim (face_ledger_000_to_002_shape item) (face_ledger_003_to_004_shape item)

#print axioms facet_shape_of_fixed_size
#print axioms face_shape_of_fixed_size
#print axioms vertices_000_to_000_shape
#print axioms vertices_001_to_001_shape
#print axioms vertices_000_to_001_shape
#print axioms vertex_values_000_to_000_shape
#print axioms vertex_values_001_to_001_shape
#print axioms vertex_values_002_to_002_shape
#print axioms vertex_values_003_to_003_shape
#print axioms vertex_values_000_to_001_shape
#print axioms vertex_values_002_to_003_shape
#print axioms vertex_values_000_to_003_shape
#print axioms facet_vertices_000_to_000_shape
#print axioms face_ledger_000_to_000_shape
#print axioms face_ledger_001_to_001_shape
#print axioms face_ledger_002_to_002_shape
#print axioms face_ledger_003_to_003_shape
#print axioms face_ledger_004_to_004_shape
#print axioms face_ledger_000_to_001_shape
#print axioms face_ledger_000_to_002_shape
#print axioms face_ledger_003_to_004_shape
#print axioms face_ledger_000_to_004_shape
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableShape.Arrays
