import ImbalancedChen.P2OriginalSaving19Geometry06ScalableVerticesNode000To002
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableVertexValuesNode000To004
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableTypedFacetVertices000
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableFaceLedgerNode000To006

/-! Finite shape for the original vertices, vertex values, facets and face ledger.
All input lists come from the original parser-bound typed leaf networks.
This source-only candidate has no geometric or integral interpretation. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableShape.Arrays
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding

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
      (∀ i : Fin n, facet[i.val]! < 33)) : FacetShape 33 facet := by
  refine ⟨h.2.1, ?_⟩
  intro i
  exact h.2.2 ⟨i.val, h.1 ▸ i.isLt⟩

theorem face_shape_of_fixed_size (face : FaceRecord) (n : Nat)
    (h : face.vertices.size = n ∧ face.vertices.toList.Nodup ∧
      (∀ i : Fin n, face.vertices[i.val]! < 33) ∧
      face.pivot < 33 ∧ face.dimension ≤ 8) : FaceShape 33 8 face := by
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
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact geometryVertices_028_shape
  · exact geometryVertices_029_shape
  · exact geometryVertices_030_shape
  · exact geometryVertices_031_shape

theorem vertices_002_to_002_shape : ∀ item ∈ geometryVerticesTypedBlock002, VertexShape 8 item := by
  intro item hitem
  simp only [geometryVerticesTypedBlock002, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl
  · exact geometryVertices_032_shape

theorem vertices_000_to_001_shape : ∀ item ∈ VerticesNode000To001.typedItems, VertexShape 8 item := by
  intro item hitem
  change item ∈ geometryVerticesTypedBlock000 ++ geometryVerticesTypedBlock001 at hitem
  exact (List.mem_append.mp hitem).elim (vertices_000_to_000_shape item) (vertices_001_to_001_shape item)

theorem vertices_000_to_002_shape : ∀ item ∈ VerticesNode000To002.typedItems, VertexShape 8 item := by
  intro item hitem
  change item ∈ VerticesNode000To001.typedItems ++ geometryVerticesTypedBlock002 at hitem
  exact (List.mem_append.mp hitem).elim (vertices_000_to_001_shape item) (vertices_002_to_002_shape item)

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
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geometryVertexValues_024_shape
  · exact geometryVertexValues_025_shape
  · exact geometryVertexValues_026_shape
  · exact geometryVertexValues_027_shape
  · exact geometryVertexValues_028_shape
  · exact geometryVertexValues_029_shape
  · exact geometryVertexValues_030_shape
  · exact geometryVertexValues_031_shape

theorem vertex_values_004_to_004_shape : ∀ item ∈ geometryVertexValuesTypedBlock004, ValueShape item := by
  intro item hitem
  simp only [geometryVertexValuesTypedBlock004, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl
  · exact geometryVertexValues_032_shape

theorem vertex_values_000_to_001_shape : ∀ item ∈ VertexValuesNode000To001.typedItems, ValueShape item := by
  intro item hitem
  change item ∈ geometryVertexValuesTypedBlock000 ++ geometryVertexValuesTypedBlock001 at hitem
  exact (List.mem_append.mp hitem).elim (vertex_values_000_to_000_shape item) (vertex_values_001_to_001_shape item)

theorem vertex_values_000_to_002_shape : ∀ item ∈ VertexValuesNode000To002.typedItems, ValueShape item := by
  intro item hitem
  change item ∈ VertexValuesNode000To001.typedItems ++ geometryVertexValuesTypedBlock002 at hitem
  exact (List.mem_append.mp hitem).elim (vertex_values_000_to_001_shape item) (vertex_values_002_to_002_shape item)

theorem vertex_values_003_to_004_shape : ∀ item ∈ VertexValuesNode003To004.typedItems, ValueShape item := by
  intro item hitem
  change item ∈ geometryVertexValuesTypedBlock003 ++ geometryVertexValuesTypedBlock004 at hitem
  exact (List.mem_append.mp hitem).elim (vertex_values_003_to_003_shape item) (vertex_values_004_to_004_shape item)

theorem vertex_values_000_to_004_shape : ∀ item ∈ VertexValuesNode000To004.typedItems, ValueShape item := by
  intro item hitem
  change item ∈ VertexValuesNode000To002.typedItems ++ VertexValuesNode003To004.typedItems at hitem
  exact (List.mem_append.mp hitem).elim (vertex_values_000_to_002_shape item) (vertex_values_003_to_004_shape item)

theorem facet_vertices_000_to_000_shape : ∀ item ∈ geometryFacetVerticesTypedBlock000, FacetShape 33 item := by
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

theorem face_ledger_000_to_000_shape : ∀ item ∈ geometryFacesTypedBlock000, FaceShape 33 8 item := by
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

theorem face_ledger_001_to_001_shape : ∀ item ∈ geometryFacesTypedBlock001, FaceShape 33 8 item := by
  intro item hitem
  simp only [geometryFacesTypedBlock001, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact face_shape_of_fixed_size _ _ geometryFaces_009_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_010_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_011_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_012_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_013_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_014_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_015_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_016_shape

theorem face_ledger_002_to_002_shape : ∀ item ∈ geometryFacesTypedBlock002, FaceShape 33 8 item := by
  intro item hitem
  simp only [geometryFacesTypedBlock002, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact face_shape_of_fixed_size _ _ geometryFaces_017_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_018_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_019_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_020_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_021_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_022_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_023_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_024_shape

theorem face_ledger_003_to_003_shape : ∀ item ∈ geometryFacesTypedBlock003, FaceShape 33 8 item := by
  intro item hitem
  simp only [geometryFacesTypedBlock003, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact face_shape_of_fixed_size _ _ geometryFaces_025_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_026_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_027_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_028_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_029_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_030_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_031_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_032_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_033_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_034_shape

theorem face_ledger_004_to_004_shape : ∀ item ∈ geometryFacesTypedBlock004, FaceShape 33 8 item := by
  intro item hitem
  simp only [geometryFacesTypedBlock004, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact face_shape_of_fixed_size _ _ geometryFaces_035_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_036_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_037_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_038_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_039_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_040_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_041_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_042_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_043_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_044_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_045_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_046_shape

theorem face_ledger_005_to_005_shape : ∀ item ∈ geometryFacesTypedBlock005, FaceShape 33 8 item := by
  intro item hitem
  simp only [geometryFacesTypedBlock005, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact face_shape_of_fixed_size _ _ geometryFaces_047_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_048_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_049_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_050_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_051_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_052_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_053_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_054_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_055_shape

theorem face_ledger_006_to_006_shape : ∀ item ∈ geometryFacesTypedBlock006, FaceShape 33 8 item := by
  intro item hitem
  simp only [geometryFacesTypedBlock006, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact face_shape_of_fixed_size _ _ geometryFaces_056_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_057_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_058_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_059_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_060_shape
  · exact face_shape_of_fixed_size _ _ geometryFaces_061_shape

theorem face_ledger_000_to_001_shape : ∀ item ∈ FaceLedgerNode000To001.typedItems, FaceShape 33 8 item := by
  intro item hitem
  change item ∈ geometryFacesTypedBlock000 ++ geometryFacesTypedBlock001 at hitem
  exact (List.mem_append.mp hitem).elim (face_ledger_000_to_000_shape item) (face_ledger_001_to_001_shape item)

theorem face_ledger_002_to_003_shape : ∀ item ∈ FaceLedgerNode002To003.typedItems, FaceShape 33 8 item := by
  intro item hitem
  change item ∈ geometryFacesTypedBlock002 ++ geometryFacesTypedBlock003 at hitem
  exact (List.mem_append.mp hitem).elim (face_ledger_002_to_002_shape item) (face_ledger_003_to_003_shape item)

theorem face_ledger_000_to_003_shape : ∀ item ∈ FaceLedgerNode000To003.typedItems, FaceShape 33 8 item := by
  intro item hitem
  change item ∈ FaceLedgerNode000To001.typedItems ++ FaceLedgerNode002To003.typedItems at hitem
  exact (List.mem_append.mp hitem).elim (face_ledger_000_to_001_shape item) (face_ledger_002_to_003_shape item)

theorem face_ledger_004_to_005_shape : ∀ item ∈ FaceLedgerNode004To005.typedItems, FaceShape 33 8 item := by
  intro item hitem
  change item ∈ geometryFacesTypedBlock004 ++ geometryFacesTypedBlock005 at hitem
  exact (List.mem_append.mp hitem).elim (face_ledger_004_to_004_shape item) (face_ledger_005_to_005_shape item)

theorem face_ledger_004_to_006_shape : ∀ item ∈ FaceLedgerNode004To006.typedItems, FaceShape 33 8 item := by
  intro item hitem
  change item ∈ FaceLedgerNode004To005.typedItems ++ geometryFacesTypedBlock006 at hitem
  exact (List.mem_append.mp hitem).elim (face_ledger_004_to_005_shape item) (face_ledger_006_to_006_shape item)

theorem face_ledger_000_to_006_shape : ∀ item ∈ FaceLedgerNode000To006.typedItems, FaceShape 33 8 item := by
  intro item hitem
  change item ∈ FaceLedgerNode000To003.typedItems ++ FaceLedgerNode004To006.typedItems at hitem
  exact (List.mem_append.mp hitem).elim (face_ledger_000_to_003_shape item) (face_ledger_004_to_006_shape item)

#print axioms facet_shape_of_fixed_size
#print axioms face_shape_of_fixed_size
#print axioms vertices_000_to_000_shape
#print axioms vertices_001_to_001_shape
#print axioms vertices_002_to_002_shape
#print axioms vertices_000_to_001_shape
#print axioms vertices_000_to_002_shape
#print axioms vertex_values_000_to_000_shape
#print axioms vertex_values_001_to_001_shape
#print axioms vertex_values_002_to_002_shape
#print axioms vertex_values_003_to_003_shape
#print axioms vertex_values_004_to_004_shape
#print axioms vertex_values_000_to_001_shape
#print axioms vertex_values_000_to_002_shape
#print axioms vertex_values_003_to_004_shape
#print axioms vertex_values_000_to_004_shape
#print axioms facet_vertices_000_to_000_shape
#print axioms face_ledger_000_to_000_shape
#print axioms face_ledger_001_to_001_shape
#print axioms face_ledger_002_to_002_shape
#print axioms face_ledger_003_to_003_shape
#print axioms face_ledger_004_to_004_shape
#print axioms face_ledger_005_to_005_shape
#print axioms face_ledger_006_to_006_shape
#print axioms face_ledger_000_to_001_shape
#print axioms face_ledger_002_to_003_shape
#print axioms face_ledger_000_to_003_shape
#print axioms face_ledger_004_to_005_shape
#print axioms face_ledger_004_to_006_shape
#print axioms face_ledger_000_to_006_shape
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableShape.Arrays
