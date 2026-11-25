import ImbalancedChen.P2OriginalSaving19Geometry00Shape

/-! Bounded access to the actual decoded cell00 rows and vertices. These
equalities eliminate every fallback in the original three-level rawVertex
lookup, using the already certified concrete shape. No geometric or floor
inequality is asserted. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00BoundedAccess
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding
open ImbalancedChen.P2OriginalSaving19Geometry00Shape

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_BOUNDED before_rows"
  err.flush

theorem row_bound (r : Fin 56) : r.val < concreteGeometry00.rows.size := by
  rw [row_count]
  exact r.isLt

noncomputable def boundedRow (r : Fin 56) : GeometryRow :=
  concreteGeometry00.rows[r.val]'(row_bound r)

theorem row_lookup_no_fallback (r : Fin 56) :
    concreteGeometry00.rows[r.val]! = boundedRow r :=
  getElem!_pos concreteGeometry00.rows r.val (row_bound r)

theorem row_properties (r : Fin 56) :
    (boundedRow r).simplexId = r.val ∧
    (boundedRow r).vertexIds.size = 9 ∧ (boundedRow r).vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, (boundedRow r).vertexIds[i.val]! < concreteGeometry00.vertices.size) ∧
    (boundedRow r).factorMaxima.size = 10 ∧ (boundedRow r).gapWeightedMeans.size = 10 := by
  rw [← row_lookup_no_fallback]
  exact all_rows r

theorem vertex_lookup_no_fallback (v : Fin concreteGeometry00.vertices.size) :
    concreteGeometry00.vertices[v.val]! = concreteGeometry00.vertices[v] :=
  getElem!_pos concreteGeometry00.vertices v.val v.isLt

theorem vertex_value_bound (v : Fin concreteGeometry00.vertices.size) :
    v.val < concreteGeometry00.vertexValues.size := by
  rw [vertex_values_size]
  exact v.isLt

theorem vertex_value_lookup_no_fallback (v : Fin concreteGeometry00.vertices.size) :
    concreteGeometry00.vertexValues[v.val]! =
      concreteGeometry00.vertexValues[v.val]'(vertex_value_bound v) :=
  getElem!_pos concreteGeometry00.vertexValues v.val (vertex_value_bound v)

theorem vertex_factor_size_bounded (v : Fin concreteGeometry00.vertices.size) :
    (concreteGeometry00.vertexValues[v.val]'(vertex_value_bound v)).factors.size = 10 := by
  rw [← vertex_value_lookup_no_fallback]
  exact (all_vertices v).2

theorem coordinate_bound (v : Fin concreteGeometry00.vertices.size) (j : Fin 8) :
    j.val < (concreteGeometry00.vertices[v]).size := by
  rw [(all_vertices v).1]
  exact j.isLt

theorem coordinate_lookup_no_fallback (v : Fin concreteGeometry00.vertices.size) (j : Fin 8) :
    (concreteGeometry00.vertices[v.val]!)[j.val]! =
      (concreteGeometry00.vertices[v])[j.val]'(coordinate_bound v j) := by
  rw [vertex_lookup_no_fallback]
  exact getElem!_pos (concreteGeometry00.vertices[v]) j.val (coordinate_bound v j)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_BOUNDED before_original_nine_vertex_ids"
  err.flush

theorem vertex_id_bound (r : Fin 56) (i : Fin 9) :
    i.val < (boundedRow r).vertexIds.size := by
  rw [(row_properties r).2.1]
  exact i.isLt

theorem vertex_id_lookup_no_fallback (r : Fin 56) (i : Fin 9) :
    (concreteGeometry00.rows[r.val]!).vertexIds[i.val]! =
      (boundedRow r).vertexIds[i.val]'(vertex_id_bound r i) := by
  rw [row_lookup_no_fallback]
  exact getElem!_pos (boundedRow r).vertexIds i.val (vertex_id_bound r i)

theorem vertex_id_range (r : Fin 56) (i : Fin 9) :
    (boundedRow r).vertexIds[i.val]'(vertex_id_bound r i) < concreteGeometry00.vertices.size := by
  have h := (all_rows r).2.2.2.1 i
  rw [vertex_id_lookup_no_fallback] at h
  exact h

noncomputable def vertexIndex (r : Fin 56) (i : Fin 9) : Fin concreteGeometry00.vertices.size :=
  ⟨(boundedRow r).vertexIds[i.val]'(vertex_id_bound r i), vertex_id_range r i⟩

theorem vertexIndex_value (r : Fin 56) (i : Fin 9) :
    (vertexIndex r i).val = (concreteGeometry00.rows[r.val]!).vertexIds[i.val]! :=
  (vertex_id_lookup_no_fallback r i).symm

noncomputable def boundedRowVertex (r : Fin 56) (i : Fin 9) (j : Fin 8) : ℚ :=
  (concreteGeometry00.vertices[vertexIndex r i])[j.val]'(coordinate_bound (vertexIndex r i) j)

theorem raw_vertex_no_fallback (r : Fin 56) (i : Fin 9) (j : Fin 8) :
    ((concreteGeometry00.vertices[(concreteGeometry00.rows[r.val]!).vertexIds[i.val]!]!)[j.val]!) =
      boundedRowVertex r i j := by
  rw [← vertexIndex_value r i]
  exact coordinate_lookup_no_fallback (vertexIndex r i) j

theorem factor_maximum_bound (r : Fin 56) (f : Fin 10) :
    f.val < (boundedRow r).factorMaxima.size := by
  rw [(row_properties r).2.2.2.2.1]
  exact f.isLt

theorem factor_maximum_lookup_no_fallback (r : Fin 56) (f : Fin 10) :
    (concreteGeometry00.rows[r.val]!).factorMaxima[f.val]! =
      (boundedRow r).factorMaxima[f.val]'(factor_maximum_bound r f) := by
  rw [row_lookup_no_fallback]
  exact getElem!_pos (boundedRow r).factorMaxima f.val (factor_maximum_bound r f)

theorem weighted_mean_bound (r : Fin 56) (f : Fin 10) :
    f.val < (boundedRow r).gapWeightedMeans.size := by
  rw [(row_properties r).2.2.2.2.2]
  exact f.isLt

theorem weighted_mean_lookup_no_fallback (r : Fin 56) (f : Fin 10) :
    (concreteGeometry00.rows[r.val]!).gapWeightedMeans[f.val]! =
      (boundedRow r).gapWeightedMeans[f.val]'(weighted_mean_bound r f) := by
  rw [row_lookup_no_fallback]
  exact getElem!_pos (boundedRow r).gapWeightedMeans f.val (weighted_mean_bound r f)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_BOUNDED all_original_lookup_levels_complete"
  err.flush

#print axioms row_bound
#print axioms row_lookup_no_fallback
#print axioms row_properties
#print axioms vertex_lookup_no_fallback
#print axioms vertex_value_bound
#print axioms vertex_value_lookup_no_fallback
#print axioms vertex_factor_size_bounded
#print axioms coordinate_bound
#print axioms coordinate_lookup_no_fallback
#print axioms vertex_id_bound
#print axioms vertex_id_lookup_no_fallback
#print axioms vertex_id_range
#print axioms vertexIndex_value
#print axioms raw_vertex_no_fallback
#print axioms factor_maximum_bound
#print axioms factor_maximum_lookup_no_fallback
#print axioms weighted_mean_bound
#print axioms weighted_mean_lookup_no_fallback
end ImbalancedChen.P2OriginalSaving19Geometry00BoundedAccess
