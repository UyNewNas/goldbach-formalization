import ImbalancedChen.P2OriginalSaving19Geometry00BoundedAccess
import ImbalancedChen.P2OriginalSaving19Moment00Shape

/-! Exact original CellShape and RowShape clauses specialized to the certified
concrete cell00 values, expected 56 rows and original witness filename. The
Archive input maps/getter aliases are not asserted here. Original schemas,
metadata, record order, predicates and numerical floors are unchanged. -/
namespace ImbalancedChen.P2OriginalSaving19Cell00Shape
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding
open ImbalancedChen.P2OriginalSaving19Moment00Decoding

def CellShape00 : Prop :=
  let g := concreteGeometry00
  let m := momentConcrete00
  g.dimension = 8 ∧ g.physicalJacobian = 1 ∧
  g.rows.size = 56 ∧ m.rows.size = 56 ∧
  g.vertexValues.size = g.vertices.size ∧
  (∀ v : Fin g.vertices.size, (g.vertices[v]).size = 8 ∧
    (g.vertexValues[v.val]!).factors.size = 10) ∧
  m.cellId = 0 ∧ m.sourceWitness = "eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json" ∧
  m.dimension = 8 ∧ m.verticesPerSimplex = 9 ∧ m.factorCount = 10 ∧
  m.logDegree = 6 ∧ m.expDegree = 3 ∧
  m.logDenominator = 2^80 ∧ m.finalDenominator = 2^96

def RowShape00 (r : Fin 56) : Prop :=
  let g := concreteGeometry00.rows[r.val]!
  let m := momentConcrete00.rows[r.val]!
  g.simplexId = r.val ∧ m.simplexId = r.val ∧
  g.vertexIds.size = 9 ∧ g.vertexIds.toList.Nodup ∧
  (∀ i : Fin 9, g.vertexIds[i.val]! < concreteGeometry00.vertices.size) ∧
  g.factorMaxima.size = 10 ∧ g.gapWeightedMeans.size = 10 ∧
  m.factorFloorsQ80.size = 10

def BoundedRowShape00 (r : Fin 56) : Prop :=
  let g := P2OriginalSaving19Geometry00BoundedAccess.boundedRow r
  let m := momentConcrete00.rows[r.val]'(P2OriginalSaving19Moment00Shape.row_bound r)
  g.simplexId = r.val ∧ m.simplexId = r.val ∧
  g.vertexIds.size = 9 ∧ g.vertexIds.toList.Nodup ∧
  (∀ i : Fin 9, g.vertexIds[i.val]! < concreteGeometry00.vertices.size) ∧
  g.factorMaxima.size = 10 ∧ g.gapWeightedMeans.size = 10 ∧
  m.factorFloorsQ80.size = 10

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_SHAPE before_opaque_cell_composition"
  err.flush

theorem cell_shape : CellShape00 :=
  ⟨P2OriginalSaving19Geometry00Shape.dimension,
    P2OriginalSaving19Geometry00Shape.physical_jacobian,
    P2OriginalSaving19Geometry00Shape.row_count,
    P2OriginalSaving19Moment00Shape.row_count,
    P2OriginalSaving19Geometry00Shape.vertex_values_size,
    P2OriginalSaving19Geometry00Shape.all_vertices,
    P2OriginalSaving19Moment00Shape.metadata⟩

theorem row_shape (r : Fin 56) : RowShape00 r := by
  rcases P2OriginalSaving19Geometry00Shape.all_rows r with
    ⟨hid, hsize, hnodup, hbounds, hmaxima, hmeans⟩
  have hm := P2OriginalSaving19Moment00Shape.row_ids_and_floor_sizes r
  exact ⟨hid, hm.1, hsize, hnodup, hbounds, hmaxima, hmeans, hm.2⟩

theorem row_shape_bounded (r : Fin 56) : BoundedRowShape00 r := by
  rcases P2OriginalSaving19Geometry00BoundedAccess.row_properties r with
    ⟨hid, hsize, hnodup, hbounds, hmaxima, hmeans⟩
  have hm := P2OriginalSaving19Moment00Shape.row_ids_and_floor_sizes_bounded r
  exact ⟨hid, hm.1, hsize, hnodup, hbounds, hmaxima, hmeans, hm.2⟩

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_SHAPE exact_original_joint_clauses_complete"
  err.flush

#print axioms cell_shape
#print axioms row_shape
#print axioms row_shape_bounded
end ImbalancedChen.P2OriginalSaving19Cell00Shape
