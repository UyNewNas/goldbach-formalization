import ImbalancedChen.P2OriginalSaving19Geometry00PackedDecoded

/-! Concrete shape of the original geometry cell00 after its complete original
parser and actual typed decoder have been certified. Every actual vertex and
row is included. These are shape and lookup-bound facts only. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Shape
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_SHAPE before_metadata"
  err.flush

theorem dimension : concreteGeometry00.dimension = 8 := by rfl

theorem physical_jacobian : concreteGeometry00.physicalJacobian = 1 := by rfl

theorem row_count : concreteGeometry00.rows.size = 56 := by rfl

theorem vertex_count : concreteGeometry00.vertices.size = 28 := by rfl

theorem vertex_values_size :
    concreteGeometry00.vertexValues.size = concreteGeometry00.vertices.size := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_SHAPE before_all_28_vertices"
  err.flush

theorem all_vertices : ∀ v : Fin concreteGeometry00.vertices.size,
    (concreteGeometry00.vertices[v]).size = 8 ∧
    (concreteGeometry00.vertexValues[v.val]!).factors.size = 10 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_SHAPE all_28_vertices_complete_before_all_56_rows"
  err.flush

theorem all_rows : ∀ r : Fin 56,
    let g := concreteGeometry00.rows[r.val]!
    g.simplexId = r.val ∧
    g.vertexIds.size = 9 ∧ g.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, g.vertexIds[i.val]! < concreteGeometry00.vertices.size) ∧
    g.factorMaxima.size = 10 ∧ g.gapWeightedMeans.size = 10 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_SHAPE all_56_rows_complete"
  err.flush

#print axioms dimension
#print axioms physical_jacobian
#print axioms row_count
#print axioms vertex_count
#print axioms vertex_values_size
#print axioms all_vertices
#print axioms all_rows
end ImbalancedChen.P2OriginalSaving19Geometry00Shape
