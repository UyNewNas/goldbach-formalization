import ImbalancedChen.P2OriginalSaving19ArchiveCore
import ImbalancedChen.P2OriginalSaving19Geometry01Decoded
import ImbalancedChen.P2OriginalSaving19Geometry01Shape

/-!
SOURCE ONLY: this bridge has not been compiled or kernel-replayed locally.
Complete direct project-source dependency set:
  ImbalancedChen.P2OriginalSaving19ArchiveCore
  ImbalancedChen.P2OriginalSaving19Geometry01Decoded
  ImbalancedChen.P2OriginalSaving19Geometry01Shape
The first dependency supplies the unchanged Archive geometryText/geometryParse/
geometry definitions and Fin 13 input map. The other two supply the concrete
original cell01 parse/decode equality and the complete original shape facts.
Only index (1 : Fin 13) is specialized. There is no new parse, schema, shape,
geometric, analytic, or all-cells hypothesis. The row theorem below uses the
actual Archive row-array size as its finite domain.
-/
namespace ImbalancedChen.P2OriginalSaving19Geometry01ArchiveBridge
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01Decoding

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_ARCHIVE before_aliases"
  err.flush

theorem geometryChars_one :
    geometryChars (1 : Fin 13) = geometryPacked01.toList := by rfl

theorem geometryText_one :
    geometryText (1 : Fin 13) = String.ofList geometryPacked01.toList :=
  congrArg String.ofList geometryChars_one

theorem geometryParse_one :
    geometryParse (1 : Fin 13) = .ok concreteGeometry01 := by
  change (SourceJson.parse (String.ofList geometryPacked01.toList) >>= decodeGeometry) =
    .ok concreteGeometry01
  exact geometryPacked01_parse_decode

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_ARCHIVE parse_transport_complete"
  err.flush

theorem geometry_one :
    geometry (1 : Fin 13) = concreteGeometry01 :=
  congrArg (fun result : Except String Geometry => result.toOption.getD default)
    geometryParse_one

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_ARCHIVE aliases_complete"
  err.flush

theorem dimension : (geometry (1 : Fin 13)).dimension = 8 := by
  rw [geometry_one]
  exact P2OriginalSaving19Geometry01Shape.dimension

theorem physical_jacobian :
    (geometry (1 : Fin 13)).physicalJacobian = 1 := by
  rw [geometry_one]
  exact P2OriginalSaving19Geometry01Shape.physical_jacobian

theorem row_count : (geometry (1 : Fin 13)).rows.size = 144 := by
  rw [geometry_one]
  exact P2OriginalSaving19Geometry01Shape.row_count

theorem vertex_count : (geometry (1 : Fin 13)).vertices.size = 40 := by
  rw [geometry_one]
  exact P2OriginalSaving19Geometry01Shape.vertex_count

theorem vertex_values_size :
    (geometry (1 : Fin 13)).vertexValues.size =
      (geometry (1 : Fin 13)).vertices.size := by
  rw [geometry_one]
  exact P2OriginalSaving19Geometry01Shape.vertex_values_size

theorem facet_count :
    (geometry (1 : Fin 13)).facetOriginalIndices.size = 12 := by
  rw [geometry_one]
  exact P2OriginalSaving19Geometry01Shape.facet_count

theorem facet_vertices_size :
    (geometry (1 : Fin 13)).facetVertices.size = 12 := by
  rw [geometry_one]
  exact P2OriginalSaving19Geometry01Shape.facet_vertices_size

theorem face_count : (geometry (1 : Fin 13)).faces.size = 79 := by
  rw [geometry_one]
  exact P2OriginalSaving19Geometry01Shape.face_count

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_ARCHIVE before_all_vertices"
  err.flush

abbrev VertexShape01 (g : Geometry) : Prop :=
  ∀ v : Fin g.vertices.size,
    (g.vertices[v.val]'v.isLt).size = 8 ∧
    (g.vertexValues[v.val]!).factors.size = 10

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_ARCHIVE vertex_predicate_ready"
  err.flush

theorem vertexShape01_iff (g : Geometry) :
    VertexShape01 g ↔
      ∀ v : Fin g.vertices.size,
        (g.vertices[v.val]'v.isLt).size = 8 ∧
        (g.vertexValues[v.val]!).factors.size = 10 :=
  Iff.rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_ARCHIVE vertex_predicate_equivalence_ready"
  err.flush

private theorem concreteVertices01 : VertexShape01 concreteGeometry01 :=
  P2OriginalSaving19Geometry01Shape.all_vertices

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_ARCHIVE concrete_vertex_fact_ready"
  err.flush

private theorem archiveVertices01 : VertexShape01 (geometry (1 : Fin 13)) :=
  Eq.ndrec (motive := VertexShape01) concreteVertices01 geometry_one.symm

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_ARCHIVE archive_vertex_transport_ready"
  err.flush

theorem all_vertices : VertexShape01 (geometry (1 : Fin 13)) :=
  archiveVertices01

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_ARCHIVE public_all_vertices_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_ARCHIVE before_all_rows"
  err.flush

theorem all_rows (r : Fin (geometry (1 : Fin 13)).rows.size) :
    let g := (geometry (1 : Fin 13)).rows[r.val]!
    g.simplexId = r.val ∧
    g.vertexIds.size = 9 ∧ g.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, g.vertexIds[i.val]! < (geometry (1 : Fin 13)).vertices.size) ∧
    g.factorMaxima.size = 10 ∧ g.gapWeightedMeans.size = 10 := by
  have hr : r.val < 144 := by simpa only [row_count] using r.isLt
  simpa only [geometry_one] using
    (P2OriginalSaving19Geometry01Shape.all_rows ⟨r.val, hr⟩)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_ARCHIVE shape_transport_complete"
  err.flush

#print axioms geometryChars_one
#print axioms geometryText_one
#print axioms geometryParse_one
#print axioms geometry_one
#print axioms dimension
#print axioms physical_jacobian
#print axioms row_count
#print axioms vertex_count
#print axioms vertex_values_size
#print axioms facet_count
#print axioms facet_vertices_size
#print axioms face_count
#print axioms all_vertices
#print axioms all_rows
end ImbalancedChen.P2OriginalSaving19Geometry01ArchiveBridge
