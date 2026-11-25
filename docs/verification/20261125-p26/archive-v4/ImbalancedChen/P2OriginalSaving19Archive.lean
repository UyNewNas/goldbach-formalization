import ImbalancedChen.P2OriginalSaving19ArchiveCore

/-!
SOURCE CANDIDATE, NOT COMPILED OR ACCEPTED. This facade retains all original
parse-success, cell-shape, row-shape, row-id and row-count obligations. Their
statements and proof bodies are unchanged. Only runtime definitions/Decidable
instances depending on the new noncomputable input are marked noncomputable.
No successful v4 Archive or downstream numerical acceptance is claimed.
-/
namespace ImbalancedChen.P2OriginalSaving19Archive

set_option maxRecDepth 1000000

/-- Closed pure kernel checks, deliberately NOT run in this source task.
The .getD fallback is eliminated by these source-data equalities. -/
theorem geometry_parse_success : ∀ c, geometryParse c = .ok (geometry c) := by decide
theorem moments_parse_success : ∀ c, momentParse c = .ok (moments c) := by decide

open P2OriginalSaving19MomentFloorConsumer

def geometryWitnessName (c : Fin 13) : String :=
  "eighth-third-minorant-extension-20261009-a23-s23_low-" ++
    (!["00", "01", "02", "03", "04", "05", "06", "07", "08", "09", "10", "11", "12"] c) ++
    "-cell.witness.json"

def CellShape (c : Fin 13) : Prop :=
  let g := geometry c
  let m := moments c
  g.dimension = 8 ∧ g.physicalJacobian = 1 ∧
  g.rows.size = originalRowCount c ∧ m.rows.size = originalRowCount c ∧
  g.vertexValues.size = g.vertices.size ∧
  (∀ v : Fin g.vertices.size, (g.vertices[v]).size = 8 ∧
    (g.vertexValues[v.val]!).factors.size = 10) ∧
  m.cellId = c.val ∧ m.sourceWitness = geometryWitnessName c ∧
  m.dimension = 8 ∧ m.verticesPerSimplex = 9 ∧ m.factorCount = 10 ∧
  m.logDegree = 6 ∧ m.expDegree = 3 ∧
  m.logDenominator = 2^80 ∧ m.finalDenominator = 2^96

noncomputable instance (c : Fin 13) : Decidable (CellShape c) := by unfold CellShape; infer_instance

theorem original_cell_shapes : ∀ c, CellShape c := by decide

noncomputable def rawGeometryRow (r : OriginalRowIndex) : GeometryRow :=
  (geometry r.1).rows[r.2.val]!

noncomputable def rawMomentRow (r : OriginalRowIndex) : MomentRecord :=
  (moments r.1).rows[r.2.val]!

def RowShape (r : OriginalRowIndex) : Prop :=
  let g := rawGeometryRow r
  let m := rawMomentRow r
  g.simplexId = r.2.val ∧ m.simplexId = r.2.val ∧
  g.vertexIds.size = 9 ∧ g.vertexIds.toList.Nodup ∧
  (∀ i : Fin 9, g.vertexIds[i.val]! < (geometry r.1).vertices.size) ∧
  g.factorMaxima.size = 10 ∧ g.gapWeightedMeans.size = 10 ∧
  m.factorFloorsQ80.size = 10

noncomputable instance (r : OriginalRowIndex) : Decidable (RowShape r) := by unfold RowShape; infer_instance

theorem original_row_shapes : ∀ r, RowShape r := by decide

theorem original_row_ids (r : OriginalRowIndex) :
    (rawGeometryRow r).simplexId = r.2.val ∧
    (rawMomentRow r).simplexId = r.2.val :=
  ⟨(original_row_shapes r).1, (original_row_shapes r).2.1⟩

/-- Physical ordered vertices, exactly in the producer's nine-ID order. -/
noncomputable def rawVertex (r : OriginalRowIndex) (i : Fin 9) (j : Fin 8) : ℚ :=
  ((geometry r.1).vertices[(rawGeometryRow r).vertexIds[i.val]!]!)[j.val]!

theorem original_row_count : Fintype.card OriginalRowIndex = 28918 := by
  rw [Fintype.card_sigma]
  simpa using originalRowCount_sum

end ImbalancedChen.P2OriginalSaving19Archive
