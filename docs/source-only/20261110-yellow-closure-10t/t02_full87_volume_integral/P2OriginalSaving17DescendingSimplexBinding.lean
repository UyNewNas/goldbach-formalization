import ImbalancedChen.P2OriginalSaving17DescendingArchive

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The unchanged generic rational edge-map and determinant lemmas are reused
from saving16. Every actual descending cap/gap/mean and Q96 floor below
comes from the same stage17 witness row. -/
namespace ImbalancedChen.P2OriginalSaving17DescendingSimplexBinding
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalDescendingEighthLogSemantics
open P2OriginalSaving17DescendingGeometry
open P2OriginalSaving17DescendingArchive
open P2OriginalSaving16OriginalArchive (QPoint castPoint edgeMatrix physicalVolumeQ simplexVertices)
open P2OriginalSaving16SimplexBinding
  (edgeLinear edgeLinear_det edgeEquiv edge_vertices physicalVolumeQ_cast)
open P2OriginalSaving16JensenFloor (q96Floor q96Floor_le)
theorem gapQ_cast (x : QPoint) : (gapQ x : ℝ) = gap (castPoint x) := by
  norm_num [gapQ, capQ, comparisonQ, gap, newCap, oldRaw, VariableEnvelope.C,
    VariableEnvelope.A, selectedSum, eta, d, castPoint]

theorem factorsQ_cast (x : QPoint) (j : Fin 10) :
    (factorsQ x j : ℝ) = factors (castPoint x) j := by
  fin_cases j <;>
    norm_num [factorsQ, comparisonQ, capQ, factors, denominatorFactors, oldRaw, d, total, newCap,
      VariableEnvelope.C, VariableEnvelope.A, selectedSum, eta, castPoint]

theorem gapTotalQ_cast (v : Fin 9 → QPoint) :
    (gapTotalQ v : ℝ) = gapTotal (fun i => castPoint (v i)) := by
  simp [gapTotalQ, gapTotal, gapQ_cast]

theorem meansQ_cast (v : Fin 9 → QPoint) (j : Fin 10) :
    (meansQ v j : ℝ) = factorMean (fun i => castPoint (v i)) j := by
  simp [meansQ, factorMean, gapTotalQ_cast, gapQ_cast, factorsQ_cast]

theorem jensenQ_cast (v : Fin 9 → QPoint) (h : (edgeMatrix v).det ≠ 0) :
    (jensenQ v : ℝ) =
      4 * Bary.physicalVolume (edgeEquiv v h) *
        (gapTotal (Bary.vertices (edgeEquiv v h) (castPoint (v 0))) / 9) /
          ∏ j : Fin 10, factorMean
            (Bary.vertices (edgeEquiv v h) (castPoint (v 0))) j := by
  rw [edge_vertices]
  simp [jensenQ, physicalVolumeQ_cast v h, gapTotalQ_cast, meansQ_cast]

abbrev RowIndex := Σ i : Fin 15, Fin (archive i).simplices.size

def rowVertices (i : Fin 15) (s : Fin (archive i).simplices.size) : Fin 9 → QPoint :=
  simplexVertices (archive i) (archive i).simplices[s]

theorem row_det_ne_zero (i : Fin 15) (s : Fin (archive i).simplices.size) :
    (edgeMatrix (rowVertices i s)).det ≠ 0 := by
  have h := original_simplex_operations i s
  rcases h with ⟨_, _, _, hvol, _⟩
  change 0 < physicalVolumeQ (rowVertices i s) at hvol
  intro hz
  simp [physicalVolumeQ, hz] at hvol

theorem row_gapTotal_pos (i : Fin 15) (s : Fin (archive i).simplices.size) :
    0 < gapTotalQ (rowVertices i s) := by
  have h := original_simplex_operations i s
  rcases h with ⟨_, _, _, _, hG, _⟩
  exact hG

theorem row_vertex_mem_closure (i : Fin 15) (s : Fin (archive i).simplices.size)
    (k : Fin 9) : castPoint (rowVertices i s k) ∈ closure (cell i) := by
  have h := original_simplex_operations i s
  rcases h with ⟨_, _, hids, _⟩
  exact original_vertex_mem_closure i
    ⟨((archive i).simplices[s]).vertexIds.getD k.val 0, hids k⟩

def rowMap (i : Fin 15) (s : Fin (archive i).simplices.size) : Point ≃L[ℝ] Point :=
  edgeEquiv (rowVertices i s) (row_det_ne_zero i s)

def rowSupport (i : Fin 15) (s : Fin (archive i).simplices.size) : Set Point :=
  Bary.support (rowMap i s) (castPoint (rowVertices i s 0))

theorem rowSupport_subset_closure (i : Fin 15) (s : Fin (archive i).simplices.size) :
    rowSupport i s ⊆ closure (cell i) := by
  apply support_subset_closure
  intro k
  rw [rowMap, edge_vertices]
  exact row_vertex_mem_closure i s k

/-- Actual row proof, with all geometric and encoding parameters filled
from the same original witness. Its closed source guards remain unevaluated. -/
theorem original_row_q96 (i : Fin 15) (s : Fin (archive i).simplices.size) :
    (q96Floor (jensenQ (rowVertices i s)) : ℝ) / (2 : ℝ) ^ 96 ≤
      ∫ t in rowSupport i s, sourceDensity t := by
  apply (q96Floor_le _).trans
  rw [jensenQ_cast (rowVertices i s) (row_det_ne_zero i s)]
  apply original_simplex_jensen i (rowMap i s) (castPoint (rowVertices i s 0))
  · intro k
    rw [rowMap, edge_vertices]
    exact row_vertex_mem_closure i s k
  · rw [rowMap, edge_vertices, ← gapTotalQ_cast]
    exact_mod_cast row_gapTotal_pos i s

/-- No assumed target estimate: the closed original-operation aggregate
and63,612 actual per-simplex inequalities give this sum of integrals.
The final region comparison is intentionally not asserted. -/
theorem historical_endpoint_le_sum_simplex_integrals :
    (467454156274267811817033 : ℝ) / (2 : ℝ) ^ 96 ≤
      ∑ i : Fin 15, ∑ s : Fin (archive i).simplices.size,
        ∫ t in rowSupport i s, sourceDensity t := by
  rw [← original_q96_aggregate_real]
  apply Finset.sum_le_sum
  intro i _
  have he : (cellFloorNumerator i : ℝ) / (2 : ℝ) ^ 96 =
      ∑ s : Fin (archive i).simplices.size,
        (q96Floor (jensenQ (rowVertices i s)) : ℝ) / (2 : ℝ) ^ 96 := by
    simp [cellFloorNumerator, rowVertices, Finset.sum_div]
  rw [he]
  exact Finset.sum_le_sum (fun s _ => original_row_q96 i s)

end
end ImbalancedChen.P2OriginalSaving17DescendingSimplexBinding

