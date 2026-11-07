import ImbalancedChen.P2OriginalSaving16OriginalArchive
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original rational edge matrix constructs the actual physical simplex
map; neither determinant, volume, means nor vertex/source membership are
semantic record fields. The resulting endpoint is a sum of the39,741 true
simplex integrals. It is deliberately NOT asserted to be bounded by the
source-region integral: that requires the still-open within-cell pulling
ownership theorem. No coverage/disjointness premise is used to mask it.
-/
namespace ImbalancedChen.P2OriginalSaving16SimplexBinding

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16JensenFloor
open P2OriginalSaving16OriginalArchive

def edgeLinear (v : Fin 9 → QPoint) : Point →L[ℝ] Point :=
  (Matrix.toLin' ((edgeMatrix v).transpose.map (fun q => (q : ℝ)))).toContinuousLinearMap

theorem edgeLinear_det (v : Fin 9 → QPoint) :
    (edgeLinear v).det = ((edgeMatrix v).det : ℝ) := by
  rw [edgeLinear, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
    ← Rat.cast_det, Matrix.det_transpose]

def edgeEquiv (v : Fin 9 → QPoint) (h : (edgeMatrix v).det ≠ 0) : Point ≃L[ℝ] Point :=
  (edgeLinear v).toContinuousLinearEquivOfDetNeZero (by
    rw [edgeLinear_det]
    exact_mod_cast h)

/-- The transposition matches the producer's row-edge determinant with
the column convention of the physical affine map. -/
theorem edge_vertices (v : Fin 9 → QPoint) (h : (edgeMatrix v).det ≠ 0) :
    Bary.vertices (edgeEquiv v h) (castPoint (v 0)) = fun i => castPoint (v i) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [Bary.vertices]
  · intro k
    ext j
    simp [Bary.vertices, edgeEquiv, edgeLinear, Matrix.toLin'_apply,
      Matrix.mulVec_single, Matrix.transpose_apply, Matrix.map_apply,
      edgeMatrix, castPoint]

theorem physicalVolumeQ_cast (v : Fin 9 → QPoint) (h : (edgeMatrix v).det ≠ 0) :
    (physicalVolumeQ v : ℝ) = Bary.physicalVolume (edgeEquiv v h) := by
  simp only [physicalVolumeQ, Bary.physicalVolume, Bary.jacobian, edgeEquiv,
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero, edgeLinear_det,
    Rat.cast_div, Rat.cast_abs, Rat.cast_natCast]

theorem gapQ_cast (x : QPoint) : (gapQ x : ℝ) = gap (castPoint x) := by
  norm_num [gapQ, capQ, comparisonQ, gap, ascendingCap, R, VariableEnvelope.C,
    VariableEnvelope.A, selectedSum, eta, d, castPoint]

theorem factorsQ_cast (x : QPoint) (j : Fin 10) :
    (factorsQ x j : ℝ) = factors (castPoint x) j := by
  fin_cases j <;>
    norm_num [factorsQ, comparisonQ, capQ, factors, R, d, S, ascendingCap,
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

abbrev RowIndex := Σ i : Fin 14, Fin (archive i).simplices.size

def rowVertices (i : Fin 14) (s : Fin (archive i).simplices.size) : Fin 9 → QPoint :=
  simplexVertices (archive i) (archive i).simplices[s]

theorem row_det_ne_zero (i : Fin 14) (s : Fin (archive i).simplices.size) :
    (edgeMatrix (rowVertices i s)).det ≠ 0 := by
  have h := original_simplex_operations i s
  rcases h with ⟨_, _, _, hvol, _⟩
  change 0 < physicalVolumeQ (rowVertices i s) at hvol
  intro hz
  simp [physicalVolumeQ, hz] at hvol

theorem row_gapTotal_pos (i : Fin 14) (s : Fin (archive i).simplices.size) :
    0 < gapTotalQ (rowVertices i s) := by
  have h := original_simplex_operations i s
  rcases h with ⟨_, _, _, _, hG, _⟩
  exact hG

theorem row_vertex_mem_closure (i : Fin 14) (s : Fin (archive i).simplices.size)
    (k : Fin 9) : castPoint (rowVertices i s k) ∈ closure (cell (atlasCell i)) := by
  have h := original_simplex_operations i s
  rcases h with ⟨_, _, hids, _⟩
  exact original_vertex_mem_closure i
    ⟨((archive i).simplices[s]).vertexIds.getD k.val 0, hids k⟩

def rowMap (i : Fin 14) (s : Fin (archive i).simplices.size) : Point ≃L[ℝ] Point :=
  edgeEquiv (rowVertices i s) (row_det_ne_zero i s)

def rowSupport (i : Fin 14) (s : Fin (archive i).simplices.size) : Set Point :=
  Bary.support (rowMap i s) (castPoint (rowVertices i s 0))

theorem rowSupport_subset_closure (i : Fin 14) (s : Fin (archive i).simplices.size) :
    rowSupport i s ⊆ closure (cell (atlasCell i)) := by
  apply support_subset_closure
  intro k
  rw [rowMap, edge_vertices]
  exact row_vertex_mem_closure i s k

/-- Actual row proof, with all geometric and encoding parameters filled
from the same original witness. Its closed source guards remain unevaluated. -/
theorem original_row_q96 (i : Fin 14) (s : Fin (archive i).simplices.size) :
    (q96Floor (jensenQ (rowVertices i s)) : ℝ) / (2 : ℝ) ^ 96 ≤
      ∫ t in rowSupport i s, sourceDensity t := by
  apply original_simplex_q96 (atlasCell i) (rowMap i s)
    (castPoint (rowVertices i s 0))
  · intro k
    rw [rowMap, edge_vertices]
    exact row_vertex_mem_closure i s k
  · rw [rowMap, edge_vertices, ← gapTotalQ_cast]
    exact_mod_cast row_gapTotal_pos i s
  · exact jensenQ_cast (rowVertices i s) (row_det_ne_zero i s)

/-- No assumed target estimate: the closed original-operation aggregate
and39,741 actual per-simplex inequalities give this sum of integrals.
The final region comparison is intentionally not asserted. -/
theorem historical_endpoint_le_sum_simplex_integrals :
    (1222997719565324892497827 : ℝ) / (2 : ℝ) ^ 96 ≤
      ∑ i : Fin 14, ∑ s : Fin (archive i).simplices.size,
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
end ImbalancedChen.P2OriginalSaving16SimplexBinding
