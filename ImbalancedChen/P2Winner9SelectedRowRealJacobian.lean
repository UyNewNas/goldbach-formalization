import ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
import ImbalancedChen.P2Winner9PhysicalVertexInterpolation
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The two rational edge determinants from the previous batch are transported
through Rat.cast_det into genuine real continuous linear equivalences.
The same edge maps define the actual physical supports, so PhaseB4's
Lebesgue affine-image theorem applies to the original row21/row22 cells
with their literal stored volumes. No rational determinant check is run
again here; the previous closed proof bodies remain unexecuted.

This supplies the geometric measure binding. Identification of the Y and
signed-deviation vertex values with SimplexData integer scales, numerical
row floors and all-row accounting remain separate.
-/

namespace ImbalancedChen.P2Winner9SelectedRowRealJacobian

noncomputable section

open Set MeasureTheory
open scoped BigOperators Matrix
open ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne

abbrev RationalVertices := Fin 9 → Fin 8 → ℚ

def realVertices (v : RationalVertices) : Fin 9 → Ambient :=
  fun i j => (v i j : ℝ)

def realEdges (v : RationalVertices) : Matrix (Fin 8) (Fin 8) ℝ :=
  (edgeMatrix v).map (fun q : ℚ => (q : ℝ))

/-- The original rational determinant is cast, not numerically reevaluated. -/
theorem realEdges_det (v : RationalVertices) :
    (realEdges v).det = ((edgeMatrix v).det : ℝ) := by
  exact (Rat.cast_det (edgeMatrix v)).symm

/-- Matrix multiplication in the actual eight physical coordinates. -/
def edgeCLM (v : RationalVertices) : Ambient →L[ℝ] Ambient :=
  (Matrix.toLin' (realEdges v)).toContinuousLinearMap

theorem edgeCLM_apply (v : RationalVertices) (x : Ambient) (i : Fin 8) :
    edgeCLM v x i = ∑ j : Fin 8, ((v j.succ i - v 0 i : ℚ) : ℝ) * x j := by
  rfl

theorem edgeCLM_det (v : RationalVertices) :
    (edgeCLM v).det = ((edgeMatrix v).det : ℝ) := by
  rw [edgeCLM, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
    realEdges_det]

theorem edgeCLM_det_ne_zero (v : RationalVertices)
    (hv : (edgeMatrix v).det ≠ 0) : (edgeCLM v).det ≠ 0 := by
  rw [edgeCLM_det]
  exact_mod_cast hv

/-- An explicit real continuous linear equivalence, justified by the
proved rational edge determinant and the injective rational embedding. -/
def realCLE (v : RationalVertices) (hv : (edgeMatrix v).det ≠ 0) :
    Ambient ≃L[ℝ] Ambient :=
  (edgeCLM v).toContinuousLinearEquivOfDetNeZero (edgeCLM_det_ne_zero v hv)

theorem realCLE_toCLM (v : RationalVertices) (hv : (edgeMatrix v).det ≠ 0) :
    (realCLE v hv).toContinuousLinearMap = edgeCLM v := by
  exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero
    (edgeCLM v) (edgeCLM_det_ne_zero v hv)

theorem realCLE_det (v : RationalVertices) (hv : (edgeMatrix v).det ≠ 0) :
    (realCLE v hv).toContinuousLinearMap.det = ((edgeMatrix v).det : ℝ) := by
  rw [realCLE_toCLM, edgeCLM_det]

theorem realCLE_apply (v : RationalVertices) (hv : (edgeMatrix v).det ≠ 0)
    (x : Ambient) : realCLE v hv x = edgeCLM v x := by
  exact ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply
    (edgeCLM v) (edgeCLM_det_ne_zero v hv) x

/-- The linear equivalence uses the same columns and the same first
vertex as the physical barycentric interpolation; no matching hypothesis
or independently chosen map is introduced. -/
theorem affinePoint_eq_vertexMap (v : RationalVertices)
    (hv : (edgeMatrix v).det ≠ 0) (x : Ambient) :
    affinePoint (realCLE v hv) (realVertices v 0) x =
      vertexMap (realVertices v) x := by
  ext i
  rw [affinePoint, Pi.add_apply, realCLE_apply, edgeCLM_apply]
  simp only [vertexMap, realVertices, Rat.cast_sub]

/-- The support is defined directly by the actual ordered raw vertices,
independently of the nonzero-determinant proof used to construct an inverse. -/
def sourceSupport (v : RationalVertices) : Set Ambient :=
  vertexMap (realVertices v) '' canonicalSupport

theorem physicalSupport_eq_sourceSupport (v : RationalVertices)
    (hv : (edgeMatrix v).det ≠ 0) :
    physicalSupport (realCLE v hv) (realVertices v 0) = sourceSupport v := by
  unfold physicalSupport sourceSupport
  congr 1
  funext x
  exact affinePoint_eq_vertexMap v hv x

theorem sourceSupport_compact (v : RationalVertices)
    (hv : (edgeMatrix v).det ≠ 0) : IsCompact (sourceSupport v) := by
  rw [← physicalSupport_eq_sourceSupport v hv]
  exact physicalSupport_compact (realCLE v hv) (realVertices v 0)

theorem sourceSupport_measurable (v : RationalVertices)
    (hv : (edgeMatrix v).det ≠ 0) : MeasurableSet (sourceSupport v) :=
  (sourceSupport_compact v hv).isClosed.measurableSet

/-- The actual row support now instantiates the affine-image measure
formula. The only hypothesis is edge nondegeneracy, proved for both rows
below from their frozen rational determinant source. -/
theorem source_integral (v : RationalVertices)
    (hv : (edgeMatrix v).det ≠ 0) (f : Ambient → ℝ) :
    (∫ y in sourceSupport v, f y) =
      |((edgeMatrix v).det : ℝ)| *
        ∫ x in canonicalSupport, f (vertexMap (realVertices v) x) := by
  have h := physical_integral (realCLE v hv) (realVertices v 0) f
  simpa only [physicalSupport_eq_sourceSupport, realCLE_det,
    affinePoint_eq_vertexMap] using h

theorem source_volume (v : RationalVertices)
    (hv : (edgeMatrix v).det ≠ 0) :
    (∫ _y in sourceSupport v, (1 : ℝ)) =
      |((edgeMatrix v).det : ℝ)| / (8.factorial : ℝ) := by
  have h := physical_volume (realCLE v hv) (realVertices v 0)
  simpa only [physicalSupport_eq_sourceSupport, realCLE_det] using h

/-- Genuine physical mixed integral with the actual vertex values. The
three vertex arrays have not yet been identified with SimplexData scales. -/
theorem source_mixed_integral (v : RationalVertices)
    (hv : (edgeMatrix v).det ≠ 0) (means : Fin 10 → ℝ) (U : ℝ)
    (j : Fin 10) :
    (∫ y in sourceSupport v, physicalMixedIntegrand means U j y) =
      |((edgeMatrix v).det : ℝ)| *
        ∫ x in canonicalSupport,
          affine (fun k => physicalGap (realVertices v k)) x *
          affine (fun k => physicalY means U (realVertices v k)) x *
          (affine (fun k => physicalDeviation means j (realVertices v k)) x)^2 := by
  simpa only [physicalMixedIntegrand_vertexMap] using
    source_integral v hv (physicalMixedIntegrand means U j)

/-- The original upper integrand retains factor four and all ten actual
physical factors on the actual measured source support. -/
theorem source_upper_integral (v : RationalVertices)
    (hv : (edgeMatrix v).det ≠ 0) :
    (∫ y in sourceSupport v, physicalUpperIntegrand y) =
      |((edgeMatrix v).det : ℝ)| *
        ∫ x in canonicalSupport,
          4 * affine (fun k => physicalGap (realVertices v k)) x /
            ∏ j : Fin 10,
              affine (fun k => physicalFactor j (realVertices v k)) x := by
  simpa only [physicalUpperIntegrand_vertexMap] using
    source_integral v hv physicalUpperIntegrand

/-- Concrete row equivalences; these contain no new matrix-reduction
procedure and inherit the first batch's explicitly unexecuted proofs. -/
def row21CLE : Ambient ≃L[ℝ] Ambient := realCLE row21 row21_det_ne_zero

def row22CLE : Ambient ≃L[ℝ] Ambient := realCLE row22 row22_det_ne_zero

theorem row21_jacobian :
    |row21CLE.toContinuousLinearMap.det| =
      (8.factorial : ℝ) * (P2Winner9Row21RawVertexData.physicalVolume : ℝ) := by
  rw [row21CLE, realCLE_det]
  exact_mod_cast row21_abs_det_volume

theorem row22_jacobian :
    |row22CLE.toContinuousLinearMap.det| =
      (8.factorial : ℝ) * (row22Volume : ℝ) := by
  rw [row22CLE, realCLE_det]
  exact_mod_cast row22_abs_det_volume

/-- The concrete nonzero-Jacobian guard needed for cancellation in the
physical weighted mixed expectation is discharged for each selected row. -/
theorem row21_jacobian_pos : 0 < |row21CLE.toContinuousLinearMap.det| := by
  rw [row21_jacobian]
  exact mul_pos (by norm_num) (by exact_mod_cast row21_volume_pos)

theorem row22_jacobian_pos : 0 < |row22CLE.toContinuousLinearMap.det| := by
  rw [row22_jacobian]
  exact mul_pos (by norm_num) (by exact_mod_cast row22_volume_pos)

/-- The actual physical row21 cell has its literal saved volume. -/
theorem row21_actual_volume :
    (∫ _y in sourceSupport row21, (1 : ℝ)) =
      (P2Winner9Row21RawVertexData.physicalVolume : ℝ) := by
  rw [source_volume row21 row21_det_ne_zero]
  have h : |((edgeMatrix row21).det : ℝ)| =
      (8.factorial : ℝ) * (P2Winner9Row21RawVertexData.physicalVolume : ℝ) := by
    exact_mod_cast row21_abs_det_volume
  rw [h]
  have hn : (8.factorial : ℝ) ≠ 0 := by norm_num
  field_simp [hn] <;> ring

/-- The actual physical row22 cell has its distinct literal saved volume. -/
theorem row22_actual_volume :
    (∫ _y in sourceSupport row22, (1 : ℝ)) = (row22Volume : ℝ) := by
  rw [source_volume row22 row22_det_ne_zero]
  have h : |((edgeMatrix row22).det : ℝ)| =
      (8.factorial : ℝ) * (row22Volume : ℝ) := by
    exact_mod_cast row22_abs_det_volume
  rw [h]
  have hn : (8.factorial : ℝ) ≠ 0 := by norm_num
  field_simp [hn] <;> ring

theorem row21_actual_integral (f : Ambient → ℝ) :
    (∫ y in sourceSupport row21, f y) =
      ((8.factorial : ℝ) * (P2Winner9Row21RawVertexData.physicalVolume : ℝ)) *
        ∫ x in canonicalSupport, f (vertexMap (realVertices row21) x) := by
  rw [source_integral row21 row21_det_ne_zero]
  congr 1
  exact_mod_cast row21_abs_det_volume

theorem row22_actual_integral (f : Ambient → ℝ) :
    (∫ y in sourceSupport row22, f y) =
      ((8.factorial : ℝ) * (row22Volume : ℝ)) *
        ∫ x in canonicalSupport, f (vertexMap (realVertices row22) x) := by
  rw [source_integral row22 row22_det_ne_zero]
  congr 1
  exact_mod_cast row22_abs_det_volume

end

end ImbalancedChen.P2Winner9SelectedRowRealJacobian
