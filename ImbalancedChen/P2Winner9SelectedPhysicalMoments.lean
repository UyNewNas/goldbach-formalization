import ImbalancedChen.P2Winner9SelectedPhysicalMeans
import ImbalancedChen.P2Winner9PowerMoment

/-! Transport of gap-weighted moments from the physical rows to the canonical simplex. -/

namespace ImbalancedChen.P2Winner9SelectedPhysicalMoments

noncomputable section

open Set MeasureTheory
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9SelectedPhysicalMeans
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9PowerMoment

/-- The gap scaling and Jacobian cancel against the physical gap mass. -/
theorem normalized_weighted_transport (r : Fin 2) (f : Ambient → ℝ) :
    (∫ z in sourceSupport (vertices r), physicalGap z * f z) / gapMass r =
      (∫ x in canonicalSupport, affine (gapVertices (data r)) x *
        f (vertexMap (realVertices (vertices r)) x)) / actualGapMass (data r) := by
  have hgap := (real_vertex_arrays (vertices r) (means r) (upper r) (data r)
    (gapScale r) (row_vertex_normalization r)).1
  rw [source_integral (vertices r) (row_det_ne_zero r), gapMass_typed]
  have he (x : Ambient) :
      (affine (gapVertices (data r)) x / (gapScale r : ℝ)) *
          f (vertexMap (realVertices (vertices r)) x) =
        (gapScale r : ℝ)⁻¹ * (affine (gapVertices (data r)) x *
          f (vertexMap (realVertices (vertices r)) x)) := by ring
  simp_rw [physicalGap_vertexMap, hgap, affine_div, he]
  rw [integral_const_mul]
  have hscale : (gapScale r : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast (row_vertex_normalization r).1)
  change jacobian r * ((gapScale r : ℝ)⁻¹ * _) /
    ((jacobian r / (gapScale r : ℝ)) * actualGapMass (data r)) = _
  rw [← mul_assoc, ← div_eq_mul_inv]
  exact mul_div_mul_left _ _ (div_ne_zero (jacobian_pos r).ne' hscale)

def physicalPowerMean (r : Fin 2) (k : ℕ) : ℝ :=
  (∫ z in sourceSupport (vertices r), physicalGap z *
    (physicalY (fun j => (means r j : ℝ)) (upper r : ℝ) z)^k) / gapMass r

theorem physicalPowerMean_eq (r : Fin 2) (k : ℕ) :
    physicalPowerMean r k = actualPowerExpectation (data r) k := by
  have hY := (real_vertex_arrays (vertices r) (means r) (upper r) (data r)
    (gapScale r) (row_vertex_normalization r)).2.1
  rw [physicalPowerMean, normalized_weighted_transport]
  simp only [physicalY_vertexMap, hY]
  rfl

theorem physical_weighted_deviation_sq (r : Fin 2) (j : Fin 10) :
    (∫ z in sourceSupport (vertices r), physicalGap z *
      (physicalDeviation (fun i => (means r i : ℝ)) j z)^2) / gapMass r =
      (∫ x in canonicalSupport, affine (gapVertices (data r)) x *
        (affine (bVertices (data r) j) x)^2) / actualGapMass (data r) := by
  have hB := (real_vertex_arrays (vertices r) (means r) (upper r) (data r)
    (gapScale r) (row_vertex_normalization r)).2.2 j
  rw [normalized_weighted_transport]
  simp only [physicalDeviation_vertexMap, hB]

end

end ImbalancedChen.P2Winner9SelectedPhysicalMoments
