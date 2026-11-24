import ImbalancedChen.P2Winner9SelectedRowAnalyticCaps

/-! Exact gap mass and the stored Jensen prefactor for the physical rows. -/

namespace ImbalancedChen.P2Winner9SelectedPhysicalMeans

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor

def jacobian (r : Fin 2) : ℝ := |((edgeMatrix (vertices r)).det : ℝ)|

def gapMass (r : Fin 2) : ℝ := ∫ z in sourceSupport (vertices r), physicalGap z

theorem row_det_ne_zero (r : Fin 2) : (edgeMatrix (vertices r)).det ≠ 0 := by
  fin_cases r
  · simpa [vertices] using row21_det_ne_zero
  · simpa [vertices] using row22_det_ne_zero

theorem jacobian_pos (r : Fin 2) : 0 < jacobian r := by
  apply abs_pos.mpr
  exact_mod_cast row_det_ne_zero r

def gapScale (r : Fin 2) : Nat := if r = 0 then Row21.gapDen else Row22.gapDen

theorem row_vertex_normalization (r : Fin 2) :
    VertexNormalization (vertices r) (means r) (upper r) (data r) (gapScale r) := by
  fin_cases r
  · simpa [vertices, means, upper, data, gapScale] using row21_vertex_normalization
  · simpa [vertices, means, upper, data, gapScale] using row22_vertex_normalization

/-- The same physical gap mass uses the exact gd and typed canonical mass. -/
theorem gapMass_typed (r : Fin 2) :
    gapMass r = (jacobian r / (gapScale r : ℝ)) * actualGapMass (data r) := by
  have hg := (real_vertex_arrays (vertices r) (means r) (upper r)
    (data r) (gapScale r) (row_vertex_normalization r)).1
  rw [gapMass, source_integral (vertices r) (row_det_ne_zero r)]
  simp only [physicalGap_vertexMap, hg, affine_div]
  have he (x : Ambient) : affine (gapVertices (data r)) x / (gapScale r : ℝ) =
      (1 / (gapScale r : ℝ)) * affine (gapVertices (data r)) x := by ring
  simp_rw [he]
  rw [integral_const_mul]
  change jacobian r * ((1 / (gapScale r : ℝ)) * actualGapMass (data r)) = _
  ring

theorem gapMass_pos (r : Fin 2) : 0 < gapMass r := by
  rw [gapMass_typed]
  have hscale : (0 : ℝ) < (gapScale r : ℝ) := by
    exact_mod_cast (row_vertex_normalization r).1
  exact mul_pos (div_pos (jacobian_pos r) hscale) (actualGapMass_pos (data r))

/-- The source sheet stores the absolute determinant as eight factorial times
its original simplex volume. -/
def storedJacobian (r : Fin 2) : ℚ :=
  ((8 : ℕ).factorial : ℚ) * (if r = 0 then P2Winner9Row21RawVertexData.physicalVolume else row22Volume)

theorem jacobian_eq_stored (r : Fin 2) : jacobian r = (storedJacobian r : ℝ) := by
  fin_cases r
  · simpa [jacobian, vertices, storedJacobian] using
      (show |((edgeMatrix row21).det : ℝ)| =
        ((((8 : ℕ).factorial : ℚ) * P2Winner9Row21RawVertexData.physicalVolume : ℚ) : ℝ) from
        by exact_mod_cast row21_abs_det_volume)
  · simpa [jacobian, vertices, storedJacobian] using
      (show |((edgeMatrix row22).det : ℝ)| =
        ((((8 : ℕ).factorial : ℚ) * row22Volume : ℚ) : ℝ) from
        by exact_mod_cast row22_abs_det_volume)

private theorem actual_jensen_arithmetic : ∀ r : Fin 2,
    ((data r).jensenNum : ℚ) / (data r).jensenDen =
      4 * (storedJacobian r / (gapScale r : ℚ) *
        ((gapTotal (data r).gaps : ℚ) / ((9 : ℕ).factorial : ℚ))) /
          ∏ j : Fin 10, means r j := by
  decide +kernel

/-- The exact Jensen prefactor equals the physical gap mass divided by
the product of the ten stored (and measured) first moments, with factor four. -/
theorem actual_Jensen_factor (r : Fin 2) :
    ((data r).jensenNum : ℝ) / (data r).jensenDen =
      4 * gapMass r / ∏ j : Fin 10, (means r j : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (actual_jensen_arithmetic r)
  push_cast at h
  rw [gapMass_typed, actualGapMass_eq, jacobian_eq_stored]
  exact h

end

end ImbalancedChen.P2Winner9SelectedPhysicalMeans
