import ImbalancedChen.P2Winner9SelectedPhysicalMeans

/-! Source-only P1 compatibility supplement.
The four declarations below are copied verbatim from the accepted P2
SelectedPhysicalMeans source. Keep the existing original owner and all its
public declarations; this module adds only its missing Jensen interface.
The combined P1 import environment has not yet been compiled. -/

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
