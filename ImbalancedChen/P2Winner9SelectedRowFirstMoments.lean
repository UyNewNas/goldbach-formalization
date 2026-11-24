import ImbalancedChen.P2Winner9SelectedPhysicalMoments
import ImbalancedChen.P2Winner9ActualRowProbability
import ImbalancedChen.P2Winner9SelectedRawMeans
import ImbalancedChen.P2Winner9CanonicalFirstMoment

/-! First moments on the two original selected physical rows. -/

namespace ImbalancedChen.P2Winner9SelectedRowFirstMoments

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P2Winner9SelectedRowAnalyticCaps (vertices data means)
open P2Winner9SelectedRowRealJacobian (sourceSupport realVertices)
open P2Winner9SelectedRowIntegerScales (rawGap rawFactor rawP rawFactor_cast rawP_cast)
open P2Winner9SelectedPhysicalMeans (gapMass gapScale row_vertex_normalization)
open P2Winner9SelectedPhysicalMoments (normalized_weighted_transport)
open P2Winner9PhysicalAffineTransfer (Ambient canonicalSupport physicalGap physicalFactor physicalP)
open P2Winner9PhysicalVertexInterpolation (vertexMap physicalFactor_vertexMap physicalP_vertexMap)
open P2Winner9BarycentricMixedDegreeOne (affine gapVertices)
open P2Winner9CurvatureExactMomentFloor (gapTotal)
open P2Winner9CanonicalFirstMoment (actualGapWeightedAffine_eq)
open P2Winner9SelectedRawMeans (gapIntegral weightedAffineIntegral)

private theorem raw_affine_ratio (r : Fin 2) (f : Fin 9 → ℚ) :
    weightedAffineIntegral (vertices r) f / gapIntegral (vertices r) =
      ((gapTotal (data r).gaps : ℚ) * (∑ i, f i) +
        ∑ i, ((data r).gaps i : ℚ) * f i) / (10 * (gapTotal (data r).gaps : ℚ)) := by
  have hg (i : Fin 9) : P2Winner9Row22Arithmetic.rawGap (vertices r) i =
      ((data r).gaps i : ℚ) / (gapScale r : ℚ) := (row_vertex_normalization r).2 i |>.1
  have hscale : (gapScale r : ℚ) ≠ 0 := by
    exact_mod_cast (row_vertex_normalization r).1.ne'
  have hG : (gapTotal (data r).gaps : ℚ) ≠ 0 := by
    exact_mod_cast (data r).gapsPos.ne'
  unfold weightedAffineIntegral gapIntegral
  simp_rw [hg]
  have hsum : (∑ i : Fin 9, ((data r).gaps i : ℚ) / (gapScale r : ℚ)) =
      (gapTotal (data r).gaps : ℚ) / (gapScale r : ℚ) := by
    rw [← Finset.sum_div, gapTotal, Nat.cast_sum]
  have hweighted :
      (∑ i : Fin 9, ((data r).gaps i : ℚ) / (gapScale r : ℚ) * f i) =
        (∑ i : Fin 9, ((data r).gaps i : ℚ) * f i) / (gapScale r : ℚ) := by
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
  rw [hsum, hweighted]
  norm_num [Nat.factorial_succ]
  field_simp [hG, hscale]
  ring

/-- Transport a function whose pullback has the given rational affine values. -/
private theorem weighted_chart_of_rational_values (r : Fin 2) (F : Ambient → ℝ)
    (f : Fin 9 → ℚ)
    (h : ∀ x, F (vertexMap (realVertices (vertices r)) x) = affine (fun i => (f i : ℝ)) x) :
    (∫ z in sourceSupport (vertices r), physicalGap z * F z) / gapMass r =
      ((weightedAffineIntegral (vertices r) f / gapIntegral (vertices r) : ℚ) : ℝ) := by
  rw [normalized_weighted_transport]
  simp_rw [h]
  rw [canonicalSupport, actualGapWeightedAffine_eq]
  have hr := congrArg (fun q : ℚ => (q : ℝ)) (raw_affine_ratio r f)
  push_cast at hr ⊢
  simpa only [gapVertices] using hr.symm

private theorem raw_gap_pos (r : Fin 2) : 0 < gapIntegral (vertices r) := by
  fin_cases r
  · exact P2Winner9SelectedRawMeans.row21_exact_affine_moments.1
  · exact P2Winner9SelectedRawMeans.row22_exact_affine_moments.1

private theorem raw_factor_identity (r : Fin 2) (j : Fin 10) :
    weightedAffineIntegral (vertices r) (fun i => rawFactor (vertices r) i j) =
      means r j * gapIntegral (vertices r) := by
  fin_cases r
  · exact P2Winner9SelectedRawMeans.row21_exact_affine_moments.2.2 j
  · exact P2Winner9SelectedRawMeans.row22_exact_affine_moments.2.2 j

private theorem raw_p_identity (r : Fin 2) :
    weightedAffineIntegral (vertices r) (rawP (vertices r) (means r)) =
      gapIntegral (vertices r) := by
  fin_cases r
  · exact P2Winner9SelectedRawMeans.row21_exact_affine_moments.2.1
  · exact P2Winner9SelectedRawMeans.row22_exact_affine_moments.2.1

/-- Every literal factor mean is the weighted first moment on its physical row. -/
theorem actual_weighted_factor_mean (r : Fin 2) (j : Fin 10) :
    (∫ z in sourceSupport (vertices r), physicalGap z * physicalFactor j z) /
      gapMass r = (means r j : ℝ) := by
  have h (x : Ambient) :
      physicalFactor j (vertexMap (realVertices (vertices r)) x) =
        affine (fun i => (rawFactor (vertices r) i j : ℝ)) x := by
    simp only [physicalFactor_vertexMap, rawFactor_cast]
  rw [weighted_chart_of_rational_values r _ _ h, raw_factor_identity,
    mul_div_cancel_right₀ _ (raw_gap_pos r).ne']

/-- The common affine function has mean one under the original gap weight. -/
theorem actual_weighted_P_mean (r : Fin 2) :
    (∫ z in sourceSupport (vertices r),
      physicalGap z * physicalP (fun j => (means r j : ℝ)) z) / gapMass r = 1 := by
  have h (x : Ambient) :
      physicalP (fun j => (means r j : ℝ)) (vertexMap (realVertices (vertices r)) x) =
        affine (fun i => (rawP (vertices r) (means r) i : ℝ)) x := by
    simp only [physicalP_vertexMap, rawP_cast]
  rw [weighted_chart_of_rational_values r _ _ h, raw_p_identity,
    div_self (raw_gap_pos r).ne', Rat.cast_one]

open P2Winner9ActualRowProbability (ν P weighted_integral)

theorem probability_factor_mean (r : Fin 2) (j : Fin 10) :
    (∫ z, physicalFactor j z ∂ν r) = (means r j : ℝ) := by
  rw [weighted_integral, actual_weighted_factor_mean]

theorem probability_P_mean (r : Fin 2) : (∫ z, P r z ∂ν r) = 1 := by
  rw [weighted_integral]
  exact actual_weighted_P_mean r

end

end ImbalancedChen.P2Winner9SelectedRowFirstMoments
