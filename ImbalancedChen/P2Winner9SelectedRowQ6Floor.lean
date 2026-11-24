import ImbalancedChen.P2Winner9MixedPowerSource
import ImbalancedChen.P2Winner9PhysicalQ6Probability
import ImbalancedChen.P2Winner9Row21Q6Arithmetic
import ImbalancedChen.P2Winner9Row22Rounding
import ImbalancedChen.P2Winner9SelectedRowT10

/-! The original directed T10 + Q6 floors for the two physical Winner9 rows. -/

namespace ImbalancedChen.P2Winner9SelectedRowQ6Floor

noncomputable section

open MeasureTheory
open P2Winner9BarycentricMixedDegreeOne
open P2Winner9CurvatureFullExactAssembly (SimplexData value t10)
open P2Winner9CurvatureExactMomentFloor (q96)
open P2Winner9MixedDegreeSixExactAssembly
open P2Winner9MixedPowerMoment
open P2Winner9MixedPowerSource
open P2Winner9SelectedRowEdgeGeometry
open P2Winner9SelectedRowRealJacobian
open P2Winner9SelectedRowIntegerScales (real_vertex_arrays)
open P2Winner9SelectedRowAnalyticCaps
open P2Winner9SelectedPhysicalMeans
open P2Winner9SelectedPhysicalMoments
open P2Winner9ActualRowProbability
open P2Winner9PhysicalConstantCurvature
open P2Winner9PhysicalQ6Probability
open P2Winner9SelectedRowT10
open P2Winner9PhysicalAffineTransfer
open P2Winner9PhysicalVertexInterpolation

/-- All powers of the physical Y and all ten signed physical deviations use
the same gap-weighted canonical simplex measure. -/
theorem moment_probability (r : Fin 2) (j : Fin 10) (k : ℕ) :
    (∫ z, (Y r z)^k * (B r j z)^2 ∂ν r) = actualMixedPowerExpectation (data r) j k := by
  have h := real_vertex_arrays (vertices r) (means r) (upper r) (data r)
    (gapScale r) (row_vertex_normalization r)
  rw [weighted_integral, normalized_weighted_transport]
  simp only [Y, U, B, physicalY_vertexMap, h.2.1, physicalDeviation_vertexMap, h.2.2 j,
    actualMixedPowerExpectation, actualMixedPowerNumerator, canonicalSupport, mul_assoc]

theorem C6_expectation_eq_source (r : Fin 2) :
    (∫ z, C6 r z ∂ν r) = (value (q6 (data r)) : ℝ) := by
  rw [C6_expectation, actual_q6_eq]
  simp only [mixedMoment, moment_probability, V_typed, U_typed]

theorem physical_Q6_enclosure (r : Fin 2) :
    (((data r).jensenNum : ℝ) / (data r).jensenDen) *
      (1 + (value (total (data r)) : ℝ)) ≤
      ∫ z in sourceSupport (vertices r), physicalUpperIntegrand z := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) (physical_density_Q6_lower r)
  rw [total, P2Winner9CurvatureFullExactAssembly.add_value, Rat.cast_add,
    ← C6_expectation_eq_source, ← add_assoc]
  exact add_le_add (actual_T10_lower r) le_rfl

def originalQ6Floor (r : Fin 2) : ℕ :=
  if r = 0 then P2Winner9Row21Q6Arithmetic.observedMixedRawQ96
  else P2Winner9Row22Rounding.observedMixedRawQ96

private theorem original_Q6_arithmetic (r : Fin 2) :
    (originalQ6Floor r : ℚ) / q96 ≤
      ((data r).jensenNum : ℚ) / (data r).jensenDen * (1 + value (total (data r))) := by
  fin_cases r
  · exact P2Winner9Row21Q6Arithmetic.row21_raw_Q6_arithmetic_lower
  · exact P2Winner9Row22Rounding.row22_raw_Q6_arithmetic_lower

theorem original_Q6_floor_actual_integral (r : Fin 2) :
    (originalQ6Floor r : ℝ) / (q96 : ℝ) ≤
      ∫ z in sourceSupport (vertices r), physicalUpperIntegrand z := by
  apply le_trans _ (physical_Q6_enclosure r)
  have hr : ((↑((originalQ6Floor r : ℚ) / q96) : ℝ)) ≤
      (↑(((data r).jensenNum : ℚ) / (data r).jensenDen *
        (1 + value (total (data r)))) : ℝ) := Rat.cast_le.mpr (original_Q6_arithmetic r)
  simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_mul, Rat.cast_add, Rat.cast_one] using hr

theorem row21_original_Q96_integral_lower :
    (33553775924834770601 : ℝ) / 79228162514264337593543950336 ≤
      ∫ z in sourceSupport row21, physicalUpperIntegrand z :=
  original_Q6_floor_actual_integral 0

theorem row22_original_Q96_integral_lower :
    (6463231997558714529 : ℝ) / 79228162514264337593543950336 ≤
      ∫ z in sourceSupport row22, physicalUpperIntegrand z :=
  original_Q6_floor_actual_integral 1

end

end ImbalancedChen.P2Winner9SelectedRowQ6Floor
