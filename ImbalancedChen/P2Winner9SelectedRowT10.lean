import ImbalancedChen.P2Winner9ActualRowProbability
import ImbalancedChen.P2Winner9SelectedPhysicalMoments
import ImbalancedChen.P2Winner9T10TailJensen
import ImbalancedChen.P2Winner9TaylorCorrection

/-! The exact T10 Jensen correction on the two actual physical row measures. -/

namespace ImbalancedChen.P2Winner9SelectedRowT10

noncomputable section

open MeasureTheory
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9SelectedPhysicalMoments
open ImbalancedChen.P2Winner9ActualRowProbability
open ImbalancedChen.P2Winner9PowerMoment
open ImbalancedChen.P2Winner9TaylorCorrection
open ImbalancedChen.P2Winner9T10TailJensen

theorem U_typed (r : Fin 2) : U r = ((data r).U : ℝ) / (data r).L := by
  fin_cases r <;> simp [U, upper, data, Row21.upper, Row22.upper]

theorem integral_Y_pow (r : Fin 2) (k : ℕ) :
    (∫ z, (Y r z)^k ∂ν r) = actualPowerExpectation (data r) k := by
  rw [weighted_integral]
  exact physicalPowerMean_eq r k

private theorem exact_mean_arithmetic : ∀ r : Fin 2,
    (meanNumerator (data r) : ℚ) / D (data r) = 1 - 1 / upper r := by
  decide +kernel

theorem integral_Y (r : Fin 2) : (∫ z, Y r z ∂ν r) = 1 - 1 / U r := by
  have h := integral_Y_pow r 1
  simp only [pow_one, actualPowerExpectation_one] at h
  rw [h]
  have hq := congrArg (fun q : ℚ => (q : ℝ)) (exact_mean_arithmetic r)
  simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_sub, Rat.cast_one, U] using hq

theorem actual_T10_lower (r : Fin 2) :
    1 + (value (t10 (data r)) : ℝ) ≤ ∫ z, invP10 r z ∂ν r := by
  have hY := weighted_integrable r (Y_continuous r).continuousOn
  have hf := weighted_integrable r (fY_continuousOn r)
  have hp (k : ℕ) (_hk : k ∈ Finset.range 11) : Integrable (fun z => (Y r z)^k) (ν r) :=
    weighted_integrable r ((Y_continuous r).pow k).continuousOn
  have hgap := probability_T10_gap (ν r) (Y r) (q_lt_one r)
    ((ν_support r).mono (fun z hz => Y_mem r hz)) hY hf hp
  have hU := U_pos r
  have hscale : 0 ≤ 1 / (U r)^10 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hgap hscale
  have hI : (∫ z, invP10 r z ∂ν r) =
      (1 / (U r)^10) * ∫ z, 1 / (1 - Y r z)^10 ∂ν r := by
    rw [← integral_const_mul]
    exact integral_congr_ae ((ν_support r).mono (fun z hz => invP10_scaled r hz))
  have hunit : (1 / (U r)^10) * (1 / (1 - ∫ z, Y r z ∂ν r)^10) = 1 := by
    rw [integral_Y]
    field_simp [hU.ne']
    ring
  rw [← hI, mul_add, hunit] at hscaled
  simp_rw [integral_Y_pow] at hscaled
  have hmean := integral_Y_pow r 1
  simp only [pow_one] at hmean
  rw [hmean, U_typed] at hscaled
  rwa [actual_T10_identity_range]

end

end ImbalancedChen.P2Winner9SelectedRowT10
