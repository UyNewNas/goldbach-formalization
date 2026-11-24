import ImbalancedChen.P2Winner9ActualRowProbability
import ImbalancedChen.P2Winner9PhysicalConstantCurvature

/-! The physical density dominates the common and constant-curvature expectations on each row. -/

namespace ImbalancedChen.P2Winner9PhysicalCurvatureProbability

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P2Winner9SelectedRowRealJacobian
open P2Winner9SelectedRowAnalyticCaps
open P2Winner9SelectedPhysicalMeans
open P2Winner9ActualRowProbability
open P2Winner9PhysicalAffineTransfer
open P2Winner9PhysicalConstantCurvature

theorem density_probability_normalization (r : Fin 2) :
    (∫ z in sourceSupport (vertices r), physicalUpperIntegrand z) =
      (((data r).jensenNum : ℝ) / (data r).jensenDen) * (∫ z, prodInv r z ∂ν r) := by
  rw [actual_Jensen_factor, weighted_integral, weighted_prodInv_integral]
  have hμ := (meanProduct_pos r).ne'
  have hm := (gapMass_pos r).ne'
  change _ = (4 * gapMass r / meanProduct r) *
    ((meanProduct r / 4) * _ / gapMass r)
  field_simp [hμ, hm]

theorem constantCorrection_expectation (r : Fin 2) :
    (∫ z, constantCorrection r z ∂ν r) =
      ∑ j : Fin 10, (∫ z, (B r j z)^2 ∂ν r) /
        (2 * (V r j)^2 * (upper r : ℝ)^10) := by
  have hterm (j : Fin 10) (_ : j ∈ (Finset.univ : Finset (Fin 10))) :
      Integrable (fun z => (B r j z)^2 / (2 * (V r j)^2)) (ν r) :=
    weighted_integrable r (((B_continuous r j).pow 2).div_const _).continuousOn
  unfold constantCorrection
  rw [integral_div, integral_finsetSum Finset.univ hterm, Finset.sum_div]
  simp_rw [integral_div, div_div]

theorem physical_curvature_expectation (r : Fin 2) :
    (∫ z, invP10 r z ∂ν r) + (∫ z, constantCorrection r z ∂ν r) ≤
      ∫ z, prodInv r z ∂ν r := by
  have hi := weighted_integrable r (invP10_continuousOn r)
  have hc := weighted_integrable r (constantCorrection_continuous r).continuousOn
  have hp := weighted_integrable r (prodInv_continuousOn r)
  have hrow : ∀ᵐ z ∂ν r, invP10 r z + constantCorrection r z ≤ prodInv r z :=
    (ν_support r).mono (fun _ hz => pointwise_constant_curvature r hz)
  have h := integral_mono_ae (hi.add hc) hp hrow
  simpa only [Pi.add_apply, integral_add hi hc] using h

theorem physical_density_curvature_lower (r : Fin 2) :
    (((data r).jensenNum : ℝ) / (data r).jensenDen) *
      ((∫ z, invP10 r z ∂ν r) + (∫ z, constantCorrection r z ∂ν r)) ≤
      ∫ z in sourceSupport (vertices r), physicalUpperIntegrand z := by
  rw [density_probability_normalization]
  exact mul_le_mul_of_nonneg_left (physical_curvature_expectation r) (by positivity)

end

end ImbalancedChen.P2Winner9PhysicalCurvatureProbability
