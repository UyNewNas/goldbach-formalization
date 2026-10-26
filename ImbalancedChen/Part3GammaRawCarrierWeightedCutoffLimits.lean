import ImbalancedChen.Part3Gamma0WeightedCutoffDefectLimit

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Weighted cutoff convergence directly on H for an arbitrary measure and
arbitrary integrable nonnegative density. No scalar quotient descent of
the density is assumed. This is needed for raw weak-gradient densities
before a quotient Sobolev model has been proved. Actual cutoff geometry
supplies pointwise eventual exactness and the uniform derivative bound.
-/

namespace ImbalancedChen.Part3.GammaRawCarrierWeightedCutoffLimits20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a
open ActualModularSmoothCuspCutoff20261025a ActualModularSmoothCutoffL2Tail20261025a
open ActualModularCutoffGradient20261025a ActualModularCutoffEnergyBudget20261025a
open Gamma0WeightedCutoffDefectLimit20261026a

theorem global_cutoff_eventually_one (z : UpperHalfPlane) :
    ∀ᶠ n in atTop, globalCutoff (cutoffHeight n) z = 1 := by
  filter_upwards [cutoffHeight_tendsto.eventually
    (eventually_gt_atTop (max z.im (1/z.im)))] with n hn
  exact globalCutoff_one_above_height _ (cutoffHeight_pos n) z hn

theorem global_cutoff_energy_eventually_zero (z : UpperHalfPlane) :
    ∀ᶠ n in atTop, cutoffEnergyH (cutoffHeight n) z = 0 := by
  filter_upwards [cutoffHeight_tendsto.eventually
    (eventually_gt_atTop (max z.im (1/z.im)))] with n hn
  exact cutoffEnergyH_zero_above_height _ (cutoffHeight_gt_one n) z hn

private theorem cutoff_measurable (n : ℕ) : Measurable (globalCutoff (cutoffHeight n)) := by
  have h := (quotientCutoff_measurable 1 (cutoffHeight n) (cutoffHeight_pos n)).comp
    (orbitProjection_measurable 1)
  exact h

/-- Multiplication of a raw finite-energy density by chi_n approaches
the identity in the genuine squared L2 error. The density need not be
invariant or arise from an existing form vector. -/
theorem raw_weighted_cutoff_defect_tendsto (μ : Measure UpperHalfPlane)
    (w : UpperHalfPlane → ℝ) (hw : Integrable w μ) (hw0 : ∀ᵐ z ∂μ, 0 ≤ w z) :
    Tendsto (fun n : ℕ => ∫ z, (1-globalCutoff (cutoffHeight n) z)^2 * w z ∂μ)
      atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun z => (1-globalCutoff (cutoffHeight n) z)^2*w z) μ :=
    ((measurable_const.sub (cutoff_measurable n)).pow_const 2).aestronglyMeasurable.mul
      hw.aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ z ∂μ,
      ‖(1-globalCutoff (cutoffHeight n) z)^2*w z‖ ≤ w z := by
    filter_upwards [hw0] with z hz
    have hc := globalCutoff_bounds (cutoffHeight n) (cutoffHeight_gt_one n).le z
    have hs : (1-globalCutoff (cutoffHeight n) z)^2 ≤ 1 := by
      nlinarith [mul_nonneg hc.1 (sub_nonneg.mpr hc.2)]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) hz)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hz
  have hl : ∀ᵐ z ∂μ, Tendsto (fun n : ℕ =>
      (1-globalCutoff (cutoffHeight n) z)^2*w z) atTop (𝓝 (0 : ℝ)) :=
    Eventually.of_forall (fun z => tendsto_const_nhds.congr'
      ((global_cutoff_eventually_one z).mono (fun n hn => by simp [hn])))
  simpa using tendsto_integral_of_dominated_convergence w hm hw hb hl

/-- The raw derivative error vanishes for EVERY integrable density on
the actual carrier, without replacing a coordinate field by a scalar
quotient field. The bound is pointwise, not a total-cutoff-energy bound. -/
theorem raw_weighted_cutoff_gradient_error_tendsto (μ : Measure UpperHalfPlane)
    (w : UpperHalfPlane → ℝ) (hw : Integrable w μ) (hw0 : ∀ᵐ z ∂μ, 0 ≤ w z) :
    Tendsto (fun n : ℕ => ∫ z, cutoffEnergyH (cutoffHeight n) z*w z ∂μ)
      atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun z => cutoffEnergyH (cutoffHeight n) z*w z) μ :=
    (cutoffEnergyH_continuous (cutoffHeight n) (cutoffHeight_pos n)).aestronglyMeasurable.mul
      hw.aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ z ∂μ,
      ‖cutoffEnergyH (cutoffHeight n) z*w z‖ ≤ cutoffEnergyConstant*w z := by
    filter_upwards [hw0] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg
      (mul_nonneg (cutoffEnergyH_nonneg (cutoffHeight n) z) hz)]
    exact mul_le_mul_of_nonneg_right
      (cutoffEnergyH_uniform (cutoffHeight n) (cutoffHeight_gt_one n) z) hz
  have hl : ∀ᵐ z ∂μ, Tendsto (fun n : ℕ =>
      cutoffEnergyH (cutoffHeight n) z*w z) atTop (𝓝 (0 : ℝ)) :=
    Eventually.of_forall (fun z => tendsto_const_nhds.congr'
      ((global_cutoff_energy_eventually_zero z).mono (fun n hn => by simp [hn])))
  simpa using tendsto_integral_of_dominated_convergence
    (fun z => cutoffEnergyConstant*w z) hm (hw.const_mul cutoffEnergyConstant) hb hl

end
end ImbalancedChen.Part3.GammaRawCarrierWeightedCutoffLimits20261026b
