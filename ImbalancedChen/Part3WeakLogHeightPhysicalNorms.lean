import ImbalancedChen.Part3WeakLogHeightCoordinate

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Literal physical dy/y^2 mass and ordinary dy gradient energy become radial
L2 mass and the exact log-coordinate shear norm. These are arbitrary-function
nonnegative-integral identities, then specialized to the derivative of an
actual weak representative. No quarter inequality, boundary deletion, or
smooth graph density is assumed.
-/

namespace ImbalancedChen.Part3.WeakLogHeightPhysicalNorms20261026b
noncomputable section
open MeasureTheory Set Filter
open CuspCylinderMeasure20261024z CuspModePhysicalCoreForm20261026a
open WeightedHeightLogMeasure20261026a WeightedHeightNativeUnitary20261026a
open ZeroModeWeakOpenHalfLine20261026b WeakLogHeightCoordinate20261026b
attribute [local instance] Measure.Subtype.measureSpace

private def tailHeightFunction (Y : ℝ) (f : ℝ → ℂ) (y : PositiveHeight) : ℂ :=
  if Y < (y : ℝ) then f y else 0

/-- The native subtype norm is evaluated against the literal physical
inverse-square density, with the tail restriction kept explicitly. -/
theorem tailHeightFunction_lintegral {Y : ℝ} (hY : 0 < Y) (f : ℝ → ℂ) :
    (∫⁻ y : PositiveHeight, ENNReal.ofReal (‖tailHeightFunction Y f y‖ ^ 2) ∂heightMeasure) =
      ∫⁻ y in Ioi Y, ENNReal.ofReal (‖f y‖ ^ 2 / y ^ 2) := by
  unfold heightMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _
    heightDensity_continuous.measurable.coe_nnreal_ennreal
    (Eventually.of_forall (fun _ => ENNReal.coe_lt_top))]
  let q : ℝ → ℝ≥0∞ := (Ioi Y).indicator (fun y => ENNReal.ofReal (‖f y‖ ^ 2 / y ^ 2))
  calc
    _ = ∫⁻ y : PositiveHeight, q y := by
      apply lintegral_congr
      intro y
      by_cases hy : Y < (y : ℝ)
      · simp only [tailHeightFunction, if_pos hy, q, indicator_of_mem hy]
        rw [show (heightDensity y : ℝ≥0∞) = ENNReal.ofReal ((1 / (y : ℝ)) ^ 2) by
          rw [← heightDensity_coe]; simp]
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        field_simp [y.property.ne'] <;> ring
      · simp [tailHeightFunction, hy, q, indicator_of_notMem hy]
    _ = ∫⁻ y in Ioi (0 : ℝ), q y := lintegral_subtype_comap measurableSet_Ioi q
    _ = ∫⁻ y in Ioi Y, ENNReal.ofReal (‖f y‖ ^ 2 / y ^ 2) := by
      dsimp [q]
      rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
        inter_eq_left.mpr (show Ioi Y ⊆ Ioi (0 : ℝ) from fun y hy => hY.trans hy)]

theorem weakLogValue_lintegral_physical_mass {a : ℝ} (ha : 0 < a) (R : ℝ) (f : ℝ → ℂ) :
    (∫⁻ r in Ioi R, ENNReal.ofReal (‖weakLogValue a f r‖ ^ 2)) =
      ∫⁻ y in Ioi (heightChart a R), ENNReal.ofReal (‖f y‖ ^ 2 / y ^ 2) := by
  have h := heightToRadialFunction_lintegral_sq a ha
    (tailHeightFunction (heightChart a R) f)
  have hrad :
      (∫⁻ r : ℝ, ENNReal.ofReal
        (‖heightToRadialFunction a ha (tailHeightFunction (heightChart a R) f) r‖ ^ 2)) =
        ∫⁻ r in Ioi R, ENNReal.ofReal (‖weakLogValue a f r‖ ^ 2) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro r
    by_cases hr : R < r
    · simp [heightToRadialFunction, tailHeightFunction, scaledHeightEquiv_coe,
        heightChart, div_lt_div_iff_of_pos_right ha, Real.exp_lt_exp, hr, weakLogValue]
    · simp [heightToRadialFunction, tailHeightFunction, scaledHeightEquiv_coe,
        heightChart, div_lt_div_iff_of_pos_right ha, Real.exp_lt_exp, hr]
  rw [hrad, tailHeightFunction_lintegral (heightChart_pos ha R)] at h
  exact h

theorem weakLogShear_lintegral_physical_energy {a : ℝ} (ha : 0 < a) (R : ℝ) (g : ℝ → ℂ) :
    (∫⁻ r in Ioi R, ENNReal.ofReal (‖weakLogShear a g r‖ ^ 2)) =
      ∫⁻ y in Ioi (heightChart a R), ENNReal.ofReal (‖g y‖ ^ 2) := by
  have h := weakLogValue_lintegral_physical_mass ha R (fun y => (y : ℂ) * g y)
  have heq : weakLogValue a (fun y => (y : ℂ) * g y) = weakLogShear a g := by
    funext r
    simp only [weakLogValue, weakLogShear, Complex.ofReal_mul]
    ring
  rw [heq] at h
  refine h.trans ?_
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos : 0 < y := (heightChart_pos ha R).trans hy
  congr 1
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos, mul_pow]
  field_simp [hypos.ne'] <;> ring

/-- The actual derivative of the transformed local-AC representative has
exactly the ordinary physical dy gradient energy after the half shear. -/
theorem weakLogValue_derivative_shear_energy {a : ℝ} (ha : 0 < a) (R : ℝ)
    {f g : ℝ → ℂ} (u : OpenHalfLineSobolevRepresentative (heightChart a R) f g) :
    (∫⁻ r in Ioi R, ENNReal.ofReal
      (‖deriv (weakLogValue a u.function) r + (1 / 2 : ℂ) * weakLogValue a u.function r‖ ^ 2)) =
      ∫⁻ y in Ioi (heightChart a R), ENNReal.ofReal (‖g y‖ ^ 2) := by
  rw [← weakLogShear_lintegral_physical_energy ha R g]
  apply lintegral_congr_ae
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [weakLogValue_hasDerivAt_ae ha u] with r hr hrR
  rw [(hr hrR).deriv]
  simp only [sub_add_cancel]

end
end ImbalancedChen.Part3.WeakLogHeightPhysicalNorms20261026b
