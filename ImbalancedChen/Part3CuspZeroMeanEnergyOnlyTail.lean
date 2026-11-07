import ImbalancedChen.Part3CuspCylinderMeasure
import ImbalancedChen.Part3CuspHorizontalDerivativeParseval
import Mathlib.MeasureTheory.Integral.Prod

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The existing source already proves the sharp horizontal Fourier gap by
actual derivative coefficients, integration by parts and AddCircle Parseval.
This new source discharges the analytic inputs for smooth periodic functions
and proves the genuinely stronger strict cusp-tail endpoint: finite horizontal
Dirichlet energy ALONE implies hyperbolic tail mass is finite, with the sharp
Y^{-2}/(4π²) estimate. No tail-mass integrability is assumed.
Everything is on the literal local period-one cusp cylinder. No global
quotient compactness, Rellich theorem or discrete Maass spectrum is asserted.
-/

namespace ImbalancedChen.Part3.CuspZeroMeanEnergyOnlyTail20261025a

noncomputable section

open Set MeasureTheory
open ImbalancedChen.Part3.CuspCylinderMeasure20261024z
open P3CuspHorizontalDerivativeParsevalSourceOnly

local instance periodOne_pos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

local instance positiveHeight_locallyCompact : LocallyCompactSpace PositiveHeight :=
  isOpen_Ioi.locallyCompactSpace

local instance positiveHeightVolume_finiteOnCompacts :
    IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)

local instance positiveHeightVolume_locallyFinite :
    IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance

local instance positiveHeightVolume_sigmaFinite : SigmaFinite (volume : Measure PositiveHeight) :=
  inferInstance

private theorem smooth_derivative_continuous (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) :
    Continuous (deriv f) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  exact hf1.continuous_deriv_one

/-- Actual Fourier derivative coefficient for a genuine smooth periodic
function; interval integrability follows from smoothness. -/
theorem smooth_period_one_derivative_coefficient (f : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hperiod : Function.Periodic f 1) (n : ℤ) :
    AddCircle.fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (deriv f) n =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        AddCircle.fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n := by
  exact derivative_fourier_coefficient f (deriv f)
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt)
    (by simpa only [zero_add] using hperiod 0)
    ((smooth_derivative_continuous f hf).intervalIntegrable 0 1) n

theorem smooth_period_one_poincare (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hperiod : Function.Periodic f 1) (hmean : (∫ x in (0 : ℝ)..1, f x) = 0) :
    (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) ≤
      (4 * Real.pi ^ 2)⁻¹ * (∫ x in (0 : ℝ)..1, ‖deriv f x‖ ^ 2) := by
  have hdcont := smooth_derivative_continuous f hf
  have hfL2 : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hf.continuous.aestronglyMeasurable).mpr
      (hf.continuous.norm.pow 2).integrableOn_Ioc
  have hdL2 : MemLp (deriv f) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hdcont.aestronglyMeasurable).mpr
      (hdcont.norm.pow 2).integrableOn_Ioc
  exact period_one_poincare_sharp_constant f (deriv f)
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt)
    (by simpa only [zero_add] using hperiod 0)
    (hdcont.intervalIntegrable 0 1) hfL2 hdL2 hmean

def strictHeightTail (Y : ℝ) : Set PositiveHeight := {y | Y < (y : ℝ)}

def strictCylinderTail (Y : ℝ) : Set CuspCylinder := univ ×ˢ strictHeightTail Y

theorem strictHeightTail_measurable (Y : ℝ) : MeasurableSet (strictHeightTail Y) :=
  (isOpen_lt continuous_const continuous_subtype_val).measurableSet

theorem strictCylinderTail_measurable (Y : ℝ) : MeasurableSet (strictCylinderTail Y) :=
  MeasurableSet.univ.prod (strictHeightTail_measurable Y)

private theorem weightedTail_product (Y : ℝ) :
    (AddCircle.haarAddCircle (T := (1 : ℝ))).prod
      (heightMeasure.restrict (strictHeightTail Y)) =
      cylinderMeasure.restrict (strictCylinderTail Y) := by
  simpa only [Measure.restrict_univ, cylinderMeasure, strictCylinderTail] using
    (Measure.prod_restrict (μ := AddCircle.haarAddCircle (T := (1 : ℝ)))
      (ν := heightMeasure) univ (strictHeightTail Y))

private theorem rawTail_product (Y : ℝ) :
    (AddCircle.haarAddCircle (T := (1 : ℝ))).prod
      ((volume : Measure PositiveHeight).restrict (strictHeightTail Y)) =
      ((AddCircle.haarAddCircle (T := (1 : ℝ))).prod
        (volume : Measure PositiveHeight)).restrict (strictCylinderTail Y) := by
  simpa only [Measure.restrict_univ, strictCylinderTail] using
    (Measure.prod_restrict (μ := AddCircle.haarAddCircle (T := (1 : ℝ)))
      (ν := (volume : Measure PositiveHeight)) univ (strictHeightTail Y))

private theorem weightedTail_density (Y : ℝ) :
    heightMeasure.restrict (strictHeightTail Y) =
      ((volume : Measure PositiveHeight).restrict (strictHeightTail Y)).withDensity
        (fun y => (heightDensity y : ℝ≥0∞)) :=
  restrict_withDensity (μ := (volume : Measure PositiveHeight)) (strictHeightTail_measurable Y) _

private theorem circle_energy_interval (u : UnitAddCircle → ℂ) :
    (∫ x : UnitAddCircle, ‖u x‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∫ t in (0 : ℝ)..1, ‖u (t : UnitAddCircle)‖ ^ 2 := by
  calc
    _ = ∫ t in Ico (0 : ℝ) 1, ‖u (t : UnitAddCircle)‖ ^ 2 := circle_integral_eq_Ico _
    _ = ∫ t in Ioc (0 : ℝ) 1, ‖u (t : UnitAddCircle)‖ ^ 2 := integral_Ico_eq_integral_Ioc
    _ = _ := (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm

private theorem actual_circle_slice_poincare (F D : CuspCylinder → ℂ)
    (hF : Continuous F) (hD : Continuous D) (y : PositiveHeight)
    (hderiv : ∀ t ∈ [[(0 : ℝ), 1]],
      HasDerivAt (fun s : ℝ => F ((s : UnitAddCircle), y)) (D ((t : UnitAddCircle), y)) t)
    (hmean : (∫ x : UnitAddCircle, F (x, y) ∂AddCircle.haarAddCircle) = 0) :
    (4 * Real.pi ^ 2) * (∫ x : UnitAddCircle, ‖F (x, y)‖ ^ 2 ∂AddCircle.haarAddCircle) ≤
      ∫ x : UnitAddCircle, ‖D (x, y)‖ ^ 2 ∂AddCircle.haarAddCircle := by
  let u : ℝ → ℂ := fun t => F ((t : UnitAddCircle), y)
  let d : ℝ → ℂ := fun t => D ((t : UnitAddCircle), y)
  have hu : Continuous u := by fun_prop
  have hd : Continuous d := by fun_prop
  have huL2 : MemLp u 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr (hu.norm.pow 2).integrableOn_Ioc
  have hdL2 : MemLp d 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mpr (hd.norm.pow 2).integrableOn_Ioc
  have hperiod : u 1 = u 0 := by
    change F (((1 : ℝ) : UnitAddCircle), y) = F (((0 : ℝ) : UnitAddCircle), y)
    congr 1
    simpa using (AddCircle.coe_add_period (1 : ℝ) (0 : ℝ))
  have hmeanI : (∫ t in (0 : ℝ)..1, u t) = 0 := by
    change (∫ t in (0 : ℝ)..1, F ((t : UnitAddCircle), y)) = 0
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hmeanV : (∫ x : UnitAddCircle, F (x, y)) = 0 := by
      simpa only [circleHaar_eq_volume] using hmean
    simpa only [zero_add] using
      (AddCircle.integral_preimage 1 0 (fun x : UnitAddCircle => F (x, y))).trans hmeanV
  have hp := period_one_poincare u d hderiv hperiod (hd.intervalIntegrable 0 1) huL2 hdL2 hmeanI
  rw [← circle_energy_interval (fun x => F (x, y)),
    ← circle_energy_interval (fun x => D (x, y))] at hp
  exact hp

/-- Finite physical horizontal energy alone supplies finite hyperbolic
tail mass and its sharp period-one cusp bound. The left density is
literally dy/y²; the right Dirichlet measure is literally dx dy. -/
theorem strict_cusp_tail_mass_of_horizontal_energy
    (Y : ℝ) (hY : 0 < Y) (F D : CuspCylinder → ℂ)
    (hF : Continuous F) (hD : Continuous D)
    (hderiv : ∀ y : PositiveHeight, Y < (y : ℝ) → ∀ t ∈ [[(0 : ℝ), 1]],
      HasDerivAt (fun s : ℝ => F ((s : UnitAddCircle), y)) (D ((t : UnitAddCircle), y)) t)
    (hmean : ∀ y : PositiveHeight, Y < (y : ℝ) →
      (∫ x : UnitAddCircle, F (x, y) ∂AddCircle.haarAddCircle) = 0)
    (hDtail : Integrable (fun z : CuspCylinder => ‖D z‖ ^ 2)
      (((AddCircle.haarAddCircle (T := (1 : ℝ))).prod
        (volume : Measure PositiveHeight)).restrict (strictCylinderTail Y))) :
    Integrable (fun z : CuspCylinder => ‖F z‖ ^ 2)
      (cylinderMeasure.restrict (strictCylinderTail Y)) ∧
    (∫ z in strictCylinderTail Y, ‖F z‖ ^ 2 ∂cylinderMeasure) ≤
      (4 * Real.pi ^ 2 * Y ^ 2)⁻¹ *
        (∫ z in strictCylinderTail Y, ‖D z‖ ^ 2
          ∂((AddCircle.haarAddCircle (T := (1 : ℝ))).prod (volume : Measure PositiveHeight))) := by
  let A : PositiveHeight → ℝ := fun y => ∫ x : UnitAddCircle, ‖F (x, y)‖ ^ 2 ∂AddCircle.haarAddCircle
  let B : PositiveHeight → ℝ := fun y => ∫ x : UnitAddCircle, ‖D (x, y)‖ ^ 2 ∂AddCircle.haarAddCircle
  let C : ℝ := (4 * Real.pi ^ 2 * Y ^ 2)⁻¹
  have hDprod : Integrable (fun z : CuspCylinder => ‖D z‖ ^ 2)
      ((AddCircle.haarAddCircle (T := (1 : ℝ))).prod
        ((volume : Measure PositiveHeight).restrict (strictHeightTail Y))) := by
    rwa [rawTail_product]
  have hBint : Integrable B ((volume : Measure PositiveHeight).restrict (strictHeightTail Y)) :=
    hDprod.integral_prod_right
  have hAmeas : StronglyMeasurable A := (hF.norm.pow 2).stronglyMeasurable.integral_prod_left'
  have hAnonneg (y : PositiveHeight) : 0 ≤ A y := integral_nonneg (fun x => sq_nonneg (‖F (x, y)‖))
  have hpoint (y : PositiveHeight) (hy : y ∈ strictHeightTail Y) :
      (heightDensity y : ℝ) * A y ≤ C * B y := by
    have hp := actual_circle_slice_poincare F D hF hD y (hderiv y hy) (hmean y hy)
    have hrec : 1 / (y : ℝ) ≤ 1 / Y := one_div_le_one_div_of_le hY (le_of_lt hy)
    have hdensity : (heightDensity y : ℝ) ≤ (1 / Y) ^ 2 := by
      rw [heightDensity_coe]
      exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hrec
    have hc : 0 < 4 * Real.pi ^ 2 * Y ^ 2 := by positivity
    calc
      _ ≤ (1 / Y) ^ 2 * A y := mul_le_mul_of_nonneg_right hdensity (hAnonneg y)
      _ = C * ((4 * Real.pi ^ 2) * A y) := by
        dsimp [C]
        field_simp [ne_of_gt hc, ne_of_gt hY] <;> ring
      _ ≤ C * B y := mul_le_mul_of_nonneg_left hp (by dsimp [C]; positivity)
  have hAE : ∀ᵐ y ∂((volume : Measure PositiveHeight).restrict (strictHeightTail Y)),
      (heightDensity y : ℝ) * A y ≤ C * B y :=
    (ae_restrict_mem (strictHeightTail_measurable Y)).mono hpoint
  have hdcont : Continuous (fun y : PositiveHeight => (heightDensity y : ℝ)) :=
    continuous_subtype_val.comp heightDensity_continuous
  have hweighted : Integrable (fun y : PositiveHeight => (heightDensity y : ℝ) * A y)
      ((volume : Measure PositiveHeight).restrict (strictHeightTail Y)) :=
    (hBint.const_mul C).mono_nonneg
      (hdcont.stronglyMeasurable.mul hAmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => mul_nonneg (heightDensity y).property (hAnonneg y)) hAE
  have hAint : Integrable A (heightMeasure.restrict (strictHeightTail Y)) := by
    rw [weightedTail_density]
    apply (integrable_withDensity_iff_integrable_smul heightDensity_continuous.measurable).mpr
    simpa only [NNReal.smul_def, smul_eq_mul] using hweighted
  have hFprod : Integrable (fun z : CuspCylinder => ‖F z‖ ^ 2)
      ((AddCircle.haarAddCircle (T := (1 : ℝ))).prod
        (heightMeasure.restrict (strictHeightTail Y))) := by
    apply (integrable_prod_iff' (hF.norm.pow 2).aestronglyMeasurable).mpr
    constructor
    · apply Filter.Eventually.of_forall
      intro y
      have hc : Continuous (fun x : UnitAddCircle => ‖F (x, y)‖ ^ 2) := by fun_prop
      simpa only [integrableOn_univ] using
        (hc.continuousOn.integrableOn_compact isCompact_univ :
          IntegrableOn (fun x : UnitAddCircle => ‖F (x, y)‖ ^ 2) univ AddCircle.haarAddCircle)
    · simpa only [Real.norm_eq_abs, abs_pow, abs_norm, A] using hAint
  have hFtail : Integrable (fun z : CuspCylinder => ‖F z‖ ^ 2)
      (cylinderMeasure.restrict (strictCylinderTail Y)) := by
    rwa [weightedTail_product] at hFprod
  refine ⟨hFtail, ?_⟩
  have hle := integral_mono_ae hweighted (hBint.const_mul C) hAE
  have hFfub : (∫ z in strictCylinderTail Y, ‖F z‖ ^ 2 ∂cylinderMeasure) =
      ∫ y : PositiveHeight, A y ∂heightMeasure.restrict (strictHeightTail Y) := by
    rw [← weightedTail_product]
    exact integral_prod_symm _ hFprod
  have hDfub : (∫ z in strictCylinderTail Y, ‖D z‖ ^ 2
      ∂((AddCircle.haarAddCircle (T := (1 : ℝ))).prod (volume : Measure PositiveHeight))) =
      ∫ y : PositiveHeight, B y ∂(volume : Measure PositiveHeight).restrict (strictHeightTail Y) := by
    rw [← rawTail_product]
    exact integral_prod_symm _ hDprod
  rw [hFfub, weightedTail_density]
  rw [integral_withDensity_eq_integral_smul heightDensity_continuous.measurable]
  change (∫ y : PositiveHeight, (heightDensity y : ℝ) * A y
    ∂(volume : Measure PositiveHeight).restrict (strictHeightTail Y)) ≤ _
  calc
    _ ≤ ∫ y : PositiveHeight, C * B y
        ∂(volume : Measure PositiveHeight).restrict (strictHeightTail Y) := hle
    _ = C * ∫ y : PositiveHeight, B y
        ∂(volume : Measure PositiveHeight).restrict (strictHeightTail Y) := integral_const_mul _ _
    _ = _ := congrArg (fun t : ℝ => C * t) hDfub.symm

end

end ImbalancedChen.Part3.CuspZeroMeanEnergyOnlyTail20261025a
