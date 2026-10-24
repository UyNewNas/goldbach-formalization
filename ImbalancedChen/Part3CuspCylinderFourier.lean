import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24; uncompiled.

This is transverse Fourier Plancherel on the literal cusp cylinder: the
unit AddCircle with normalized Haar measure times positive height with
Lebesgue density y⁻². It combines Mathlib's *all-integer* AddCircle Parseval
with Tonelli. It is not spectral Plancherel for Maass or Eisenstein forms.

The measure definitions below are literal copies of the independent
Part3CuspCylinderMeasure source-only candidate. No unbuilt project module is
imported. They are to be deduplicated at actual intake.
-/

noncomputable section

namespace P3CuspCylinderFourierSourceOnly

open Set MeasureTheory
open scoped ENNReal NNReal

local instance periodOne_pos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

abbrev PositiveHeight := Ioi (0 : ℝ)
abbrev CuspCylinder := UnitAddCircle × PositiveHeight

def heightDensity (y : PositiveHeight) : ℝ≥0 :=
  (1 / NNReal.mk (y : ℝ) y.property.le) ^ 2

def heightMeasure : Measure PositiveHeight :=
  volume.withDensity (fun y => (heightDensity y : ℝ≥0∞))

def cylinderMeasure : Measure CuspCylinder :=
  (AddCircle.haarAddCircle (T := (1 : ℝ))).prod heightMeasure

local instance positiveHeight_locallyCompact : LocallyCompactSpace PositiveHeight :=
  isOpen_Ioi.locallyCompactSpace

local instance positiveHeightVolume_finiteOnCompacts :
    IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) := by
  exact IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)

local instance positiveHeightVolume_locallyFinite :
    IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance

local instance heightMeasure_sigmaFinite : SigmaFinite heightMeasure := by
  unfold heightMeasure
  infer_instance

abbrev CircleL2 := Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))

def coefficientEnergy (F : CuspCylinder → ℂ) (y : PositiveHeight) (n : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖AddCircle.fourierCoeff (fun x : UnitAddCircle => F (x, y)) n‖ ^ 2)

def cylinderEnergy (F : CuspCylinder → ℂ) (p : CuspCylinder) : ℝ≥0∞ :=
  ENNReal.ofReal (‖F p‖ ^ 2)

theorem cylinderEnergy_measurable (F : CuspCylinder → ℂ) (hF : Measurable F) :
    Measurable (cylinderEnergy F) := by
  exact (hF.norm.pow_const 2).ennreal_ofReal

theorem coefficientEnergy_measurable (F : CuspCylinder → ℂ)
    (hF : Measurable F) (n : ℤ) :
    Measurable (fun y : PositiveHeight => coefficientEnergy F y n) := by
  have hweighted : StronglyMeasurable (fun p : CuspCylinder =>
      (AddCircle.fourier (-n) p.1 : ℂ) • F p) := by
    have hm : Measurable (fun p : CuspCylinder =>
        (AddCircle.fourier (-n) p.1 : ℂ) • F p) := by fun_prop
    exact hm.stronglyMeasurable
  have hcoeff : Measurable (fun y : PositiveHeight =>
      AddCircle.fourierCoeff (fun x : UnitAddCircle => F (x, y)) n) := by
    change Measurable (fun y : PositiveHeight =>
      ∫ x : UnitAddCircle, AddCircle.fourier (-n) x • F (x, y)
        ∂AddCircle.haarAddCircle)
    exact hweighted.integral_prod_left'.measurable
  exact (hcoeff.norm.pow_const 2).ennreal_ofReal

/-- Parseval on one genuinely square-integrable height slice, rewritten in
nonnegative extended-real form so Tonelli needs no extra summability. -/
private theorem slice_plancherel (F : CuspCylinder → ℂ) (hF : Measurable F)
    (y : PositiveHeight)
    (hy : Integrable (fun x : UnitAddCircle => ‖F (x, y)‖ ^ 2)
      AddCircle.haarAddCircle) :
    (∑' n : ℤ, coefficientEnergy F y n) =
      ∫⁻ x : UnitAddCircle, cylinderEnergy F (x, y)
        ∂AddCircle.haarAddCircle := by
  let fy : UnitAddCircle → ℂ := fun x => F (x, y)
  have hfy_meas : AEStronglyMeasurable fy AddCircle.haarAddCircle :=
    (hF.comp measurable_prodMk_right).aestronglyMeasurable
  have hfy_L2 : MemLp fy 2 AddCircle.haarAddCircle :=
    (memLp_two_iff_integrable_sq_norm hfy_meas).2 hy
  have hcoeff (n : ℤ) :
      AddCircle.fourierCoeff (hfy_L2.toLp fy) n = AddCircle.fourierCoeff fy n := by
    exact congrFun (AddCircle.fourierCoeff_congr_ae hfy_L2.coeFn_toLp) n
  have hint :
      (∫ x : UnitAddCircle, ‖(hfy_L2.toLp fy) x‖ ^ 2
        ∂AddCircle.haarAddCircle) =
        ∫ x : UnitAddCircle, ‖fy x‖ ^ 2 ∂AddCircle.haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [hfy_L2.coeFn_toLp] with x hx
    rw [hx]
  have hparse : HasSum (fun n : ℤ => ‖AddCircle.fourierCoeff fy n‖ ^ 2)
      (∫ x : UnitAddCircle, ‖fy x‖ ^ 2 ∂AddCircle.haarAddCircle) := by
    simpa only [hcoeff, hint] using
      (AddCircle.hasSum_sq_fourierCoeff (hfy_L2.toLp fy))
  calc
    (∑' n : ℤ, coefficientEnergy F y n) =
        ENNReal.ofReal (∑' n : ℤ, ‖AddCircle.fourierCoeff fy n‖ ^ 2) := by
          exact (ENNReal.ofReal_tsum_of_nonneg
            (fun n : ℤ => sq_nonneg _) hparse.summable).symm
    _ = ENNReal.ofReal
          (∫ x : UnitAddCircle, ‖fy x‖ ^ 2 ∂AddCircle.haarAddCircle) := by
          rw [hparse.tsum_eq]
    _ = ∫⁻ x : UnitAddCircle, cylinderEnergy F (x, y)
          ∂AddCircle.haarAddCircle := by
          exact ofReal_integral_eq_lintegral_ofReal hy
            (Filter.Eventually.of_forall (fun x => sq_nonneg (‖fy x‖)))

/-- Integration in height of all transverse modes equals the cylinder
energy. This is the nonnegative Tonelli formulation. -/
theorem cylinder_plancherel_lintegral (F : CuspCylinder → ℂ)
    (hF : Measurable F) (hL2 : MemLp F 2 cylinderMeasure) :
    (∫⁻ y : PositiveHeight, ∑' n : ℤ, coefficientEnergy F y n
      ∂heightMeasure) =
      ∫⁻ p : CuspCylinder, cylinderEnergy F p ∂cylinderMeasure := by
  have hsq : Integrable (fun p : CuspCylinder => ‖F p‖ ^ 2) cylinderMeasure :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hL2
  have hslice : ∀ᵐ y : PositiveHeight ∂heightMeasure,
      Integrable (fun x : UnitAddCircle => ‖F (x, y)‖ ^ 2)
        AddCircle.haarAddCircle := hsq.prod_right_ae
  calc
    (∫⁻ y : PositiveHeight, ∑' n : ℤ, coefficientEnergy F y n
        ∂heightMeasure) =
        ∫⁻ y : PositiveHeight,
          ∫⁻ x : UnitAddCircle, cylinderEnergy F (x, y)
            ∂AddCircle.haarAddCircle ∂heightMeasure := by
          apply lintegral_congr_ae
          filter_upwards [hslice] with y hy
          exact slice_plancherel F hF y hy
    _ = ∫⁻ p : CuspCylinder, cylinderEnergy F p ∂cylinderMeasure := by
          exact (lintegral_prod_symm' (cylinderEnergy F)
            (cylinderEnergy_measurable F hF)).symm

/-- Tonelli also exchanges the entire integer sum and height integral;
no chosen finite set of modes occurs. -/
theorem cylinder_lintegral_tsum (F : CuspCylinder → ℂ) (hF : Measurable F) :
    (∫⁻ y : PositiveHeight, ∑' n : ℤ, coefficientEnergy F y n
      ∂heightMeasure) =
      ∑' n : ℤ, ∫⁻ y : PositiveHeight, coefficientEnergy F y n
        ∂heightMeasure := by
  exact lintegral_tsum (fun n => (coefficientEnergy_measurable F hF n).aemeasurable)

theorem cylinder_plancherel_tsum_lintegral (F : CuspCylinder → ℂ)
    (hF : Measurable F) (hL2 : MemLp F 2 cylinderMeasure) :
    (∑' n : ℤ, ∫⁻ y : PositiveHeight, coefficientEnergy F y n
      ∂heightMeasure) =
      ∫⁻ p : CuspCylinder, cylinderEnergy F p ∂cylinderMeasure := by
  rw [← cylinder_lintegral_tsum F hF]
  exact cylinder_plancherel_lintegral F hF hL2

end P3CuspCylinderFourierSourceOnly
