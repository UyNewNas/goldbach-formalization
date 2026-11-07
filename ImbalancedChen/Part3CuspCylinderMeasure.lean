import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY, 2026-10-24.
The cusp cylinder is (R/Z) times the positive-height subtype. The circle
measure is the actual normalized Haar AddCircle.haarAddCircle at period 1.
The height measure is the actual subtype Lebesgue measure with density
(1/y)^2, matching the reciprocal-square density in UpperHalfPlane.volume_def.
This is a concrete cusp-coordinate measure, not an automorphic spectral
measure, spectral expansion, or Plancherel theorem.
-/

namespace ImbalancedChen.Part3.CuspCylinderMeasure20261024z
noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

local instance periodOne_pos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

abbrev PositiveHeight := Ioi (0 : ℝ)
abbrev CuspCylinder := AddCircle (1 : ℝ) × PositiveHeight

/-- Literal NNReal reciprocal-square density, as in UpperHalfPlane.volume_def. -/
def heightDensity (y : PositiveHeight) : ℝ≥0 :=
  (1 / NNReal.mk (y : ℝ) y.property.le) ^ 2

theorem heightDensity_coe (y : PositiveHeight) :
    (heightDensity y : ℝ) = (1 / (y : ℝ)) ^ 2 := by
  simp [heightDensity]

theorem heightDensity_continuous : Continuous heightDensity := by
  unfold heightDensity
  apply Continuous.pow
  apply Continuous.div₀ continuous_const
  · exact continuous_subtype_val.subtype_mk (fun y => y.property.le)
  · intro y
    exact NNReal.ne_iff.mp y.property.ne'

theorem heightDensity_pos (y : PositiveHeight) : 0 < heightDensity y := by
  unfold heightDensity
  exact sq_pos_of_pos (div_pos zero_lt_one y.property)

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

instance heightMeasure_locallyFinite : IsLocallyFiniteMeasure heightMeasure := by
  unfold heightMeasure
  exact IsLocallyFiniteMeasure.withDensity_coe heightDensity_continuous

instance heightMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts heightMeasure :=
  inferInstance

instance heightMeasure_sigmaFinite : SigmaFinite heightMeasure := inferInstance

instance cylinderMeasure_sigmaFinite : SigmaFinite cylinderMeasure := by
  unfold cylinderMeasure
  infer_instance

instance cylinderMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts cylinderMeasure := by
  unfold cylinderMeasure
  infer_instance

/-- Compact height intervals remain compact in the open positive-height subtype. -/
theorem positiveHeight_Icc_isCompact (a b : PositiveHeight) :
    IsCompact (Icc a b) := by
  apply Subtype.isCompact_iff.mpr
  have himage : ((↑) : PositiveHeight → ℝ) '' Icc a b = Icc (a : ℝ) (b : ℝ) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, a.property.trans_le hy.1⟩, hy, rfl⟩
  rw [himage]
  exact isCompact_Icc

def cylinderBand (a b : PositiveHeight) : Set CuspCylinder :=
  univ ×ˢ Icc a b

theorem cylinderBand_isCompact (a b : PositiveHeight) : IsCompact (cylinderBand a b) := by
  exact isCompact_univ.prod (positiveHeight_Icc_isCompact a b)

theorem cylinderBand_measure_lt_top (a b : PositiveHeight) :
    cylinderMeasure (cylinderBand a b) < ∞ := by
  exact (cylinderBand_isCompact a b).measure_lt_top

/-- Explicit real-coordinate finite band, including the degenerate a=b case. -/
theorem cylinder_realBand_measure_lt_top {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    cylinderMeasure {z : CuspCylinder | a ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ b} < ∞ := by
  have hb : 0 < b := ha.trans_le hab
  have he : {z : CuspCylinder | a ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ b} =
      cylinderBand (⟨a, ha⟩ : PositiveHeight) (⟨b, hb⟩ : PositiveHeight) := by
    ext z
    change (a ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ b) ↔
      True ∧ (a ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ b)
    simp only [true_and]
  rw [he]
  exact cylinderBand_measure_lt_top _ _

theorem positiveHeight_volume_univ : (volume : Measure PositiveHeight) univ = ∞ := by
  rw [Measure.Subtype.volume_univ measurableSet_Ioi.nullMeasurableSet]
  simp

theorem heightMeasure_ne_zero : heightMeasure ≠ 0 := by
  have hf : AEMeasurable (fun y : PositiveHeight => (heightDensity y : ℝ≥0∞))
      (volume : Measure PositiveHeight) :=
    heightDensity_continuous.measurable.coe_nnreal_ennreal.aemeasurable
  have hpos : ∀ᵐ y ∂(volume : Measure PositiveHeight),
      (heightDensity y : ℝ≥0∞) ≠ 0 := by
    apply Filter.Eventually.of_forall
    intro y
    exact_mod_cast (heightDensity_pos y).ne'
  have hac : (volume : Measure PositiveHeight) ≪ heightMeasure :=
    withDensity_absolutelyContinuous' hf hpos
  intro hz
  have hzero : heightMeasure univ = 0 := by rw [hz]; simp
  have hbase : (volume : Measure PositiveHeight) univ = 0 := hac hzero
  rw [positiveHeight_volume_univ] at hbase
  exact top_ne_zero hbase

theorem cylinderMeasure_univ : cylinderMeasure univ = heightMeasure univ := by
  unfold cylinderMeasure
  rw [← univ_prod_univ, Measure.prod_prod, measure_univ, one_mul]

theorem cylinderMeasure_ne_zero : cylinderMeasure ≠ 0 := by
  intro hz
  have hu : cylinderMeasure univ = 0 := by rw [hz]; simp
  rw [cylinderMeasure_univ] at hu
  exact heightMeasure_ne_zero (measure_univ_eq_zero.mp hu)

/-- At period one normalized Haar agrees exactly with the circle's standard volume. -/
theorem circleHaar_eq_volume :
    (AddCircle.haarAddCircle (T := (1 : ℝ))) = (volume : Measure (AddCircle (1 : ℝ))) := by
  simpa only [ENNReal.ofReal_one, one_smul] using
    (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm

/-- Actual real representatives on Ico 0 1; endpoint changes are volume-null. -/
theorem circle_integral_eq_Ico (f : AddCircle (1 : ℝ) → ℝ) :
    (∫ x, f x ∂AddCircle.haarAddCircle) =
      ∫ x in Ico (0 : ℝ) 1, f (x : AddCircle (1 : ℝ)) := by
  rw [circleHaar_eq_volume]
  calc
    (∫ x : AddCircle (1 : ℝ), f x) =
        ∫ x in Ioc (0 : ℝ) 1, f (x : AddCircle (1 : ℝ)) := by
      simpa only [zero_add] using (AddCircle.integral_preimage 1 0 f).symm
    _ = ∫ x in Ico (0 : ℝ) 1, f (x : AddCircle (1 : ℝ)) :=
      integral_Ico_eq_integral_Ioc.symm

/-- The height integral is exactly dy/y^2 on the positive subtype. -/
theorem height_integral_eq_weighted_volume (g : PositiveHeight → ℝ) :
    (∫ y, g y ∂heightMeasure) =
      ∫ y : PositiveHeight, (1 / (y : ℝ)) ^ 2 * g y := by
  have h := integral_withDensity_eq_integral_smul heightDensity_continuous.measurable g
  simpa only [heightMeasure, NNReal.smul_def, smul_eq_mul, heightDensity_coe] using h

/-- Tonelli's norm-square formula, with infinite energy allowed. -/
theorem cylinder_lintegral_norm_sq (F : CuspCylinder → ℂ) (hF : Measurable F) :
    (∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2) ∂cylinderMeasure) =
      ∫⁻ y, ∫⁻ x, ENNReal.ofReal (‖F (x, y)‖ ^ 2)
        ∂AddCircle.haarAddCircle ∂heightMeasure := by
  exact lintegral_prod_symm _ (hF.norm.pow_const 2).ennreal_ofReal.aemeasurable

/-- Fubini's norm-square formula when the genuine full energy is integrable. -/
theorem cylinder_integral_norm_sq (F : CuspCylinder → ℂ)
    (hF : Integrable (fun z => ‖F z‖ ^ 2) cylinderMeasure) :
    (∫ z, ‖F z‖ ^ 2 ∂cylinderMeasure) =
      ∫ y, ∫ x, ‖F (x, y)‖ ^ 2 ∂AddCircle.haarAddCircle ∂heightMeasure := by
  exact integral_prod_symm _ hF

theorem cylinder_integral_norm_sq_representatives (F : CuspCylinder → ℂ)
    (hF : Integrable (fun z => ‖F z‖ ^ 2) cylinderMeasure) :
    (∫ z, ‖F z‖ ^ 2 ∂cylinderMeasure) =
      ∫ y, ∫ x in Ico (0 : ℝ) 1,
        ‖F ((x : AddCircle (1 : ℝ)), y)‖ ^ 2 ∂volume ∂heightMeasure := by
  rw [cylinder_integral_norm_sq F hF]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => circle_integral_eq_Ico
    (fun x => ‖F (x, y)‖ ^ 2))

/-- Explicit dx dy/y^2 formula with period-one real horizontal representatives. -/
theorem cylinder_integral_norm_sq_weighted_representatives (F : CuspCylinder → ℂ)
    (hF : Integrable (fun z => ‖F z‖ ^ 2) cylinderMeasure) :
    (∫ z, ‖F z‖ ^ 2 ∂cylinderMeasure) =
      ∫ y : PositiveHeight, (1 / (y : ℝ)) ^ 2 *
        (∫ x in Ico (0 : ℝ) 1, ‖F ((x : AddCircle (1 : ℝ)), y)‖ ^ 2) := by
  rw [cylinder_integral_norm_sq_representatives F hF,
    height_integral_eq_weighted_volume]

end
end ImbalancedChen.Part3.CuspCylinderMeasure20261024z

