import ImbalancedChen.Part3CuspCylinderMeasure
import ImbalancedChen.Part3ImaginaryOrderKExplicitMajorant
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY, 2026-10-24.
The actual Fourier--Bessel mode on the period-one cylinder is truncated to
positive heights y>=a>0. The actual K bound |K_{2it}(q)|<=2/q supplies a finite
L2 budget. No full-y integrability, spectral basis, orthogonal completeness,
automorphic coefficient normalization, or Plancherel theorem is asserted.
-/

namespace ImbalancedChen.Part3.CuspCylinderBesselMode20261024z
noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open CuspCylinderMeasure20261024z
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKExplicitMajorantSourceOnly

local instance periodOne_pos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

def frequencyScale (n : ℤ) : ℝ := 2 * Real.pi * |(n : ℝ)|

theorem frequencyScale_pos {n : ℤ} (hn : n ≠ 0) : 0 < frequencyScale n := by
  have hcast : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr hcast)

def heightTail (a : ℝ) : Set PositiveHeight :=
  ((↑) : PositiveHeight → ℝ) ⁻¹' Ici a

def tailSet (a : ℝ) : Set CuspCylinder := univ ×ˢ heightTail a

def tailMeasure (a : ℝ) : Measure CuspCylinder := cylinderMeasure.restrict (tailSet a)

theorem heightTail_measurable (a : ℝ) : MeasurableSet (heightTail a) := by
  exact measurable_subtype_coe measurableSet_Ici

theorem tailSet_measurable (a : ℝ) : MeasurableSet (tailSet a) := by
  exact MeasurableSet.univ.prod (heightTail_measurable a)

/-- Reciprocal-square decay makes the actual height tail finite. -/
theorem heightMeasure_tail_lt_top {a : ℝ} (ha : 0 < a) :
    heightMeasure (heightTail a) < ∞ := by
  have hp : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ici a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha).congr_set_ae
      Ioi_ae_eq_Ici.symm
  have hr : IntegrableOn (fun y : ℝ => (1 / y) ^ 2) (Ici a) := by
    simpa only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, one_div, inv_pow] using hp
  have hsub : Ici a ⊆ Set.range ((↑) : PositiveHeight → ℝ) := by
    intro y hy
    exact ⟨⟨y, ha.trans_le hy⟩, rfl⟩
  have hi : IntegrableOn (fun y : PositiveHeight => (heightDensity y : ℝ))
      (heightTail a) (volume : Measure PositiveHeight) := by
    have h := ((MeasurableEmbedding.subtype_coe measurableSet_Ioi).integrableOn_iff_comap
      hsub).mp hr
    simpa only [Function.comp_def, heightDensity_coe] using h
  have hn : 0 ≤ᵐ[(volume : Measure PositiveHeight).restrict (heightTail a)]
      (fun y => (heightDensity y : ℝ)) :=
    Filter.Eventually.of_forall (fun y => (heightDensity y).coe_nonneg)
  have hfinite := (hasFiniteIntegral_iff_ofReal hn).mp hi.hasFiniteIntegral
  rw [heightMeasure, withDensity_apply _ (heightTail_measurable a)]
  simpa using hfinite

theorem tailSet_mass (a : ℝ) :
    cylinderMeasure (tailSet a) = heightMeasure (heightTail a) := by
  unfold cylinderMeasure tailSet
  rw [Measure.prod_prod, measure_univ, one_mul]

theorem tailMeasure_univ (a : ℝ) :
    tailMeasure a univ = heightMeasure (heightTail a) := by
  unfold tailMeasure
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, tailSet_mass]

theorem tailMeasure_isFinite {a : ℝ} (ha : 0 < a) : IsFiniteMeasure (tailMeasure a) := by
  apply isFiniteMeasure_restrict.mpr
  rw [tailSet_mass]
  exact (heightMeasure_tail_lt_top ha).ne

theorem tailMeasure_eq_prod (a : ℝ) :
    tailMeasure a = (AddCircle.haarAddCircle (T := (1 : ℝ))).prod
      (heightMeasure.restrict (heightTail a)) := by
  unfold tailMeasure cylinderMeasure tailSet
  rw [← Measure.prod_restrict, Measure.restrict_univ]

/-- The requested literal mode, with real-order K and period-one horizontal phase. -/
def cuspMode (n : ℤ) (t : ℝ) (z : CuspCylinder) : ℂ :=
  AddCircle.fourier n z.1 * (Real.sqrt (z.2 : ℝ) : ℂ) *
    (imaginaryOrderK t (frequencyScale n * (z.2 : ℝ)) : ℂ)

/-- A continuous extension used only to prove measurability on the actual tail. -/
def cuspModeExtension (n : ℤ) (hn : n ≠ 0) (t a : ℝ) (ha : 0 < a)
    (z : CuspCylinder) : ℂ :=
  AddCircle.fourier n z.1 * (Real.sqrt (z.2 : ℝ) : ℂ) *
    ((frequencyScale n * (z.2 : ℝ) : ℝ) : ℂ) *
    extendedKKernel (frequencyScale n * a) (mul_pos (frequencyScale_pos hn) ha) t
      (frequencyScale n * (z.2 : ℝ))

theorem cuspModeExtension_continuous (n : ℤ) (hn : n ≠ 0) (t a : ℝ)
    (ha : 0 < a) : Continuous (cuspModeExtension n hn t a ha) := by
  have hfourier : Continuous (fun z : CuspCylinder => AddCircle.fourier n z.1) :=
    (AddCircle.fourier n).continuous.comp continuous_fst
  have hsqrt : Continuous (fun z : CuspCylinder => (Real.sqrt (z.2 : ℝ) : ℂ)) := by
    fun_prop
  have harg : Continuous (fun z : CuspCylinder => frequencyScale n * (z.2 : ℝ)) := by
    fun_prop
  have hcomplex : Continuous (fun z : CuspCylinder =>
      ((frequencyScale n * (z.2 : ℝ) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp harg
  have hK := (extendedKKernel (frequencyScale n * a)
    (mul_pos (frequencyScale_pos hn) ha) t).continuous.comp harg
  exact ((hfourier.mul hsqrt).mul hcomplex).mul hK

theorem cuspModeExtension_eq (n : ℤ) (hn : n ≠ 0) (t a : ℝ) (ha : 0 < a)
    {z : CuspCylinder} (hz : z ∈ tailSet a) :
    cuspModeExtension n hn t a ha z = cuspMode n t z := by
  have hy : a ≤ (z.2 : ℝ) := hz.2
  have hc := frequencyScale_pos hn
  have hq : ((frequencyScale n * (z.2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos hc z.2.property).ne'
  unfold cuspModeExtension cuspMode
  rw [extendedKKernel_eq _ _ _ _ (mul_le_mul_of_nonneg_left hy hc.le)]
  have hcancel : ((frequencyScale n * (z.2 : ℝ) : ℝ) : ℂ) *
      ((imaginaryOrderK t (frequencyScale n * (z.2 : ℝ)) : ℂ) /
        ((frequencyScale n * (z.2 : ℝ) : ℝ) : ℂ)) =
      (imaginaryOrderK t (frequencyScale n * (z.2 : ℝ)) : ℂ) := by
    field_simp [hq]
  calc
    _ = (AddCircle.fourier n z.1 * (Real.sqrt (z.2 : ℝ) : ℂ)) *
        (((frequencyScale n * (z.2 : ℝ) : ℝ) : ℂ) *
          ((imaginaryOrderK t (frequencyScale n * (z.2 : ℝ)) : ℂ) /
            ((frequencyScale n * (z.2 : ℝ) : ℝ) : ℂ))) := by ring
    _ = _ := by rw [hcancel]

/-- Measurability of the actual function restricted to the actual tail subtype. -/
theorem cuspMode_tail_measurable (n : ℤ) (hn : n ≠ 0) (t a : ℝ) (ha : 0 < a) :
    Measurable (fun z : tailSet a => cuspMode n t z) := by
  have h : (fun z : tailSet a => cuspMode n t z) =
      (fun z : tailSet a => cuspModeExtension n hn t a ha z) := by
    funext z
    exact (cuspModeExtension_eq n hn t a ha z.property).symm
  rw [h]
  exact (cuspModeExtension_continuous n hn t a ha).measurable.comp measurable_subtype_coe

theorem cuspMode_aestronglyMeasurable (n : ℤ) (hn : n ≠ 0) (t a : ℝ) (ha : 0 < a) :
    AEStronglyMeasurable (cuspMode n t) (tailMeasure a) := by
  apply (cuspModeExtension_continuous n hn t a ha).aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem (tailSet_measurable a)] with z hz
  exact cuspModeExtension_eq n hn t a ha hz

/-- Unit modulus of the Haar Fourier character removes the horizontal variable exactly. -/
theorem cuspMode_norm_sq (n : ℤ) (t : ℝ) (z : CuspCylinder) :
    ‖cuspMode n t z‖ ^ 2 =
      (z.2 : ℝ) * imaginaryOrderK t (frequencyScale n * (z.2 : ℝ)) ^ 2 := by
  have hf : ‖AddCircle.fourier n z.1‖ = 1 := by
    rw [AddCircle.fourier_apply]
    exact Circle.norm_coe _
  unfold cuspMode
  rw [norm_mul, norm_mul, hf, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt z.2.property.le]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The actual absolute K bound gives a uniform norm-square bound on y>=a. -/
theorem cuspMode_norm_sq_le (n : ℤ) (hn : n ≠ 0) (t a : ℝ) (ha : 0 < a)
    {z : CuspCylinder} (hz : z ∈ tailSet a) :
    ‖cuspMode n t z‖ ^ 2 ≤ 4 / (frequencyScale n ^ 2 * a) := by
  have hc := frequencyScale_pos hn
  have hy : a ≤ (z.2 : ℝ) := hz.2
  have hq := mul_pos hc z.2.property
  have hk := imaginaryOrderK_abs_le t hq
  have hk2 : imaginaryOrderK t (frequencyScale n * (z.2 : ℝ)) ^ 2 ≤
      (2 / (frequencyScale n * (z.2 : ℝ))) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hk)
      (add_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hq.le)
        (abs_nonneg (imaginaryOrderK t (frequencyScale n * (z.2 : ℝ)))))
    nlinarith [sq_abs (imaginaryOrderK t (frequencyScale n * (z.2 : ℝ)))]
  calc
    ‖cuspMode n t z‖ ^ 2 =
        (z.2 : ℝ) * imaginaryOrderK t (frequencyScale n * (z.2 : ℝ)) ^ 2 :=
      cuspMode_norm_sq n t z
    _ ≤ (z.2 : ℝ) * (2 / (frequencyScale n * (z.2 : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_left hk2 z.2.property.le
    _ = 4 / (frequencyScale n ^ 2 * (z.2 : ℝ)) := by
      field_simp [hc.ne', z.2.property.ne']
      ring
    _ ≤ 4 / (frequencyScale n ^ 2 * a) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos (sq_pos_of_pos hc) ha)
        (mul_le_mul_of_nonneg_left hy (sq_nonneg _))

theorem cuspMode_norm_sq_integrable (n : ℤ) (hn : n ≠ 0) (t a : ℝ) (ha : 0 < a) :
    Integrable (fun z => ‖cuspMode n t z‖ ^ 2) (tailMeasure a) := by
  letI : IsFiniteMeasure (tailMeasure a) := tailMeasure_isFinite ha
  have hmeas : AEStronglyMeasurable (fun z => ‖cuspMode n t z‖ ^ 2) (tailMeasure a) := by
    apply ((cuspModeExtension_continuous n hn t a ha).norm.pow 2).aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem (tailSet_measurable a)] with z hz
    rw [cuspModeExtension_eq n hn t a ha hz]
  refine ⟨hmeas, HasFiniteIntegral.of_bounded ?_⟩
  filter_upwards [ae_restrict_mem (tailSet_measurable a)] with z hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using
    cuspMode_norm_sq_le n hn t a ha hz

theorem cuspMode_memLp_two (n : ℤ) (hn : n ≠ 0) (t a : ℝ) (ha : 0 < a) :
    MemLp (cuspMode n t) 2 (tailMeasure a) := by
  exact (memLp_two_iff_integrable_sq_norm
    (cuspMode_aestronglyMeasurable n hn t a ha)).mpr
      (cuspMode_norm_sq_integrable n hn t a ha)

/-- Finite budget using the actual, proved finite height-tail mass. -/
def cuspL2Budget (n : ℤ) (a : ℝ) : ℝ :=
  (4 / (frequencyScale n ^ 2 * a)) * (heightMeasure (heightTail a)).toReal

theorem cuspMode_energy_le_budget (n : ℤ) (hn : n ≠ 0) (t a : ℝ) (ha : 0 < a) :
    (∫ z, ‖cuspMode n t z‖ ^ 2 ∂tailMeasure a) ≤ cuspL2Budget n a := by
  letI : IsFiniteMeasure (tailMeasure a) := tailMeasure_isFinite ha
  have hbound : ∀ᵐ z ∂tailMeasure a,
      ‖cuspMode n t z‖ ^ 2 ≤ 4 / (frequencyScale n ^ 2 * a) := by
    filter_upwards [ae_restrict_mem (tailSet_measurable a)] with z hz
    exact cuspMode_norm_sq_le n hn t a ha hz
  have h := integral_mono_ae (cuspMode_norm_sq_integrable n hn t a ha)
    (integrable_const (4 / (frequencyScale n ^ 2 * a))) hbound
  have hc : (∫ _ : CuspCylinder, 4 / (frequencyScale n ^ 2 * a) ∂tailMeasure a) =
      cuspL2Budget n a := by
    rw [integral_const, smul_eq_mul]
    change (tailMeasure a univ).toReal * (4 / (frequencyScale n ^ 2 * a)) = _
    rw [tailMeasure_univ]
    unfold cuspL2Budget
    ring
  exact h.trans_eq hc

/-- Exact horizontal elimination; heightMeasure is dy/y^2 by definition. -/
theorem cuspMode_energy_horizontal_elimination (n : ℤ) (hn : n ≠ 0)
    (t a : ℝ) (ha : 0 < a) :
    (∫ z, ‖cuspMode n t z‖ ^ 2 ∂tailMeasure a) =
      ∫ y in heightTail a, (y : ℝ) *
        imaginaryOrderK t (frequencyScale n * (y : ℝ)) ^ 2 ∂heightMeasure := by
  have hi := cuspMode_norm_sq_integrable n hn t a ha
  rw [tailMeasure_eq_prod] at hi ⊢
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    simp only [cuspMode_norm_sq]
    simp [integral_const])

end
end ImbalancedChen.Part3.CuspCylinderBesselMode20261024z

