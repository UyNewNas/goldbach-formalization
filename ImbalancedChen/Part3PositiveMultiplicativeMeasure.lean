import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
SOURCEONLY / UNCOMPILED. The positive-axis measure below is the literal
dq/q measure on the real physical q coordinate. Its bridge to the existing
actual K transform uses the proved physical integrability. This is no
automorphic or GL2 Plancherel assertion.
-/

namespace ImbalancedChen.Part3.PositiveMultiplicativeMeasureSourceOnly

noncomputable section

open Classical Set MeasureTheory
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralMode spectralTest)
open ImaginaryOrderKBesselSourceOnly
open ActualCommonHeightKGramSourceOnly (kTestTransform kTestTransform_integrable)

variable {ι : Type*}

/-- The physical positive-axis dq/q measure, with zero mass outside q>0. -/
def positiveMultiplicativeMeasure : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
    (fun q : ℝ => ENNReal.ofReal (q⁻¹))

private theorem reciprocal_density_measurable :
    Measurable (fun q : ℝ => ENNReal.ofReal (q⁻¹)) := by
  fun_prop

/-- Its density is strictly positive at every point of the positive axis. -/
private theorem reciprocal_density_ne_zero {q : ℝ} (hq : 0 < q) :
    ENNReal.ofReal (q⁻¹) ≠ 0 :=
  ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr hq)

/-- The density does not change which assertions hold almost everywhere on
the positive axis. -/
theorem ae_positiveMultiplicativeMeasure_iff {p : ℝ → Prop} :
    (∀ᵐ q ∂positiveMultiplicativeMeasure, p q) ↔
      ∀ᵐ q ∂(volume : Measure ℝ).restrict (Ioi 0), p q := by
  unfold positiveMultiplicativeMeasure
  rw [ae_withDensity_iff reciprocal_density_measurable]
  constructor
  · intro h
    filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with q hp hq
    exact hp (reciprocal_density_ne_zero hq)
  · intro h
    exact h.mono (fun _ hp _ => hp)

/-- Every compact interval bounded away from zero has finite dq/q mass. -/
theorem positiveMultiplicativeMeasure_Icc_lt_top
    {a b : ℝ} (ha : 0 < a) :
    positiveMultiplicativeMeasure (Icc a b) < ∞ := by
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := by
    intro q hq
    exact lt_of_lt_of_le ha hq.1
  have hc : ContinuousOn (fun q : ℝ => q⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun q hq => ne_of_gt (hsub hq))
  have hi : IntegrableOn (fun q : ℝ => q⁻¹) (Icc a b) :=
    hc.integrableOn_compact isCompact_Icc
  have hn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Icc a b)]
      (fun q : ℝ => q⁻¹) :=
    (ae_restrict_mem measurableSet_Icc).mono
      (fun q hq => inv_nonneg.mpr (hsub hq).le)
  have hfinite :
      (∫⁻ q : ℝ, ENNReal.ofReal (q⁻¹)
        ∂(volume : Measure ℝ).restrict (Icc a b)) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable
      hi.aestronglyMeasurable hn).2 hi
  change (((volume : Measure ℝ).restrict (Ioi 0)).withDensity
    (fun q : ℝ => ENNReal.ofReal (q⁻¹))) (Icc a b) < ∞
  rw [← Measure.restrict_apply_univ,
    restrict_withDensity measurableSet_Icc,
    Measure.restrict_restrict_of_subset hsub,
    withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact lt_top_iff_ne_top.mpr hfinite

/-- Bochner integration against dq/q is the positive-axis Lebesgue integral
with the reciprocal factor. This identity is valid for every complex function;
Mathlib's integral convention covers the nonintegrable case. -/
private theorem integral_positiveMultiplicativeMeasure_eq (g : ℝ → ℂ) :
    (∫ q : ℝ, g q ∂positiveMultiplicativeMeasure) =
      ∫ q in Ioi (0 : ℝ), q⁻¹ • g q := by
  have hden := integral_withDensity_eq_integral_toReal_smul
    (μ := (volume : Measure ℝ).restrict (Ioi 0))
    reciprocal_density_measurable
    (Filter.Eventually.of_forall (fun q : ℝ => ENNReal.ofReal_lt_top)) g
  calc
    (∫ q : ℝ, g q ∂positiveMultiplicativeMeasure) =
        ∫ q in Ioi (0 : ℝ),
          (ENNReal.ofReal (q⁻¹)).toReal • g q := hden
    _ = ∫ q in Ioi (0 : ℝ), q⁻¹ • g q := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hq.le)]

/-- Exact positive multiplicative invariance of every complex Bochner
integral. The substitution theorem supplies the physical Jacobian; the
reciprocal density cancels it. -/
theorem integral_positiveMultiplicativeMeasure_mul
    (Y : ℝ) (hY : 0 < Y) (g : ℝ → ℂ) :
    (∫ q : ℝ, g (Y*q) ∂positiveMultiplicativeMeasure) =
      ∫ q : ℝ, g q ∂positiveMultiplicativeMeasure := by
  have hscale := integral_comp_mul_left_Ioi'
    (fun q : ℝ => q⁻¹ • g q) 0 hY
  simp only [mul_zero] at hscale
  calc
    (∫ q : ℝ, g (Y*q) ∂positiveMultiplicativeMeasure) =
        ∫ q in Ioi (0 : ℝ), q⁻¹ • g (Y*q) :=
      integral_positiveMultiplicativeMeasure_eq _
    _ = Y • ∫ q in Ioi (0 : ℝ), (Y*q)⁻¹ • g (Y*q) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      have hcoef : q⁻¹ = Y * (Y*q)⁻¹ := by
        field_simp [hY.ne', hq.ne'] <;> ring
      rw [smul_smul, ← hcoef]
    _ = ∫ q in Ioi (0 : ℝ), q⁻¹ • g q := hscale
    _ = ∫ q : ℝ, g q ∂positiveMultiplicativeMeasure :=
      (integral_positiveMultiplicativeMeasure_eq g).symm

/-- The actual test-weighted K/q integrand vanishes off the positive axis. -/
private theorem actual_K_zero_off_positive (P : PacketData ι)
    (k : D4 → ℤ) (t q : ℝ) (hq : q ∉ Ioi (0 : ℝ)) :
    spectralTest k P.Y0 q *
      ((imaginaryOrderK t q : ℂ)/(q : ℂ)) = 0 := by
  have hnot : q ∉ P.region := by
    intro hr
    have hpos : 0 < P.Y0/16 := div_pos P.Y0_pos (by norm_num)
    exact hq (lt_of_lt_of_le hpos hr.1)
  simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hnot,
    Complex.ofReal_zero, zero_mul]

/-- The exact actual physical K transform is integration of the test times
K against dq/q. No scale or spectral weight is inserted. -/
theorem kTestTransform_eq_positiveMultiplicativeMeasure (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k t =
      ∫ q : ℝ, spectralTest k P.Y0 q *
        (imaginaryOrderK t q : ℂ) ∂positiveMultiplicativeMeasure := by
  let g : ℝ → ℂ := fun q =>
    spectralTest k P.Y0 q * (imaginaryOrderK t q : ℂ)
  calc
    kTestTransform P k t =
        ∫ q in Ioi (0 : ℝ), spectralTest k P.Y0 q *
          ((imaginaryOrderK t q : ℂ)/(q : ℂ)) := by
      unfold kTestTransform
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (actual_K_zero_off_positive P k t)).symm
    _ = ∫ q in Ioi (0 : ℝ), q⁻¹ • g q := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      simp only [g, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    _ = ∫ q : ℝ, g q ∂positiveMultiplicativeMeasure := by
      exact (integral_positiveMultiplicativeMeasure_eq g).symm
    _ = ∫ q : ℝ, spectralTest k P.Y0 q *
          (imaginaryOrderK t q : ℂ) ∂positiveMultiplicativeMeasure := rfl

/-- Integrability under dq/q follows from the already proved integrability
of the actual physical K/q integrand. -/
theorem kTestTransform_positiveMultiplicativeMeasure_integrable
    (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    Integrable (fun q : ℝ => spectralTest k P.Y0 q *
      (imaginaryOrderK t q : ℂ)) positiveMultiplicativeMeasure := by
  have hq := kTestTransform_integrable P k t
  have hr : Integrable (fun q : ℝ =>
      spectralTest k P.Y0 q *
        ((imaginaryOrderK t q : ℂ)/(q : ℂ)))
      ((volume : Measure ℝ).restrict (Ioi 0)) := hq.integrableOn
  have hden := (integrable_withDensity_iff_integrable_smul'
    (μ := (volume : Measure ℝ).restrict (Ioi 0))
    reciprocal_density_measurable
    (Filter.Eventually.of_forall (fun q : ℝ => ENNReal.ofReal_lt_top))
    (g := fun q : ℝ => spectralTest k P.Y0 q *
      (imaginaryOrderK t q : ℂ))).2
  apply hden
  apply hr.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hq.le)]
  simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

end

end ImbalancedChen.Part3.PositiveMultiplicativeMeasureSourceOnly
