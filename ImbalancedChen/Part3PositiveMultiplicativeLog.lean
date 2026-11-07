import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED. The logarithmic coordinate on the actual physical
positive q-axis. The measure statement comes from Mathlib's differentiable
Jacobian theorem, not from a presumed complex-integral substitution. The last
theorem is an exact coordinate identity for the already defined K transform;
it makes no spectral or decay assertion.
-/

namespace ImbalancedChen.Part3.PositiveMultiplicativeLogSourceOnly

noncomputable section

open Classical Set MeasureTheory ContinuousLinearMap
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralMode spectralTest)
open ImaginaryOrderKBesselSourceOnly
open ActualCommonHeightKGramSourceOnly (kTestTransform kTestTransform_integrable)

variable {ι : Type*}

/-- The physical positive-axis `dq/q` measure. It is definitionally the same
measure as in `Part3PositiveMultiplicativeMeasure.lean.txt`. -/
def positiveMultiplicativeMeasure : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
    (fun q : ℝ => ENNReal.ofReal (q⁻¹))

private theorem reciprocal_density_measurable :
    Measurable (fun q : ℝ => ENNReal.ofReal (q⁻¹)) := by
  fun_prop

/-- Direct Jacobian proof that logarithm sends physical `dq/q` to `dv`. -/
theorem map_log_positiveMultiplicativeMeasure :
    Measure.map Real.log positiveMultiplicativeMeasure =
      (volume : Measure ℝ) := by
  have hderiv : ∀ q ∈ Ioi (0 : ℝ),
      HasFDerivWithinAt Real.log
        (ContinuousLinearMap.toSpanSingleton ℝ (q⁻¹)) (Ioi (0 : ℝ)) q := by
    intro q hq
    exact (Real.hasDerivAt_log (ne_of_gt hq)).hasFDerivAt.hasFDerivWithinAt
  have himage : Real.log '' Ioi (0 : ℝ) = Set.univ := by
    ext v
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨Real.exp v, Real.exp_pos v, Real.log_exp v⟩
  have hJac := map_withDensity_abs_det_fderiv_eq_addHaar
    (μ := (volume : Measure ℝ))
    (f := Real.log)
    (f' := fun q : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (q⁻¹))
    measurableSet_Ioi.nullMeasurableSet hderiv Real.log_injOn_pos
  have hden :
      positiveMultiplicativeMeasure =
        ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
          (fun q : ℝ => ENNReal.ofReal
            |(ContinuousLinearMap.toSpanSingleton ℝ (q⁻¹)).det|) := by
    unfold positiveMultiplicativeMeasure
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    rw [det_toSpanSingleton, abs_of_pos (inv_pos.mpr hq)]
  calc
    Measure.map Real.log positiveMultiplicativeMeasure =
        Measure.map Real.log
          (((volume : Measure ℝ).restrict (Ioi 0)).withDensity
            (fun q : ℝ => ENNReal.ofReal
              |(ContinuousLinearMap.toSpanSingleton ℝ (q⁻¹)).det|)) := by
          rw [hden]
    _ = (volume : Measure ℝ).restrict (Real.log '' Ioi (0 : ℝ)) := hJac
    _ = (volume : Measure ℝ) := by rw [himage, Measure.restrict_univ]

/-- The inverse coordinate map sends `dv` to the literal `dq/q` measure. -/
theorem map_exp_volume :
    Measure.map Real.exp (volume : Measure ℝ) =
      positiveMultiplicativeMeasure := by
  have hpos : ∀ᵐ q ∂positiveMultiplicativeMeasure, 0 < q := by
    unfold positiveMultiplicativeMeasure
    exact (ae_restrict_mem measurableSet_Ioi).mono_ac
      (withDensity_absolutelyContinuous _ _)
  calc
    Measure.map Real.exp (volume : Measure ℝ) =
        Measure.map Real.exp
          (Measure.map Real.log positiveMultiplicativeMeasure) := by
          rw [map_log_positiveMultiplicativeMeasure]
    _ = Measure.map (Real.exp ∘ Real.log) positiveMultiplicativeMeasure :=
          Measure.map_map (by fun_prop) Real.measurable_log
    _ = Measure.map id positiveMultiplicativeMeasure := by
          apply Measure.map_congr
          filter_upwards [hpos] with q hq
          simp only [Function.comp_apply, id_eq, Real.exp_log hq]
    _ = positiveMultiplicativeMeasure := Measure.map_id

/-- The logarithmic chart is measure preserving when the source carries
physical `dq/q`; equivalently the exponential chart preserves `dv`. -/
theorem log_measurePreserving :
    MeasurePreserving Real.log positiveMultiplicativeMeasure
      (volume : Measure ℝ) :=
  ⟨Real.measurable_log, map_log_positiveMultiplicativeMeasure⟩

theorem exp_measurePreserving :
    MeasurePreserving Real.exp (volume : Measure ℝ)
      positiveMultiplicativeMeasure :=
  ⟨by fun_prop, map_exp_volume⟩

/-- The actual K/q integrand vanishes off the physical positive axis. -/
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

private theorem actual_K_dlog_integrable (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
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

/-- The exact actual transform in additive Mellin coordinate `v = log q`.
The factor `dq/q` has disappeared because `map exp dv = dq/q`. -/
theorem kTestTransform_eq_integral_exp (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k t =
      ∫ v : ℝ, spectralTest k P.Y0 (Real.exp v) *
        (imaginaryOrderK t (Real.exp v) : ℂ) := by
  let g : ℝ → ℂ := fun q =>
    spectralTest k P.Y0 q * (imaginaryOrderK t q : ℂ)
  have hg : Integrable g positiveMultiplicativeMeasure :=
    actual_K_dlog_integrable P k t
  calc
    kTestTransform P k t =
        ∫ q in Ioi (0 : ℝ), spectralTest k P.Y0 q *
          ((imaginaryOrderK t q : ℂ)/(q : ℂ)) := by
      unfold kTestTransform
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (actual_K_zero_off_positive P k t)).symm
    _ = ∫ q : ℝ, g q ∂positiveMultiplicativeMeasure := by
      rw [integral_positiveMultiplicativeMeasure_eq]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      simp only [g, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    _ = ∫ v : ℝ, g (Real.exp v) := by
      rw [← map_exp_volume]
      apply integral_map (by fun_prop)
      simpa only [map_exp_volume] using hg.aestronglyMeasurable
    _ = ∫ v : ℝ, spectralTest k P.Y0 (Real.exp v) *
          (imaginaryOrderK t (Real.exp v) : ℂ) := rfl

end

end ImbalancedChen.Part3.PositiveMultiplicativeLogSourceOnly
