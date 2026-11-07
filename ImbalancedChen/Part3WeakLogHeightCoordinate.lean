import ImbalancedChen.Part3AbsoluteContinuousMonotoneCoordinate
import ImbalancedChen.Part3ZeroModeWeakOpenHalfLine
import ImbalancedChen.Part3WeightedHeightNativeUnitary
import ImbalancedChen.Part3CuspModePhysicalCoreForm

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The actual log/sqrt-height transform of a genuine local-AC weak representative
is locally AC. Its a.e. derivative is derived by product and chain rules,
using the clean nonsingular native height chart to transfer the original
a.e. derivative statement. No weak change-of-variables, derivative formula,
or graph approximation is assumed.
-/

namespace ImbalancedChen.Part3.WeakLogHeightCoordinate20261026b
noncomputable section
open MeasureTheory Set Filter
open CuspCylinderMeasure20261024z CuspModePhysicalCoreForm20261026a
open WeightedHeightLogMeasure20261026a WeightedHeightNativeUnitary20261026a
open ZeroModeWeakOpenHalfLine20261026b AbsoluteContinuousMonotoneCoordinate20261026b
attribute [local instance] Measure.Subtype.measureSpace

def weakLogValue (a : ℝ) (u : ℝ → ℂ) (r : ℝ) : ℂ :=
  (heightForwardAmplitude a r : ℂ) * u (heightChart a r)

def weakLogShear (a : ℝ) (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  ((heightForwardAmplitude a r * heightChart a r : ℝ) : ℂ) * g (heightChart a r)

theorem weakLogValue_eq_inverse_sqrt {a : ℝ} (ha : 0 < a) (u : ℝ → ℂ) (r : ℝ) :
    weakLogValue a u r = (Real.sqrt (heightChart a r) : ℂ)⁻¹ * u (heightChart a r) := by
  have hinv := heightForwardAmplitude_inverse_coefficient a ha r
  have hs : (Real.sqrt (heightChart a r) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (heightChart_pos ha r)).ne'
  have hc : (heightForwardAmplitude a r : ℂ) * (Real.sqrt (heightChart a r) : ℂ) = 1 := by
    exact_mod_cast hinv
  have hA : (heightForwardAmplitude a r : ℂ) = (Real.sqrt (heightChart a r) : ℂ)⁻¹ := by
    apply mul_right_cancel₀ hs
    calc
      _ = 1 := hc
      _ = _ := by simp [hs]
  simp only [weakLogValue, hA]

/-- Nonsingularity for arbitrary a.e. real-height statements, derived through
the literal positive-height subtype and its dy/y^2 measure. -/
theorem ae_heightChart_of_ae {p : ℝ → Prop} (hp : ∀ᵐ y, p y)
    {a : ℝ} (ha : 0 < a) : ∀ᵐ r, p (heightChart a r) := by
  have hsub : ∀ᵐ y : PositiveHeight ∂(volume : Measure PositiveHeight), p (y : ℝ) :=
    (ae_restrict_iff_subtype measurableSet_Ioi).mp (ae_restrict_of_ae hp)
  have hac : heightMeasure ≪ (volume : Measure PositiveHeight) :=
    withDensity_absolutelyContinuous _ _
  have hh : ∀ᵐ y : PositiveHeight ∂heightMeasure, p (y : ℝ) := hac.ae hsub
  have hr := (scaledHeightEquiv_quasiMeasurePreserving a ha).ae hh
  simpa only [scaledHeightEquiv_coe, heightChart] using hr

theorem heightForwardAmplitude_hasDerivAt (a r : ℝ) :
    HasDerivAt (heightForwardAmplitude a)
      ((-1 / 2 : ℝ) * heightForwardAmplitude a r) r := by
  have hi : HasDerivAt (fun s : ℝ => -s / 2) (-1 / 2 : ℝ) r := by
    convert (hasDerivAt_id r).neg.div_const 2 using 1 <;> ring
  have h := ((Real.hasDerivAt_exp (-r / 2)).comp r hi).const_mul (Real.sqrt a)
  convert h using 1 <;> simp only [heightForwardAmplitude] <;> ring

theorem weakLogValue_continuousOn {a R : ℝ} (ha : 0 < a) {f g : ℝ → ℂ}
    (u : OpenHalfLineSobolevRepresentative (heightChart a R) f g) :
    ContinuousOn (weakLogValue a u.function) (Ioi R) := by
  have hA : Continuous (fun r : ℝ => (heightForwardAmplitude a r : ℂ)) := by
    unfold heightForwardAmplitude
    fun_prop
  apply hA.continuousOn.mul
  apply u.continuous.comp (Real.continuous_exp.div_const a).continuousOn
  intro r hr
  exact (div_lt_div_iff_of_pos_right ha).mpr (Real.exp_lt_exp.mpr hr)

theorem weakLogValue_re_ac {a R r s : ℝ} (ha : 0 < a) (hr : R < r) (hrs : r ≤ s)
    {f g : ℝ → ℂ} (u : OpenHalfLineSobolevRepresentative (heightChart a R) f g) :
    AbsolutelyContinuousOnInterval (fun t => (weakLogValue a u.function t).re) r s := by
  have hphysical : heightChart a R < heightChart a r :=
    (div_lt_div_iff_of_pos_right ha).mpr (Real.exp_lt_exp.mpr hr)
  have horder : heightChart a r ≤ heightChart a s :=
    (div_le_div_iff_of_pos_right ha).mpr (Real.exp_le_exp.mpr hrs)
  have hu := u.re_ac (heightChart a r) (heightChart a s) hphysical horder
  have hcomp := absolutelyContinuous_comp_scaled_exp ha r s hu
  have hAd : ContDiff ℝ 1 (heightForwardAmplitude a) := by
    unfold heightForwardAmplitude
    fun_prop
  have hA := hAd.contDiffOn.absolutelyContinuousOnInterval (a := r) (b := s)
  simpa [weakLogValue, heightChart, Complex.mul_re] using hA.mul hcomp

theorem weakLogValue_im_ac {a R r s : ℝ} (ha : 0 < a) (hr : R < r) (hrs : r ≤ s)
    {f g : ℝ → ℂ} (u : OpenHalfLineSobolevRepresentative (heightChart a R) f g) :
    AbsolutelyContinuousOnInterval (fun t => (weakLogValue a u.function t).im) r s := by
  have hphysical : heightChart a R < heightChart a r :=
    (div_lt_div_iff_of_pos_right ha).mpr (Real.exp_lt_exp.mpr hr)
  have horder : heightChart a r ≤ heightChart a s :=
    (div_le_div_iff_of_pos_right ha).mpr (Real.exp_le_exp.mpr hrs)
  have hu := u.im_ac (heightChart a r) (heightChart a s) hphysical horder
  have hcomp := absolutelyContinuous_comp_scaled_exp ha r s hu
  have hAd : ContDiff ℝ 1 (heightForwardAmplitude a) := by
    unfold heightForwardAmplitude
    fun_prop
  have hA := hAd.contDiffOn.absolutelyContinuousOnInterval (a := r) (b := s)
  simpa [weakLogValue, heightChart, Complex.mul_im] using hA.mul hcomp

/-- The actual weak-coordinate shear derivative; the formula is proved from
the constructed representative's a.e. derivative and the native chain rule. -/
theorem weakLogValue_hasDerivAt_ae {a R : ℝ} (ha : 0 < a) {f g : ℝ → ℂ}
    (u : OpenHalfLineSobolevRepresentative (heightChart a R) f g) :
    ∀ᵐ r, r ∈ Ioi R → HasDerivAt (weakLogValue a u.function)
      (weakLogShear a g r - (1 / 2 : ℂ) * weakLogValue a u.function r) r := by
  have hae := ae_heightChart_of_ae u.derivative_ae ha
  filter_upwards [hae] with r hr hrR
  have hy : heightChart a R < heightChart a r :=
    (div_lt_div_iff_of_pos_right ha).mpr (Real.exp_lt_exp.mpr hrR)
  have hcomp := (hr hy).scomp r (heightChart_hasDerivAt ha r)
  have hprod := (heightForwardAmplitude_hasDerivAt a r).ofReal_comp.mul hcomp
  convert hprod using 1 <;>
    simp only [weakLogValue, weakLogShear, Complex.real_smul,
      Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] <;> ring

/-- The native shear coefficient is literally sqrt(y), rather than a
renormalized automorphic spectral density. -/
theorem weakLogShear_coefficient {a : ℝ} (ha : 0 < a) (r : ℝ) :
    heightForwardAmplitude a r * heightChart a r = Real.sqrt (heightChart a r) := by
  have hy := heightChart_pos ha r
  have hinv := heightForwardAmplitude_inverse_coefficient a ha r
  have hsq := Real.sq_sqrt hy.le
  change heightForwardAmplitude a r * Real.sqrt (heightChart a r) = 1 at hinv
  calc
    _ = heightForwardAmplitude a r * Real.sqrt (heightChart a r) ^ 2 :=
      congrArg (fun t : ℝ => heightForwardAmplitude a r * t) hsq.symm
    _ = (heightForwardAmplitude a r * Real.sqrt (heightChart a r)) *
        Real.sqrt (heightChart a r) := by ring
    _ = _ := by rw [hinv]; simp

end
end ImbalancedChen.Part3.WeakLogHeightCoordinate20261026b
