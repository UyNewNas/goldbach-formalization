import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED. This is a measure-level proof of positive dilation
invariance of the literal dq/q measure. It starts from withDensity and
Lebesgue-volume scaling; it does not infer measure equality from the earlier
complex Bochner-integral bridge. The local measure definition is intentionally
definitionally identical to PositiveMultiplicativeMeasureSourceOnly's draft,
so these theorems can be moved there when ROOT assembles actual modules.
-/

namespace ImbalancedChen.Part3.PositiveMultiplicativeMapSourceOnly

noncomputable section

open Classical Set MeasureTheory

/-- The same positive physical dq/q density used by the previous draft. -/
def positiveMultiplicativeMeasure : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
    (fun q : ℝ => ENNReal.ofReal (q⁻¹))

/-- Extend the reciprocal density by zero outside the positive axis. -/
private def positiveReciprocalDensity : ℝ → ℝ≥0∞ :=
  (Ioi (0 : ℝ)).indicator (fun q : ℝ => ENNReal.ofReal (q⁻¹))

private theorem positiveReciprocalDensity_measurable :
    Measurable positiveReciprocalDensity := by
  unfold positiveReciprocalDensity
  exact (by fun_prop : Measurable (fun q : ℝ => ENNReal.ofReal (q⁻¹))).indicator
    measurableSet_Ioi

private theorem positiveMultiplicativeMeasure_eq_withDensity :
    positiveMultiplicativeMeasure =
      (volume : Measure ℝ).withDensity positiveReciprocalDensity := by
  unfold positiveMultiplicativeMeasure positiveReciprocalDensity
  exact (withDensity_indicator measurableSet_Ioi
    (fun q : ℝ => ENNReal.ofReal (q⁻¹))).symm

/-- The reciprocal density transforms exactly with the inverse dilation. -/
private theorem positiveReciprocalDensity_scale
    (Y : ℝ) (hY : 0 < Y) (q : ℝ) :
    positiveReciprocalDensity q =
      ENNReal.ofReal Y * positiveReciprocalDensity (Y*q) := by
  by_cases hq : 0 < q
  · have hYq : 0 < Y*q := mul_pos hY hq
    simp only [positiveReciprocalDensity,
      Set.indicator_of_mem (show q ∈ Ioi (0 : ℝ) from hq),
      Set.indicator_of_mem (show Y*q ∈ Ioi (0 : ℝ) from hYq)]
    rw [← ENNReal.ofReal_mul hY.le]
    congr 1
    field_simp [hY.ne', hq.ne'] <;> ring
  · have hYq : Y*q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hY.le (le_of_not_gt hq)
    simp only [positiveReciprocalDensity,
      Set.indicator_of_notMem (show q ∉ Ioi (0 : ℝ) from hq),
      Set.indicator_of_notMem (show Y*q ∉ Ioi (0 : ℝ) from not_lt.mpr hYq),
      mul_zero]

/-- Lebesgue's inverse Jacobian under a positive real dilation, at the
extended-nonnegative integral level. -/
private theorem lintegral_volume_positive_scale
    (Y : ℝ) (hY : 0 < Y) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q : ℝ, F (Y*q) ∂(volume : Measure ℝ)) =
      ENNReal.ofReal (Y⁻¹) * ∫⁻ q : ℝ, F q ∂(volume : Measure ℝ) := by
  have hscale : Measurable (fun q : ℝ => Y*q) := by fun_prop
  have hmap : Measure.map (fun q : ℝ => Y*q) (volume : Measure ℝ) =
      ENNReal.ofReal (Y⁻¹) • (volume : Measure ℝ) := by
    simpa [smul_eq_mul, Module.finrank_self, abs_of_pos hY,
      abs_of_pos (inv_pos.mpr hY)] using
      (Measure.map_addHaar_smul (volume : Measure ℝ) hY.ne')
  calc
    (∫⁻ q : ℝ, F (Y*q) ∂(volume : Measure ℝ)) =
        ∫⁻ q : ℝ, F q ∂Measure.map (fun x : ℝ => Y*x) (volume : Measure ℝ) :=
      (lintegral_map hF hscale).symm
    _ = ∫⁻ q : ℝ, F q ∂(ENNReal.ofReal (Y⁻¹) • (volume : Measure ℝ)) := by
      rw [hmap]
    _ = ENNReal.ofReal (Y⁻¹) * ∫⁻ q : ℝ, F q ∂(volume : Measure ℝ) := by
      simp only [lintegral_smul_measure, smul_eq_mul]

/-- Precise change of variables for every measurable nonnegative extended
function, including infinite integrals. -/
theorem lintegral_positiveMultiplicativeMeasure_scale
    (Y : ℝ) (hY : 0 < Y) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ q : ℝ, g (Y*q) ∂positiveMultiplicativeMeasure) =
      ∫⁻ q : ℝ, g q ∂positiveMultiplicativeMeasure := by
  have hscale : Measurable (fun q : ℝ => Y*q) := by fun_prop
  have hF : Measurable (fun q : ℝ => positiveReciprocalDensity q * g q) :=
    positiveReciprocalDensity_measurable.mul hg
  have hcancel : ENNReal.ofReal Y * ENNReal.ofReal (Y⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hY.le, mul_inv_cancel₀ hY.ne']
    norm_num
  calc
    (∫⁻ q : ℝ, g (Y*q) ∂positiveMultiplicativeMeasure) =
        ∫⁻ q : ℝ, positiveReciprocalDensity q * g (Y*q)
          ∂(volume : Measure ℝ) := by
      rw [positiveMultiplicativeMeasure_eq_withDensity]
      exact lintegral_withDensity_eq_lintegral_mul
        (volume : Measure ℝ) positiveReciprocalDensity_measurable
        (hg.comp hscale)
    _ = ∫⁻ q : ℝ,
          ENNReal.ofReal Y *
            (positiveReciprocalDensity (Y*q) * g (Y*q))
          ∂(volume : Measure ℝ) := by
      apply lintegral_congr
      intro q
      rw [positiveReciprocalDensity_scale Y hY q, mul_assoc]
    _ = ENNReal.ofReal Y *
          ∫⁻ q : ℝ, positiveReciprocalDensity (Y*q) * g (Y*q)
            ∂(volume : Measure ℝ) := by
      exact lintegral_const_mul _ (hF.comp hscale)
    _ = ENNReal.ofReal Y *
          (ENNReal.ofReal (Y⁻¹) *
            ∫⁻ q : ℝ, positiveReciprocalDensity q * g q
              ∂(volume : Measure ℝ)) := by
      rw [lintegral_volume_positive_scale Y hY _ hF]
    _ = ∫⁻ q : ℝ, positiveReciprocalDensity q * g q
          ∂(volume : Measure ℝ) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ = ∫⁻ q : ℝ, g q ∂positiveMultiplicativeMeasure := by
      rw [positiveMultiplicativeMeasure_eq_withDensity]
      exact (lintegral_withDensity_eq_lintegral_mul
        (volume : Measure ℝ) positiveReciprocalDensity_measurable hg).symm

/-- Dilation preserves the literal positive physical dq/q measure. -/
theorem map_positiveMultiplicativeMeasure_scale
    (Y : ℝ) (hY : 0 < Y) :
    Measure.map (fun q : ℝ => Y*q) positiveMultiplicativeMeasure =
      positiveMultiplicativeMeasure := by
  have hscale : Measurable (fun q : ℝ => Y*q) := by fun_prop
  apply Measure.ext_of_lintegral positiveMultiplicativeMeasure
  intro g hg
  rw [lintegral_map hg hscale]
  exact lintegral_positiveMultiplicativeMeasure_scale Y hY g hg

theorem measurePreserving_positiveMultiplicativeMeasure_scale
    (Y : ℝ) (hY : 0 < Y) :
    MeasurePreserving (fun q : ℝ => Y*q)
      positiveMultiplicativeMeasure positiveMultiplicativeMeasure := by
  exact ⟨by fun_prop, map_positiveMultiplicativeMeasure_scale Y hY⟩

end

end ImbalancedChen.Part3.PositiveMultiplicativeMapSourceOnly
