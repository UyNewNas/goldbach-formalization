import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual exponentially damped logarithmic weight has integrable
derivative on each positive half-line. Its total variation is computed
exactly by the improper fundamental theorem. These are concrete inputs
to the uniform Abel cosine-kernel estimate; no oscillatory bound is a
hypothesis, and no critical Mellin or Bessel kernel is asserted.
-/

namespace ImbalancedChen.Part3.AbelLogWeightVariation20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

def abelWeight (ε t : ℝ) : ℝ := Real.exp (-ε*t) * t⁻¹

def abelLoss (ε t : ℝ) : ℝ := Real.exp (-ε*t) * (ε*t⁻¹+(t⁻¹)^2)

theorem abelWeight_measurable (ε : ℝ) : Measurable (abelWeight ε) := by
  unfold abelWeight
  fun_prop

theorem abelLoss_measurable (ε : ℝ) : Measurable (abelLoss ε) := by
  unfold abelLoss
  fun_prop

theorem abelWeight_nonneg (ε : ℝ) {t : ℝ} (ht : 0 < t) : 0 ≤ abelWeight ε t :=
  mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr ht.le)

theorem abelLoss_nonneg {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) :
    0 ≤ abelLoss ε t :=
  mul_nonneg (Real.exp_pos _).le
    (add_nonneg (mul_nonneg hε (inv_nonneg.mpr ht.le)) (sq_nonneg _))

theorem abelWeight_le_inv {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) :
    abelWeight ε t ≤ t⁻¹ := by
  have he : Real.exp (-ε*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right he (inv_nonneg.mpr ht.le)

theorem abelWeight_hasDerivAt (ε : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (abelWeight ε) (-abelLoss ε t) t := by
  convert (((hasDerivAt_id t).const_mul (-ε)).exp).mul ((hasDerivAt_id t).inv ht)
      using 1 <;> dsimp [abelWeight,abelLoss]
  field_simp [ht]
  <;> ring

theorem abelWeight_continuousAt (ε : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (abelWeight ε) t := (abelWeight_hasDerivAt ε ht).continuousAt

theorem abelWeight_bound_on_tail (ε : ℝ) {R t : ℝ} (hR : 0 < R) (ht : R ≤ t) :
    abelWeight ε t ≤ Real.exp (-ε*t)*R⁻¹ := by
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  simpa only [one_div] using one_div_le_one_div_of_le hR ht

theorem abelLoss_bound_on_tail {ε R t : ℝ} (hε : 0 ≤ ε) (hR : 0 < R) (ht : R ≤ t) :
    abelLoss ε t ≤ Real.exp (-ε*t)*(ε*R⁻¹+(R⁻¹)^2) := by
  have ht0 : 0 < t := hR.trans_le ht
  have hi : t⁻¹ ≤ R⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hR ht
  have hs : (t⁻¹)^2 ≤ (R⁻¹)^2 :=
    (sq_le_sq₀ (inv_nonneg.mpr ht0.le) (inv_nonneg.mpr hR.le)).mpr hi
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hi hε) hs) (Real.exp_pos _).le

theorem abelWeight_integrable {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    IntegrableOn (abelWeight ε) (Ioi R) := by
  have he : IntegrableOn (fun t : ℝ => Real.exp (-ε*t)) (Ioi R) :=
    integrableOn_exp_mul_Ioi (by linarith) R
  apply (he.mul_const R⁻¹).mono' (abelWeight_measurable ε).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (abelWeight_nonneg ε (hR.trans ht))]
  exact abelWeight_bound_on_tail ε hR ht.le

theorem abelLoss_integrable {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    IntegrableOn (abelLoss ε) (Ioi R) := by
  have he : IntegrableOn (fun t : ℝ => Real.exp (-ε*t)) (Ioi R) :=
    integrableOn_exp_mul_Ioi (by linarith) R
  apply (he.mul_const (ε*R⁻¹+(R⁻¹)^2)).mono' (abelLoss_measurable ε).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (abelLoss_nonneg hε.le (hR.trans ht))]
  exact abelLoss_bound_on_tail hε.le hR ht.le

/-- The limit follows already from the elementary 1/t bound. -/
theorem abelWeight_tendsto_zero {ε : ℝ} (hε : 0 ≤ ε) :
    Tendsto (abelWeight ε) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact abelWeight_nonneg ε ht
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact abelWeight_le_inv hε ht

/-- Exact positive derivative mass on a genuine positive half-line.
This produces the total-variation budget needed by sine-primitive IBP. -/
theorem integral_abelLoss {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    (∫ t in Ioi R, abelLoss ε t) = abelWeight ε R := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (abelWeight_continuousAt ε hR.ne').continuousWithinAt
    (fun t ht => abelWeight_hasDerivAt ε (hR.trans ht).ne')
    (abelLoss_integrable hε hR).neg (abelWeight_tendsto_zero hε.le)
  rw [integral_neg] at h
  linarith

end
end ImbalancedChen.Part3.AbelLogWeightVariation20261026b
