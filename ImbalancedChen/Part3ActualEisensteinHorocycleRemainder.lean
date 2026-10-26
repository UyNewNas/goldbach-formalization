import ImbalancedChen.Part3ActualEisensteinHeightDerivativeTail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Actual high-cusp horocycle nonconstant mean square and Green flux

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The remainder and its first height derivative are those of the actual
completed continued Eisenstein Fourier expression. Uniform bounds on its
literal K series give exponentially vanishing horocycle mean square and
nonconstant/nonconstant Green current. The completed constant is retained
exactly. This does not assert cancellation of mixed constant/nonconstant
terms, paired quotient sides, or a spectral completeness measure.
-/
namespace ImbalancedChen.Part3.ActualEisensteinHorocycleRemainder20261026b
noncomputable section
open Set MeasureTheory
open CompletedEisensteinReflection20261025a CompletedEisensteinSpatialMaass
open ContinuedFourierMomentSeriesCalculus ContinuedFourierNonconstantMaass
open CompletedEisensteinCuspTail20261025a ActualEisensteinHeightDerivativeTail20261026b

def actualRemainder (s : ℂ) (y x : ℝ) : ℂ :=
  completedEisensteinFourier s y x - completedConstant y s

def actualRemainderY (s : ℂ) (y x : ℝ) : ℂ :=
  deriv (fun v : ℝ => completedEisensteinFourier s v x) y -
    deriv (fun v : ℝ => completedConstant v s) y

theorem actualRemainder_eq_kernel (s : ℂ) (y x : ℝ) :
    actualRemainder s y x = weightedKernel s y x := by
  simp only [actualRemainder, completedEisensteinFourier, weightedKernel, add_sub_cancel_left]

theorem actualRemainder_continuous_x (s : ℂ) {y : ℝ} (hy : 0 < y) :
    Continuous (actualRemainder s y) := by
  change Continuous (fun x : ℝ => actualRemainder s y x)
  simp_rw [actualRemainder_eq_kernel]
  exact continuous_iff_continuousAt.mpr (fun x => (weightedKernel_hasDerivAt_x s y x hy).continuousAt)

theorem actualRemainderY_eq_kernel (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) (x : ℝ) : actualRemainderY s y x = weightedKernelY s y x := by
  rw [actualRemainderY, (completedFourier_hasDerivAt_y s hs0 hs1 y x hy).deriv,
    (completedConstant_hasDerivAt s hs0 hs1 hy).deriv, completedFourierY, add_sub_cancel_left]

theorem actualRemainderY_continuous_x (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) : Continuous (actualRemainderY s y) := by
  change Continuous (fun x : ℝ => actualRemainderY s y x)
  simp_rw [actualRemainderY_eq_kernel s hs0 hs1 hy]
  have h0 : Continuous (fun x => signedMomentSum 0 0 s y x) :=
    continuous_iff_continuousAt.mpr (fun x => (signedMomentSum_hasDerivAt_x 0 0 s y x hy).continuousAt)
  have h1 : Continuous (fun x => signedMomentSum 0 1 s y x) :=
    continuous_iff_continuousAt.mpr (fun x => (signedMomentSum_hasDerivAt_x 0 1 s y x hy).continuousAt)
  exact (h0.const_mul (2 * root1 y)).add (h1.const_mul (2 * root0 y))

/-- The actual nonconstant horocycle mass has a uniform exponential bound
on every fixed real-part strip, hence on every fixed compact spectral set. -/
theorem actualRemainder_horocycle_mean_square_bound (M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : 1 ≤ y) :
    (∫ x in (0 : ℝ)..1, ‖actualRemainder s y x‖ ^ 2) ≤
      (cuspTailConstant M * Real.exp (-(Real.pi / 2) * y)) ^ 2 := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hi := ((actualRemainder_continuous_x s hy0).norm.pow 2).intervalIntegrable 0 1
  have hb (x : ℝ) : ‖actualRemainder s y x‖ ≤
      cuspTailConstant M * Real.exp (-(Real.pi / 2) * y) :=
    completedFourier_cusp_tail_bound_strip M hs hy x
  have hbound : 0 ≤ cuspTailConstant M * Real.exp (-(Real.pi / 2) * y) :=
    mul_nonneg (cuspTailConstant_pos M).le (Real.exp_pos _).le
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hi
    intervalIntegrable_const (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hb x) 2)
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using h

/-- The nonconstant part of the actual Green current. Both actual height
jets occur; no formal derivative or boundary error is a premise. -/
def nonconstantGreenCurrent (s u : ℂ) (y x : ℝ) : ℂ :=
  star (actualRemainder s y x) * actualRemainderY u y x -
    star (actualRemainderY s y x) * actualRemainder u y x

theorem nonconstantGreenCurrent_bound (M : ℕ) {s u : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) (hu : |u.re| ≤ (M : ℝ))
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖nonconstantGreenCurrent s u y x‖ ≤
      2 * (cuspTailConstant M * derivativeTailConstant M) *
        (Real.exp (-(Real.pi / 2) * y)) ^ 2 := by
  have hrs : ‖actualRemainder s y x‖ ≤ cuspTailConstant M * Real.exp (-(Real.pi / 2) * y) :=
    completedFourier_cusp_tail_bound_strip M hs hy x
  have hru : ‖actualRemainder u y x‖ ≤ cuspTailConstant M * Real.exp (-(Real.pi / 2) * y) :=
    completedFourier_cusp_tail_bound_strip M hu hy x
  have hds := completedActual_chart_derivative_remainder_bound M hs hs0 hs1 hy x
  have hdu := completedActual_chart_derivative_remainder_bound M hu hu0 hu1 hy x
  change ‖actualRemainderY s y x‖ ≤ _ at hds
  change ‖actualRemainderY u y x‖ ≤ _ at hdu
  have hC := (cuspTailConstant_pos M).le
  have hD := (derivativeTailConstant_pos M).le
  unfold nonconstantGreenCurrent
  calc
    _ ≤ ‖star (actualRemainder s y x) * actualRemainderY u y x‖ +
        ‖star (actualRemainderY s y x) * actualRemainder u y x‖ := norm_sub_le _ _
    _ = ‖actualRemainder s y x‖ * ‖actualRemainderY u y x‖ +
        ‖actualRemainderY s y x‖ * ‖actualRemainder u y x‖ := by simp only [norm_mul, norm_star]
    _ ≤ (cuspTailConstant M * Real.exp (-(Real.pi / 2) * y)) *
        (derivativeTailConstant M * Real.exp (-(Real.pi / 2) * y)) +
        (derivativeTailConstant M * Real.exp (-(Real.pi / 2) * y)) *
        (cuspTailConstant M * Real.exp (-(Real.pi / 2) * y)) := by gcongr
    _ = _ := by ring

/-- Uniform exponentially decaying bound for the actual nonconstant
horocycle Green boundary integral, with unit horizontal length. -/
theorem nonconstantGreenCurrent_horocycle_bound (M : ℕ) {s u : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) (hu : |u.re| ≤ (M : ℝ))
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    {y : ℝ} (hy : 1 ≤ y) :
    ‖∫ x in (0 : ℝ)..1, nonconstantGreenCurrent s u y x‖ ≤
      2 * (cuspTailConstant M * derivativeTailConstant M) *
        (Real.exp (-(Real.pi / 2) * y)) ^ 2 := by
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x _ => nonconstantGreenCurrent_bound M hs hu hs0 hs1 hu0 hu1 hy x)

end
end ImbalancedChen.Part3.ActualEisensteinHorocycleRemainder20261026b

