import ImbalancedChen.Part3ActualEisensteinHorocycleGreenFlux
import ImbalancedChen.Part3ActualCompletedGreenCurrentRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Actual first-height jets of every positive INTEGER oldform dilation.
The derivative multiplier n is retained. Both literal remainders have
honest zero unit-period means, from the full-level actual zero means and
the proved periodic integer-dilation integral. Their pointwise decay
retains physical height n*y before the monotone n>=1 estimate. This is
the analytic input missing from the existing finite all-level constants.
No assumed jet mean, cusp-tail bound or flux identity is an input.
-/

noncomputable section
open Set Complex Filter Topology MeasureTheory
open ImbalancedChen.Part3.ActualEisensteinHorocycleRemainder20261026b
open ImbalancedChen.Part3.ActualEisensteinHorocycleJetMean20261026b
open ImbalancedChen.Part3.ActualCompletedGreenCurrentRegularity20261026b
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedEisensteinSpatialMaass
open ImbalancedChen.Part3.CompletedEisensteinCuspTail20261025a
open ImbalancedChen.Part3.ActualEisensteinHeightDerivativeTail20261026b

namespace ImbalancedChen.Part3.IntegerDilatedEisensteinHeightJets20261026b

def scaledFourier (n : ℕ+) (s : ℂ) (y x : ℝ) : ℂ :=
  completedEisensteinFourier s ((n : ℝ) * y) ((n : ℝ) * x)

def scaledConstant (n : ℕ+) (s : ℂ) (y : ℝ) : ℂ :=
  completedConstant ((n : ℝ) * y) s

def scaledConstantFirst (n : ℕ+) (s : ℂ) (y : ℝ) : ℂ :=
  (n : ℝ) • completedFirst s ((n : ℝ) * y)

def scaledRemainder (n : ℕ+) (s : ℂ) (y x : ℝ) : ℂ :=
  actualRemainder s ((n : ℝ) * y) ((n : ℝ) * x)

def scaledRemainderY (n : ℕ+) (s : ℂ) (y x : ℝ) : ℂ :=
  (n : ℝ) • actualRemainderY s ((n : ℝ) * y) ((n : ℝ) * x)

theorem scaledConstant_hasDerivAt (n : ℕ+) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (scaledConstant n s) (scaledConstantFirst n s y) y := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast n.pos
  simpa only [scaledConstant, scaledConstantFirst, Function.comp_def, mul_one] using
    (completedConstant_hasDerivAt s hs0 hs1 (mul_pos hn hy)).scomp y
      ((hasDerivAt_id y).const_mul (n : ℝ))

theorem scaledFourier_hasDerivAt_y (n : ℕ+) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun v : ℝ => scaledFourier n s v x)
      (scaledConstantFirst n s y + scaledRemainderY n s y x) y := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast n.pos
  have hd := (completedFourier_hasDerivAt_y s hs0 hs1 ((n : ℝ) * y)
    ((n : ℝ) * x) (mul_pos hn hy)).scomp y ((hasDerivAt_id y).const_mul (n : ℝ))
  have hjet := (completedConstant_hasDerivAt s hs0 hs1 (mul_pos hn hy)).deriv
  have hfjet := (completedFourier_hasDerivAt_y s hs0 hs1 ((n : ℝ) * y)
    ((n : ℝ) * x) (mul_pos hn hy)).deriv
  convert hd using 1 <;>
    simp only [scaledFourier, scaledConstantFirst, scaledRemainderY,
      actualRemainderY, hfjet, hjet, Function.comp_def, mul_one, Complex.real_smul] <;> ring

/-- The remainder Y is the true derivative of the actual subtracted field. -/
theorem scaledRemainder_hasDerivAt_y (n : ℕ+) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun v : ℝ => scaledRemainder n s v x) (scaledRemainderY n s y x) y := by
  have h := (scaledFourier_hasDerivAt_y n s hs0 hs1 hy x).sub
    (scaledConstant_hasDerivAt n s hs0 hs1 hy)
  simpa only [scaledFourier, scaledConstant, scaledRemainder, actualRemainder,
    add_sub_cancel_left] using h

theorem actualRemainder_horizontal_periodic (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) : Function.Periodic (actualRemainder s y) 1 := by
  intro x
  unfold actualRemainder
  rw [completedFourier_horizontal_periodic s hs0 hs1 y hy x]

theorem actualRemainderY_horizontal_periodic (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) : Function.Periodic (actualRemainderY s y) 1 := by
  intro x
  have he : (fun v : ℝ => completedEisensteinFourier s v (x + 1)) =ᶠ[𝓝 y]
      (fun v : ℝ => completedEisensteinFourier s v x) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with v hv
    exact completedFourier_horizontal_periodic s hs0 hs1 v hv x
  unfold actualRemainderY
  rw [he.deriv_eq]

/-- Native periodic integration pays for the integer-scaled horizontal
frequency. No Fourier or zero-mean preservation assertion is assumed. -/
theorem integer_scaled_mean_zero (n : ℕ+) (f : ℝ → ℂ) (hf : Continuous f)
    (hp : Function.Periodic f 1) (hm : (∫ x in (0 : ℝ)..1, f x) = 0) :
    (∫ x in (0 : ℝ)..1, f ((n : ℝ) * x)) = 0 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hint : (∫ x in (0 : ℝ)..(n : ℝ), f x) = 0 := by
    simpa only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one, hm, smul_zero, mul_zero] using
      hp.intervalIntegral_add_zsmul_eq ((n : ℕ) : ℤ) 0 (fun a b => hf.intervalIntegrable a b)
  rw [intervalIntegral.integral_comp_mul_left f hn]
  simpa only [mul_zero, mul_one, hint, smul_zero]

theorem scaledRemainder_continuous_x (n : ℕ+) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    Continuous (scaledRemainder n s y) :=
  (actualRemainder_continuous_x s (mul_pos (by exact_mod_cast n.pos) hy)).comp (by fun_prop)

theorem scaledRemainderY_continuous_x (n : ℕ+) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) : Continuous (scaledRemainderY n s y) :=
  ((actualRemainderY_continuous_x s hs0 hs1
    (mul_pos (by exact_mod_cast n.pos) hy)).comp (by fun_prop)).const_smul (n : ℝ)

theorem scaledRemainder_mean_zero (n : ℕ+) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) : (∫ x in (0 : ℝ)..1, scaledRemainder n s y x) = 0 :=
  integer_scaled_mean_zero n _
    (actualRemainder_continuous_x s (mul_pos (by exact_mod_cast n.pos) hy))
    (actualRemainder_horizontal_periodic s hs0 hs1 (mul_pos (by exact_mod_cast n.pos) hy))
    (actualRemainder_mean_zero s (mul_pos (by exact_mod_cast n.pos) hy))

theorem scaledRemainderY_mean_zero (n : ℕ+) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) : (∫ x in (0 : ℝ)..1, scaledRemainderY n s y x) = 0 := by
  unfold scaledRemainderY
  rw [intervalIntegral.integral_smul, integer_scaled_mean_zero n _
    (actualRemainderY_continuous_x s hs0 hs1 (mul_pos (by exact_mod_cast n.pos) hy))
    (actualRemainderY_horizontal_periodic s hs0 hs1 (mul_pos (by exact_mod_cast n.pos) hy))
    (actualRemainderY_mean_zero s hs0 hs1 (mul_pos (by exact_mod_cast n.pos) hy)), smul_zero]

theorem scaled_height_exp_le (n : ℕ+) {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-(Real.pi / 2) * ((n : ℝ) * y)) ≤ Real.exp (-(Real.pi / 2) * y) := by
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.one_le
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr hn) hy]

theorem scaledRemainder_bound (n : ℕ+) (M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖scaledRemainder n s y x‖ ≤
      cuspTailConstant M * Real.exp (-(Real.pi / 2) * y) := by
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.one_le
  have hny : 1 ≤ (n : ℝ) * y := one_le_mul_of_one_le_of_one_le hn hy
  exact (completedFourier_cusp_tail_bound_strip M hs hny ((n : ℝ) * x)).trans
    (mul_le_mul_of_nonneg_left (scaled_height_exp_le n (by linarith)) (cuspTailConstant_pos M).le)

theorem scaledRemainderY_bound (n : ℕ+) (M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖scaledRemainderY n s y x‖ ≤
      ((n : ℝ) * derivativeTailConstant M) * Real.exp (-(Real.pi / 2) * y) := by
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.one_le
  have hny : 1 ≤ (n : ℝ) * y := one_le_mul_of_one_le_of_one_le hn hy
  have hb := completedActual_chart_derivative_remainder_bound M hs hs0 hs1 hny ((n : ℝ) * x)
  change ‖actualRemainderY s ((n : ℝ) * y) ((n : ℝ) * x)‖ ≤ _ at hb
  unfold scaledRemainderY
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
  calc
    _ ≤ (n : ℝ) * (derivativeTailConstant M * Real.exp (-(Real.pi / 2) * ((n : ℝ) * y))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (n : ℝ) * (derivativeTailConstant M * Real.exp (-(Real.pi / 2) * y)) := by
      gcongr
      exact scaled_height_exp_le n (by linarith)
    _ = _ := by ring

end ImbalancedChen.Part3.IntegerDilatedEisensteinHeightJets20261026b
