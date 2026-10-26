import ImbalancedChen.Part3ActualEisensteinHeightMomentDecay
import ImbalancedChen.Part3CompletedEisensteinSpatialMaass
import Mathlib.Tactic

/-!
# Actual completed Eisenstein first-height remainder decays in the cusp

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The actual continued completed Fourier expression has already been
differentiated by a genuine normal-convergence theorem. This module
bounds that actual derivative after subtracting the exact completed
constant term. It retains the central s=1/2 constant and both noncentral
incoming/outgoing powers; no constant term is discarded or renormalized.
-/
namespace ImbalancedChen.Part3.ActualEisensteinHeightDerivativeTail20261026b
noncomputable section
open Set MeasureTheory
open ContinuedFourierMomentSeriesCalculus ContinuedFourierNonconstantMaass
open CompletedEisensteinSpatialMaass CompletedEisensteinReflection20261025a
open CompletedEisensteinCuspTail20261025a ActualEisensteinHeightMomentDecay20261026b

def derivativeTailConstant (M : ℕ) : ℝ :=
  1 + (16 / Real.pi) * (heightMomentMass 0 0 M + heightMomentMass 0 1 M)

theorem derivativeTailConstant_pos (M : ℕ) : 0 < derivativeTailConstant M := by
  unfold derivativeTailConstant
  have h0 := heightMomentMass_nonneg 0 0 M
  have h1 := heightMomentMass_nonneg 0 1 M
  positivity

theorem root0_norm (y : ℝ) : ‖root0 y‖ = Real.sqrt y := by
  rw [root0_eq_sqrt]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg y)]

theorem root1_norm_le_root0 {y : ℝ} (hy : 1 ≤ y) : ‖root1 y‖ ≤ Real.sqrt y := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have h := congrArg norm (root1_relation hy0)
  norm_num only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0,
    norm_div, norm_one, Complex.norm_ofNat, root0_norm] at h
  have hmul := mul_nonneg (sub_nonneg.mpr hy) (norm_nonneg (root1 y))
  nlinarith [Real.sqrt_nonneg y]

/-- A uniform exponential bound for the literal nonconstant first-height
jet of the actual completed continued Eisenstein Fourier series. -/
theorem weightedKernelY_height_bound (M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖weightedKernelY s y x‖ ≤ derivativeTailConstant M * Real.exp (-(Real.pi / 2) * y) := by
  have h0 := signedMomentSum_height_bound 0 0 M hs hy x
  have h1 := signedMomentSum_height_bound 0 1 M hs hy x
  have hr0 := root0_norm y
  have hr1 := root1_norm_le_root0 hy
  have hmass0 := heightMomentMass_nonneg 0 0 M
  have hmass1 := heightMomentMass_nonneg 0 1 M
  have hmass : 0 ≤ heightMomentMass 0 0 M + heightMomentMass 0 1 M :=
    add_nonneg (heightMomentMass_nonneg 0 0 M) (heightMomentMass_nonneg 0 1 M)
  calc
    _ ≤ ‖2 * root1 y * signedMomentSum 0 0 s y x‖ +
        ‖2 * root0 y * signedMomentSum 0 1 s y x‖ := norm_add_le _ _
    _ = 2 * ‖root1 y‖ * ‖signedMomentSum 0 0 s y x‖ +
        2 * ‖root0 y‖ * ‖signedMomentSum 0 1 s y x‖ := by
      simp only [norm_mul, Complex.norm_ofNat]
    _ ≤ 2 * Real.sqrt y * ((2 * Real.exp (-(3 * Real.pi / 4) * y)) * heightMomentMass 0 0 M) +
        2 * Real.sqrt y * ((2 * Real.exp (-(3 * Real.pi / 4) * y)) * heightMomentMass 0 1 M) := by
      rw [hr0]
      gcongr
    _ = (4 * (heightMomentMass 0 0 M + heightMomentMass 0 1 M)) *
        (Real.sqrt y * Real.exp (-(3 * Real.pi / 4) * y)) := by ring
    _ ≤ (4 * (heightMomentMass 0 0 M + heightMomentMass 0 1 M)) *
        ((4 / Real.pi) * Real.exp (-(Real.pi / 2) * y)) :=
      mul_le_mul_of_nonneg_left (sqrt_height_exponential_absorption hy) (by positivity)
    _ ≤ _ := by
      unfold derivativeTailConstant
      nlinarith [Real.exp_pos (-(Real.pi / 2) * y)]

/-- The bound concerns the ACTUAL derivative, not a formal jet supplied
as a premise. Both exact constant-term derivatives are subtracted. -/
theorem completedActual_chart_derivative_remainder_bound (M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖deriv (fun v : ℝ => completedEisensteinFourier s v x) y -
      deriv (fun v : ℝ => completedConstant v s) y‖ ≤
      derivativeTailConstant M * Real.exp (-(Real.pi / 2) * y) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  rw [(completedFourier_hasDerivAt_y s hs0 hs1 y x hy0).deriv,
    (completedConstant_hasDerivAt s hs0 hs1 hy0).deriv,
    completedFourierY, add_sub_cancel_left]
  exact weightedKernelY_height_bound M hs hy x

end
end ImbalancedChen.Part3.ActualEisensteinHeightDerivativeTail20261026b

