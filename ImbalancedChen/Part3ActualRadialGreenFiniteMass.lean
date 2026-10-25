import ImbalancedChen.Part3GeneralActualRadialGreen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Exact finite-interval weighted mass for the actual general-order I/K Green
kernel. The potential, both ODEs, the C² branches, and the normalized source
Wronskian are actual imported theorems. No boundary-flux or integral bound is
assumed. Endpoint decay is a separate input still required for an improper
whole-line mass theorem; no Schur bound is asserted in this finite module.
-/

namespace ImbalancedChen.Part3.ActualRadialGreenFiniteMass20261025a

noncomputable section
open Set MeasureTheory
open GeneralActualRadialGreenSourceOnly ComplexOrderKRadialRegularitySourceOnly
open ComplexCompactGreenGluingSourceOnly

private theorem derivative_C1 {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (deriv f) := by
  have h : ContDiff ℝ ((1 : ℕ∞ω) + 1) f := by simpa using hf
  exact (contDiff_succ_iff_deriv.mp h).2.2

theorem potential_continuous (nu : ℂ) : Continuous (potential nu) := by
  unfold potential
  fun_prop

theorem actual_radialI_second_derivative {nu : ℂ} (hnu : -1 < nu.re) (r : ℝ) :
    deriv (deriv (radialI nu)) r = potential nu r * radialI nu r := by
  have h := actual_radialI_homogeneous hnu r
  unfold operator at h
  linear_combination -h

theorem actual_radialK_second_derivative (nu : ℂ) (r : ℝ) :
    deriv (deriv (radialK nu)) r = potential nu r * radialK nu r := by
  have h := actual_radialK_homogeneous nu r
  unfold operator at h
  linear_combination -h

theorem integral_potential_radialI {nu : ℂ} (hnu : -1 < nu.re) (a b : ℝ) :
    (∫ r in a..b, potential nu r * radialI nu r) =
      deriv (radialI nu) b - deriv (radialI nu) a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro r _
    simpa only [actual_radialI_second_derivative hnu r] using
      (((derivative_C1 (radialI_C2 hnu)).differentiable_one r).hasDerivAt)
  · exact ((potential_continuous nu).mul (radialI_C2 hnu).continuous).intervalIntegrable a b

theorem integral_potential_radialK (nu : ℂ) (a b : ℝ) :
    (∫ r in a..b, potential nu r * radialK nu r) =
      deriv (radialK nu) b - deriv (radialK nu) a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro r _
    simpa only [actual_radialK_second_derivative nu r] using
      (((derivative_C1 (radialK_C2 nu)).differentiable_one r).hasDerivAt)
  · exact ((potential_continuous nu).mul (radialK_C2 nu).continuous).intervalIntegrable a b

theorem actualGreen_left_branch (nu : ℂ) {s r : ℝ} (hr : r ≤ s) :
    actualRadialGreen nu s r = radialI nu r * radialK nu s := by
  simp only [actualRadialGreen, kernel, min_eq_left hr, max_eq_right hr]

theorem actualGreen_right_branch (nu : ℂ) {s r : ℝ} (hr : s ≤ r) :
    actualRadialGreen nu s r = radialI nu s * radialK nu r := by
  simp only [actualRadialGreen, kernel, min_eq_right hr, max_eq_left hr]

theorem integral_potential_actualGreen_left {nu : ℂ} (hnu : -1 < nu.re)
    {a s : ℝ} (has : a ≤ s) :
    (∫ r in a..s, potential nu r * actualRadialGreen nu s r) =
      radialK nu s * (deriv (radialI nu) s - deriv (radialI nu) a) := by
  calc
    _ = ∫ r in a..s, radialK nu s * (potential nu r * radialI nu r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hrs : r ≤ s := by
        rw [uIcc_of_le has] at hr
        exact hr.2
      rw [actualGreen_left_branch nu hrs]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_potential_radialI hnu]

theorem integral_potential_actualGreen_right {nu : ℂ} {s b : ℝ} (hsb : s ≤ b) :
    (∫ r in s..b, potential nu r * actualRadialGreen nu s r) =
      radialI nu s * (deriv (radialK nu) b - deriv (radialK nu) s) := by
  calc
    _ = ∫ r in s..b, radialI nu s * (potential nu r * radialK nu r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hsr : s ≤ r := by
        rw [uIcc_of_le hsb] at hr
        exact hr.1
      rw [actualGreen_right_branch nu hsr]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_potential_radialK]

/-- The exact source mass and both literal remote fluxes. In particular the
right flux has a plus sign and the left flux has a minus sign. -/
theorem actualGreen_finite_weighted_mass {nu : ℂ}
    (hnu : 0 < nu.re) (hnuUpper : nu.re < 1)
    {a s b : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    (∫ r in a..b, potential nu r * actualRadialGreen nu s r) =
      1 + radialI nu s * deriv (radialK nu) b -
        radialK nu s * deriv (radialI nu) a := by
  have hi : -1 < nu.re := by linarith
  have hc : Continuous (fun r : ℝ => potential nu r * actualRadialGreen nu s r) :=
    (potential_continuous nu).mul (actualRadialGreen_continuous hi s)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a s) (hc.intervalIntegrable s b),
    integral_potential_actualGreen_left hi has,
    integral_potential_actualGreen_right hsb]
  have hw := actual_radial_source_wronskian hnu hnuUpper s
  linear_combination hw

end
end ImbalancedChen.Part3.ActualRadialGreenFiniteMass20261025a
