import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual principal-power control of the angular J Abel rate epsilon-i*u.
For nonzero u the rate power has an explicit |u|^(-Re a) majorant and
converges to the literal imaginary-axis power as epsilon tends to zero.
There is no pointwise assertion at u=0 and no hidden branch replacement.
-/

namespace ImbalancedChen.Part3.ActualJAngularAbelRateBound20261026b

noncomputable section
open Complex Filter
open scoped Topology

theorem angularAbelRate_ne_zero (epsilon : ℝ) {u : ℝ} (hu : u ≠ 0) :
    (epsilon : ℂ) - I * (u : ℂ) ≠ 0 := by
  intro hz
  have him := congrArg Complex.im hz
  have he : -u = 0 := by simpa using him
  exact hu (neg_eq_zero.mp he)

theorem angularAbelRate_norm_lower (epsilon u : ℝ) :
    |u| ≤ ‖(epsilon : ℂ) - I * (u : ℂ)‖ := by
  simpa using Complex.abs_im_le_norm ((epsilon : ℂ) - I * (u : ℂ))

/-- Uniform in the Abel parameter. The angular origin is explicitly
excluded; no pointwise bound at u=0 is claimed. -/
theorem angularAbelRate_power_norm_le {a : ℂ} (ha : 0 < a.re)
    (epsilon : ℝ) {u : ℝ} (hu : u ≠ 0) :
    ‖((epsilon : ℂ) - I * (u : ℂ)) ^ (-a)‖ ≤
      Real.exp (Real.pi * |a.im|) * |u| ^ (-a.re) := by
  let z : ℂ := (epsilon : ℂ) - I * (u : ℂ)
  have hz : z ≠ 0 := angularAbelRate_ne_zero epsilon hu
  have hp : ‖z‖ ^ (-a.re) ≤ |u| ^ (-a.re) :=
    Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hu)
      (angularAbelRate_norm_lower epsilon u) (neg_nonpos.mpr ha.le)
  have hphase : Complex.arg z * a.im ≤ Real.pi * |a.im| := by
    calc
      Complex.arg z * a.im ≤ |Complex.arg z * a.im| := le_abs_self _
      _ = |Complex.arg z| * |a.im| := abs_mul _ _
      _ ≤ Real.pi * |a.im| :=
        mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi z) (abs_nonneg _)
  change ‖z ^ (-a)‖ ≤ _
  rw [Complex.norm_cpow_of_ne_zero hz, Complex.neg_re, Complex.neg_im,
    show Complex.arg z * -a.im = -(Complex.arg z * a.im) by ring,
    Real.exp_neg, div_inv_eq_mul]
  calc
    ‖z‖ ^ (-a.re) * Real.exp (Complex.arg z * a.im) ≤
        |u| ^ (-a.re) * Real.exp (Real.pi * |a.im|) :=
      mul_le_mul hp (Real.exp_le_exp.mpr hphase) (Real.exp_pos _).le
        (Real.rpow_nonneg (abs_nonneg u) _)
    _ = Real.exp (Real.pi * |a.im|) * |u| ^ (-a.re) := mul_comm _ _

/-- Pointwise angular Abel convergence is proved at every nonzero angular
variable by actual cpow continuity on the principal slit plane. -/
theorem angularAbelRate_power_tendsto (a : ℂ) {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun epsilon : ℝ => ((epsilon : ℂ) - I * (u : ℂ)) ^ (-a))
      (𝓝 0) (𝓝 ((-(I * (u : ℂ))) ^ (-a))) := by
  have hz : (-(I * (u : ℂ))) ∈ Complex.slitPlane := by
    right
    simpa using (neg_ne_zero.mpr hu)
  have hc : ContinuousAt (fun epsilon : ℝ =>
      ((epsilon : ℂ) - I * (u : ℂ)) ^ (-a)) 0 :=
    (Complex.continuousAt_cpow_const hz).comp (by fun_prop)
  simpa only [Complex.ofReal_zero, zero_sub] using hc.tendsto

end
end ImbalancedChen.Part3.ActualJAngularAbelRateBound20261026b
