import ImbalancedChen.Part3ZeroModeWeakOpenHalfLine
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

A constructed weak representative whose weak derivative has a continuous
representative is genuinely C1. The proof differentiates its proved finite
FTC, after replacing the weak coordinate a.e. by that continuous function.
The complex-conjugated compact-test ABI is reduced to the real-test ABI.
-/

namespace ImbalancedChen.Part3.WeakHalfLineClassicalDerivative20261026b
noncomputable section
open MeasureTheory Set Filter
open ZeroModeWeakOpenHalfLine20261026b

/-- The scalar real-test ABI follows from the actual conjugated complex-test
identity by selecting real-valued complex tests. -/
theorem weak_real_tests_of_complex_tests {U : Set ℝ} {f g : ℝ → ℂ}
    (hweak : ∀ φ : ℝ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ x, star (deriv φ x) * f x) = -(∫ x, star (φ x) * g x)) :
    ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      (∫ x, deriv ψ x • f x) = -(∫ x, ψ x • g x) := by
  intro ψ hψ hψc hψs
  let φ : ℝ → ℂ := Complex.ofRealCLM ∘ ψ
  have hφ : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp hψ
  have hφc : HasCompactSupport φ := hψc.comp_left rfl
  have hφs : tsupport φ ⊆ U := (tsupport_comp_subset rfl ψ).trans hψs
  have hd (x : ℝ) : deriv φ x = (deriv ψ x : ℂ) :=
    ((hψ.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv
  have h := hweak φ hφ hφc hφs
  simpa only [hd, φ, Function.comp_apply, Complex.reCLM_apply,
    Complex.ofRealCLM_apply, Complex.star_def, Complex.conj_ofReal, Complex.real_smul] using h

theorem OpenHalfLineSobolevRepresentative.hasDerivAt_of_continuous_coordinate
    {Y : ℝ} {f g v : ℝ → ℂ} (u : OpenHalfLineSobolevRepresentative Y f g)
    (hv : ContinuousOn v (Ioi Y))
    (hgv : ∀ᵐ x, x ∈ Ioi Y → g x = v x) :
    ∀ x ∈ Ioi Y, HasDerivAt u.function (v x) x := by
  intro x hx
  have hint (y : ℝ) (hy : Y < y) :
      (∫ t in x..y, g t) = ∫ t in x..y, v t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hgv] with t ht hti
    have htu : t ∈ uIcc x y := uIoc_subset_uIcc hti
    exact ht (lt_of_lt_of_le (lt_min hx hy) htu.1)
  have hnative : HasDerivAt (fun y => u.function x + ∫ t in x..y, v t) (v x) x := by
    have hi := intervalIntegral.integral_hasDerivAt_right
      (IntervalIntegrable.refl : IntervalIntegrable v volume x x)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hv x hx)
      (hv.continuousAt (isOpen_Ioi.mem_nhds hx))
    simpa only [zero_add] using (hasDerivAt_const x (u.function x)).add hi
  apply hnative.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  have h := u.fundamental x y hx hy
  rw [hint y hy] at h
  exact ((sub_eq_iff_eq_add).mp h).trans (add_comm _ _)

theorem OpenHalfLineSobolevRepresentative.contDiffOn_one_of_continuous_coordinate
    {Y : ℝ} {f g v : ℝ → ℂ} (u : OpenHalfLineSobolevRepresentative Y f g)
    (hv : ContinuousOn v (Ioi Y))
    (hgv : ∀ᵐ x, x ∈ Ioi Y → g x = v x) :
    ContDiffOn ℝ 1 u.function (Ioi Y) := by
  have hd := OpenHalfLineSobolevRepresentative.hasDerivAt_of_continuous_coordinate u hv hgv
  apply (contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn).mpr
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, ?_⟩
  apply hv.congr
  intro x hx
  rw [derivWithin_of_isOpen isOpen_Ioi hx]
  exact (hd x hx).deriv

end
end ImbalancedChen.Part3.WeakHalfLineClassicalDerivative20261026b
