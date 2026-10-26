import ImbalancedChen.Part3WeakEulerInverseSquareLocalL2

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Genuine one-dimensional weak Euler data become a classical C2/C1 pair.
The first and second weak coordinates are separately constructed as local
AC representatives. Their proved finite FTC identities, with continuous
right sides, supply actual classical derivatives. Y=0 is permitted on the
OPEN positive half-line: no lower endpoint trace/admissibility is asserted.
-/

namespace ImbalancedChen.Part3.WeakEulerClassicalPair20261026b
noncomputable section
open MeasureTheory Set Filter
open ZeroModeWeakOpenHalfLine20261026b
open WeakHalfLineClassicalDerivative20261026b WeakEulerInverseSquareLocalL220261026b

structure ClassicalWeakEulerPair (Y : ℝ) (M G : ℝ → ℂ) where
  mean : ℝ → ℂ
  gradient : ℝ → ℂ
  mean_ae : ∀ᵐ y, y ∈ Ioi Y → M y = mean y
  gradient_ae : ∀ᵐ y, y ∈ Ioi Y → G y = gradient y
  mean_C2 : ContDiffOn ℝ 2 mean (Ioi Y)
  gradient_C1 : ContDiffOn ℝ 1 gradient (Ioi Y)
  mean_derivative : ∀ y ∈ Ioi Y, HasDerivAt mean (gradient y) y
  gradient_derivative : ∀ y ∈ Ioi Y, HasDerivAt gradient (mean y / (y : ℂ) ^ 2) y
  mean_second_derivative : ∀ y ∈ Ioi Y, deriv (deriv mean) y = mean y / (y : ℂ) ^ 2

/-- The only derivative inputs are the literal compact-test weak identities. -/
theorem nonempty_classicalWeakEulerPair {Y : ℝ} (hY : 0 ≤ Y) {M G : ℝ → ℂ}
    (hloc : ∀ a b, Y < a → a < b →
      MemLp M 2 (volume.restrict (Ioo a b)) ∧ MemLp G 2 (volume.restrict (Ioo a b)))
    (hMG : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi Y →
      (∫ y, deriv ψ y • M y) = -(∫ y, ψ y • G y))
    (hGH : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi Y →
      (∫ y, deriv ψ y • G y) = -(∫ y, ψ y • inverseSquareRhs M y)) :
    Nonempty (ClassicalWeakEulerPair Y M G) := by
  let u : OpenHalfLineSobolevRepresentative Y M G :=
    Classical.choice (nonempty_openHalfLineSobolevRepresentative hloc hMG)
  have hlocG : ∀ a b, Y < a → a < b →
      MemLp G 2 (volume.restrict (Ioo a b)) ∧
        MemLp (inverseSquareRhs M) 2 (volume.restrict (Ioo a b)) := by
    intro a b ha hab
    exact ⟨(hloc a b ha hab).2,
      local_memLp_inverseSquareRhs (lt_of_le_of_lt hY ha) (hloc a b ha hab).1⟩
  let v : OpenHalfLineSobolevRepresentative Y G (inverseSquareRhs M) :=
    Classical.choice (nonempty_openHalfLineSobolevRepresentative hlocG hGH)
  have hMd : ∀ y ∈ Ioi Y, HasDerivAt u.function (v.function y) y :=
    OpenHalfLineSobolevRepresentative.hasDerivAt_of_continuous_coordinate
      u v.continuous v.value_ae
  have hHcont : ContinuousOn (inverseSquareRhs u.function) (Ioi Y) :=
    continuousOn_inverseSquareRhs hY u.continuous
  have hHae : ∀ᵐ y, y ∈ Ioi Y → inverseSquareRhs M y = inverseSquareRhs u.function y :=
    inverseSquareRhs_ae_of_value_ae u.value_ae
  have hGd : ∀ y ∈ Ioi Y, HasDerivAt v.function (inverseSquareRhs u.function y) y :=
    OpenHalfLineSobolevRepresentative.hasDerivAt_of_continuous_coordinate v hHcont hHae
  have hGC1 : ContDiffOn ℝ 1 v.function (Ioi Y) :=
    OpenHalfLineSobolevRepresentative.contDiffOn_one_of_continuous_coordinate v hHcont hHae
  have hMdEq : EqOn (deriv u.function) v.function (Ioi Y) :=
    fun y hy => (hMd y hy).deriv
  have hMC2 : ContDiffOn ℝ 2 u.function (Ioi Y) := by
    rw [show (2 : ℕ∞ω) = 1 + 1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => (hMd y hy).differentiableAt.differentiableWithinAt, ?_,
      hGC1.congr hMdEq⟩
    intro hn
    norm_num at hn
  have hMdd (y : ℝ) (hy : y ∈ Ioi Y) :
      deriv (deriv u.function) y = inverseSquareRhs u.function y := by
    have heq : deriv u.function =ᶠ[𝓝 y] v.function := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
      exact hMdEq hz
    exact heq.deriv_eq.trans (hGd y hy).deriv
  exact ⟨{
    mean := u.function
    gradient := v.function
    mean_ae := u.value_ae
    gradient_ae := v.value_ae
    mean_C2 := hMC2
    gradient_C1 := hGC1
    mean_derivative := hMd
    gradient_derivative := hGd
    mean_second_derivative := hMdd }⟩

/-- Actual complex-conjugated weak test ABI, with no change in the ordinary
dy gradient coordinate. -/
theorem nonempty_classicalWeakEulerPair_of_complex_tests {Y : ℝ} (hY : 0 ≤ Y)
    {M G : ℝ → ℂ}
    (hloc : ∀ a b, Y < a → a < b →
      MemLp M 2 (volume.restrict (Ioo a b)) ∧ MemLp G 2 (volume.restrict (Ioo a b)))
    (hMG : ∀ φ : ℝ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioi Y →
      (∫ y, star (deriv φ y) * M y) = -(∫ y, star (φ y) * G y))
    (hGH : ∀ φ : ℝ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioi Y →
      (∫ y, star (deriv φ y) * G y) = -(∫ y, star (φ y) * (M y / (y : ℂ) ^ 2))) :
    Nonempty (ClassicalWeakEulerPair Y M G) :=
  nonempty_classicalWeakEulerPair hY hloc
    (weak_real_tests_of_complex_tests hMG) (weak_real_tests_of_complex_tests hGH)

/-- The first-order weak identity and the second-order mean equation derive
the gradient's weak derivative by testing the first identity with φ'. -/
theorem weak_gradient_identity_of_first_and_second {U : Set ℝ} {M G H : ℝ → ℂ}
    (hMG : ∀ φ : ℝ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ y, star (deriv φ y) * M y) = -(∫ y, star (φ y) * G y))
    (hsecond : ∀ φ : ℝ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ y, star (deriv (deriv φ) y) * M y) = ∫ y, star (φ y) * H y) :
    ∀ φ : ℝ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ y, star (deriv φ y) * G y) = -(∫ y, star (φ y) * H y) := by
  intro φ hφ hφc hφs
  have hder := hMG (deriv φ) (contDiff_infty_iff_deriv.mp hφ).2 hφc.deriv
    (tsupport_deriv_subset.trans hφs)
  have hs := hsecond φ hφ hφc hφs
  linear_combination hder - hs

/-- Direct actual mean-pair ABI used by the cylinder Riesz/mean construction:
the gradient relation and second test identity suffice, including Y=0. -/
theorem nonempty_classicalWeakEulerPair_of_first_and_second {Y : ℝ} (hY : 0 ≤ Y)
    {M G : ℝ → ℂ}
    (hloc : ∀ a b, Y < a → a < b →
      MemLp M 2 (volume.restrict (Ioo a b)) ∧ MemLp G 2 (volume.restrict (Ioo a b)))
    (hMG : ∀ φ : ℝ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioi Y →
      (∫ y, star (deriv φ y) * M y) = -(∫ y, star (φ y) * G y))
    (hsecond : ∀ φ : ℝ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioi Y →
      (∫ y, star (deriv (deriv φ) y) * M y) =
        ∫ y, star (φ y) * (M y / (y : ℂ) ^ 2)) :
    Nonempty (ClassicalWeakEulerPair Y M G) :=
  nonempty_classicalWeakEulerPair_of_complex_tests hY hloc hMG
    (weak_gradient_identity_of_first_and_second hMG hsecond)

end
end ImbalancedChen.Part3.WeakEulerClassicalPair20261026b
