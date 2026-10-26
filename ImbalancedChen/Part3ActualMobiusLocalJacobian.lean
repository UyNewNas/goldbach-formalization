import ImbalancedChen.Part3ActualMobiusConformalTwoJet
import Mathlib.MeasureTheory.Function.Jacobian

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Actual scalar local change of variables for the native Mobius map.
The real Jacobian is computed from Mathlib's actual differential as
J_g(z)=1/|c*z+d|^4=normSq((c*z+d)^(-2)).  Injectivity on the positive
half-plane is derived from the actual inverse group action.  No local
composition continuity or weak-gradient covariance is assumed.
-/
namespace ImbalancedChen.Part3.ActualMobiusLocalJacobian20261026b
noncomputable section
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane
open ActualMobiusConformalTwoJet20261025a

def rawJacobian (g : SL(2, ℤ)) (z : ℂ) : ℝ :=
  1 / ‖UpperHalfPlane.denom (realMatrix g) z‖^4

theorem abs_det_actual_mobius (g : SL(2, ℤ)) (z : ℂ) :
    |(UpperHalfPlane.smulFDeriv (realMatrix g) z).det| = rawJacobian g z := by
  rw [UpperHalfPlane.det_smulFDeriv]
  have hdet : (realMatrix g).det.val = 1 := by simp [realMatrix]
  simp [hdet, rawJacobian, abs_of_nonneg (by positivity :
    0 ≤ 1/‖UpperHalfPlane.denom (realMatrix g) z‖^4)]

theorem rawJacobian_eq_normSq_factor (g : SL(2, ℤ)) (z : ℂ) :
    rawJacobian g z = Complex.normSq (factor g z) := by
  simp [rawJacobian,factor,Complex.normSq_div,Complex.normSq_eq_norm_sq,← pow_mul]

theorem rawJacobian_pos (g : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    0 < rawJacobian g z := by
  apply one_div_pos.mpr
  exact pow_pos (norm_pos_iff.mpr (denom_ne_zero g ⟨z,hz⟩)) 4

/-- The native actual map is injective on every positive chart subset. -/
theorem actualMobius_injOn_positive (g : SL(2, ℤ)) {K : Set ℂ}
    (hK : ∀ z ∈ K, 0 < z.im) : Set.InjOn (actualMobius g) K := by
  intro x hx y hy hxy
  let X : UpperHalfPlane := ⟨x,hK x hx⟩
  let Y : UpperHalfPlane := ⟨y,hK y hy⟩
  have haction : g • X = g • Y := by
    apply UpperHalfPlane.ext
    simpa only [← actualMobius_eq_smul] using hxy
  have hinv := congrArg (fun u : UpperHalfPlane => g⁻¹ • u) haction
  have hpoint : X = Y := by simpa only [inv_smul_smul] using hinv
  exact congrArg UpperHalfPlane.coe hpoint

/-- Exact native scalar Jacobian equality for arbitrary nonnegative
integrands, with no integrability hypothesis hiding the transport. -/
theorem actualMobius_lintegral_image (g : SL(2, ℤ)) {K : Set ℂ}
    (hKm : MeasurableSet K) (hKp : ∀ z ∈ K, 0 < z.im) (f : ℂ → ℝ≥0∞) :
    (∫⁻ w in actualMobius g '' K, f w) =
      ∫⁻ z in K, ENNReal.ofReal (rawJacobian g z)*f (actualMobius g z) := by
  have hd (z : ℂ) (hz : z ∈ K) :
      HasFDerivWithinAt (actualMobius g) (UpperHalfPlane.smulFDeriv (realMatrix g) z) K z := by
    let Z : UpperHalfPlane := ⟨z,hKp z hz⟩
    simpa only [actualMobius] using
      (UpperHalfPlane.hasStrictFDerivAt_smul (realMatrix g) Z).hasFDerivAt.hasFDerivWithinAt
  have hnative := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure ℂ) hKm hd (actualMobius_injOn_positive g hKp) f
  simpa only [abs_det_actual_mobius] using hnative

theorem actualMobius_integral_image (g : SL(2, ℤ)) {K : Set ℂ}
    (hKm : MeasurableSet K) (hKp : ∀ z ∈ K, 0 < z.im) (f : ℂ → ℂ) :
    (∫ w in actualMobius g '' K, f w) =
      ∫ z in K, rawJacobian g z • f (actualMobius g z) := by
  have hd (z : ℂ) (hz : z ∈ K) :
      HasFDerivWithinAt (actualMobius g) (UpperHalfPlane.smulFDeriv (realMatrix g) z) K z := by
    let Z : UpperHalfPlane := ⟨z,hKp z hz⟩
    simpa only [actualMobius] using
      (UpperHalfPlane.hasStrictFDerivAt_smul (realMatrix g) Z).hasFDerivAt.hasFDerivWithinAt
  have hnative := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure ℂ) hKm hd (actualMobius_injOn_positive g hKp) f
  simpa only [abs_det_actual_mobius] using hnative

/-- The actual inverse Jacobian has a produced compact upper bound.
This is the coefficient needed for value-L2 composition continuity. -/
theorem compact_inverseJacobian_bound (g : SL(2, ℤ)) {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z ∈ K, ‖UpperHalfPlane.denom (realMatrix g) z‖^4 ≤ C := by
  have hc : Continuous (fun z : ℂ => ‖UpperHalfPlane.denom (realMatrix g) z‖^4) := by
    unfold UpperHalfPlane.denom
    fun_prop
  obtain ⟨B,hB⟩ := hK.bddAbove_image hc.continuousOn
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro z hz
  exact (hB ⟨z,hz,rfl⟩).trans (le_max_right _ _)

end
end ImbalancedChen.Part3.ActualMobiusLocalJacobian20261026b
