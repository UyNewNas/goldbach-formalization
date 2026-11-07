import ImbalancedChen.Part3ActualGreenBoundaryMajorant
import ImbalancedChen.Part3ActualKLCompactTestIntegrationByParts

/-!
The actual raw K transform dictionary and diagonal boundary normalization.
The spectral parameter is tau, the order is i*tau, and the density here is
with respect to lambda=tau^2. No equality of spectral measures is assumed.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualGreenBoundaryDiagonal20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ComplexOrderKBridgeSourceOnly ComplexOrderKRadialRegularitySourceOnly
open ActualGreenBoundaryMajorant20261025a ActualGreenPairingHolomorphy20261025a
open ActualKLCompactTestIntegrationByParts20261025a

theorem rawRadialKTransform_eq_actualKtransform (f : ℝ → ℂ) (tau : ℝ) :
    rawRadialKTransform f tau = actualKtransform f tau := by
  unfold rawRadialKTransform actualKtransform radialK
  apply integral_congr_ae
  exact Eventually.of_forall (fun r => mul_comm _ _)

theorem complexOrderK_imaginary_star (tau q : ℝ) :
    star (complexOrderK ((tau : ℂ) * Complex.I) q) =
      complexOrderK ((tau : ℂ) * Complex.I) q := by
  have h := complexOrderK_imaginary (tau / 2) q
  rw [show 2 * (tau / 2) = tau by ring] at h
  rw [h]
  simp

theorem rawRadialKTransform_star (f : ℝ → ℂ) (tau : ℝ) :
    rawRadialKTransform (fun r => star (f r)) tau = star (rawRadialKTransform f tau) := by
  unfold rawRadialKTransform
  calc
    _ = ∫ r : ℝ, star (complexOrderK ((tau : ℂ) * Complex.I) (Real.exp r) * f r) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun r => by
        simp only [star_mul, complexOrderK_imaginary_star]
        <;> ring)
    _ = _ := integral_conj

theorem hasCompactSupport_star {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun r => star (f r)) := by
  apply HasCompactSupport.intro hf.isCompact
  intro r hr
  simp only [image_eq_zero_of_notMem_tsupport hr, star_zero]

/-- Exact normalized diagonal jump in the lambda variable. The transform
is the already defined literal actualKtransform, not a renamed supplier. -/
theorem actualGreenPairing_normalized_diagonal_jump {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (tau : ℝ) :
    (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (actualGreenPairing f (fun r => star (f r)) (-((tau : ℂ) * Complex.I)) -
          actualGreenPairing f (fun r => star (f r)) ((tau : ℂ) * Complex.I)) =
      ((Real.sinh (Real.pi * tau) / Real.pi ^ 2 *
        ‖actualKtransform f tau‖ ^ 2 : ℝ) : ℂ) := by
  rw [actualGreenPairing_boundary_jump hf hf.star hfc (hasCompactSupport_star hfc),
    rawRadialKTransform_star]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hnorm (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.normSq_eq_norm_sq] using Complex.mul_conj z
  rw [mul_assoc
    (2 * (Real.sinh (Real.pi * tau) : ℂ) * Complex.I / (Real.pi : ℂ)), hnorm,
    rawRadialKTransform_eq_actualKtransform]
  push_cast
  field_simp [hp, Complex.I_ne_zero]
  <;> ring

end
end ImbalancedChen.Part3.ActualGreenBoundaryDiagonal20261025a
