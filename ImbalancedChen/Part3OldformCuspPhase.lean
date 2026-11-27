import ImbalancedChen.Part3SignedCuspFourierSection

namespace ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly

/-- Signed cusp conversion plus the coprime ABL oldform phase. This is
only their exact scalar cancellation, not an assumed packet spectral theorem. -/
theorem signed_cusp_phase_cancel (eta A nu n z : ℝ) :
    (-eta*A*(nu*n)/z) + (eta*n*(A*nu-1)/z) = -eta*n/z := by
  ring

end ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly

namespace ImbalancedChen.Part3.OldformCuspPhase

open P3Period64NativeReconstructionSourceOnly (e e_add)
open P3ActualLiteralPacketIntegralSourceOnly (cuspPhase)
open ActualCuspFourierSectionSourceOnly (oldFourierCoeff newFourierCoeff)
open scoped MatrixGroups UpperHalfPlane

/-- The product of the two scalar phases reduces to the opposite cusp phase. -/
theorem oldform_cusp_phase_mul (eta A nu n z : ℝ) :
    e (-eta*A*(nu*n)/z) * e (eta*n*(A*nu-1)/z) = e (-eta*n/z) := by
  rw [← e_add, ActualPoissonNormalizedFSourceOnly.signed_cusp_phase_cancel]

theorem oldform_cusp_phase_mul_signed (negative : Bool) (A nu : ℝ) (N n : ℕ) :
    let eta : ℝ := if negative then -1 else 1
    e (-eta*A*(nu*n)/N) * e (eta*n*(A*nu-1)/N) = cuspPhase negative N n := by
  dsimp only
  rw [oldform_cusp_phase_mul]
  cases negative <;> simp [cuspPhase]

/-- The scalar identity paired with the two fixed-height cusp sections. -/
theorem oldform_cusp_phase_mul_oldFourierCoeff
    (negative : Bool) (A nu : ℝ) (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ w : ℍ, f (γ • w) = f w) (y : ℝ) (hy : 0 < y) (n : ℕ) :
    let eta : ℝ := if negative then -1 else 1
    e (-eta*A*(nu*n)/N) * e (eta*n*(A*nu-1)/N) *
        oldFourierCoeff N hN f hfΓ y hy (if negative then -(n : ℤ) else (n : ℤ)) =
      newFourierCoeff N hN f hfΓ y hy (if negative then -(n : ℤ) else (n : ℤ)) := by
  dsimp only
  rw [oldform_cusp_phase_mul_signed negative A nu N n]
  exact OriginalSignedNativeCuspFourier20261102.cuspPhase_cancels_actual_section_signed
    negative N hN f hfΓ y hy n

end ImbalancedChen.Part3.OldformCuspPhase
