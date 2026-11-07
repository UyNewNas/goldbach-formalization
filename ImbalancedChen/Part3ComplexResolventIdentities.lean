import ImbalancedChen.Part3ComplexContractionResolvent
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

The actual complex CFC graph resolvent obeys adjoint symmetry and the first
resolvent identity. Both are proved from the concrete scalar ratio on the
actual self-adjoint spectrum. This preserves the sign convention for
(A-z)^(-1) in a later Stone jump. No resolvent-law premise is introduced.
-/

namespace ImbalancedChen.Part3.ComplexResolventIdentities20261025a

noncomputable section
open Set
open ComplexContractionResolvent20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem ratio_star_real (z : ℂ) (t : ℝ) :
    star (complexResolventRatio z (t : ℂ)) = complexResolventRatio (star z) (t : ℂ) := by
  simp [complexResolventRatio, complexDenominator, star_sub, star_add, star_mul, star_div₀,
    mul_comm]

/-- Actual adjoint symmetry of the complex CFC graph resolvent. -/
theorem complexResolvent_star (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R) (z : ℂ) :
    star (complexResolvent R z) = complexResolvent R (star z) := by
  change star (cfc (complexResolventRatio z) R) = cfc (complexResolventRatio (star z)) R
  rw [← cfc_star]
  apply cfc_congr
  intro w hw
  rw [hSA.mem_spectrum_eq_re hw]
  exact ratio_star_real z w.re

private theorem ratio_resolvent_identity_real {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (t : ℝ) :
    complexResolventRatio z (t : ℂ) - complexResolventRatio w (t : ℂ) =
      (z - w) * complexResolventRatio z (t : ℂ) * complexResolventRatio w (t : ℂ) := by
  have hdZ := complexDenominator_real_ne_zero hz t
  have hdW := complexDenominator_real_ne_zero hw t
  dsimp only [complexResolventRatio, complexDenominator] at hdZ hdW ⊢
  field_simp [hdZ, hdW] <;> ring

/-- First resolvent identity with the actual (A-z)^(-1) sign convention. -/
theorem complexResolvent_first_identity (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    complexResolvent R z - complexResolvent R w =
      (z - w) • (complexResolvent R z * complexResolvent R w) := by
  have hzCont := complexResolventRatio_continuousOn R hSA hz
  have hwCont := complexResolventRatio_continuousOn R hSA hw
  calc
    complexResolvent R z - complexResolvent R w =
        cfc (fun t : ℂ => complexResolventRatio z t - complexResolventRatio w t) R := by
      rw [cfc_sub (hf := hzCont) (hg := hwCont)]
      rfl
    _ = cfc (fun t : ℂ => (z - w) * complexResolventRatio z t * complexResolventRatio w t) R := by
      apply cfc_congr
      intro t ht
      rw [hSA.mem_spectrum_eq_re ht]
      exact ratio_resolvent_identity_real hz hw t.re
    _ = (z - w) • (complexResolvent R z * complexResolvent R w) := by
      rw [cfc_mul (fun t : ℂ => (z - w) * complexResolventRatio z t)
        (complexResolventRatio w) R (continuousOn_const.mul hzCont) hwCont,
        cfc_const_mul (z - w) (complexResolventRatio z) R hzCont,
        smul_mul_assoc]
      rfl

end
end ImbalancedChen.Part3.ComplexResolventIdentities20261025a
