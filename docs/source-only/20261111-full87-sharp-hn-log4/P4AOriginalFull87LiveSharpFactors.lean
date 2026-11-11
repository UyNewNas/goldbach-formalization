import ImbalancedChen.P4AOriginalFull87SharpFrozenLog4
import ImbalancedChen.ActualSmallRoughAttachment
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The ORIGINAL sixth-minus-eighth signed full-q physical coefficient is
NONZERO only if at least one of its own policy coefficients is genuinely
nonzero. Importantly, the displayed full-q support can contain zero
coefficients above its level; hence support alone does not license the
sharp-prime PP modulus bound. We recover the actual small/rough factorization
for the LIVE side(s), including the strict original small-factor cap and
a genuinely nonzero corresponding rough first-exit coefficient.

This is a local internal source adaptation, not a new free PP weight class,
not an unproved high-level bound and not a sharp-PP application.
-/

namespace ImbalancedChen.P4AOriginalFull87LiveSharpFactors
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87LicensedSixthPolicy
open P4AOriginalFull87SignedSharpReceiver (full87PhysicalRhoChange)

/-- A nonzero original OLD-minus-NEW coefficient cannot arise solely from
the zero-valued entries displayed in either original physical carrier. -/
theorem original_full87_rho_change_ne_zero_old_or_new
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (d : ℕ)
    (hd : full87PhysicalRhoChange r n e q om N cap w z L d ≠ 0) :
    actualSmallRoughRho
        ((sixthPolicy n e q om (N : ℝ)) false) N cap w z L d ≠ 0 ∨
      actualSmallRoughRho
        ((policy (width r) n e q om (N : ℝ)) false) N cap w z L d ≠ 0 := by
  by_contra hzero
  have h6 : actualSmallRoughRho
        ((sixthPolicy n e q om (N : ℝ)) false) N cap w z L d = 0 := by
    by_contra h
    exact hzero (Or.inl h)
  have h8 : actualSmallRoughRho
        ((policy (width r) n e q om (N : ℝ)) false) N cap w z L d = 0 := by
    by_contra h
    exact hzero (Or.inr h)
  apply hd
  unfold full87PhysicalRhoChange
  simp [h6, h8]

/-- ORIGINAL complete-modulus factorization, only for genuinely LIVE
sixth-minus-eighth coefficients.  It uses the actual small Rosser support,
the corresponding policy's actual first-exit rough support, the ORIGINAL
strict small-factor level L, and the nonzero rough weight condition.
Neither continuation is assigned the other policy's mask. -/
theorem original_full87_live_change_has_original_factor
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (d : ℕ)
    (hd : full87PhysicalRhoChange r n e q om N cap w z L d ≠ 0) :
    (∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ b ∈ fixedRoughSupport
          ((sixthPolicy n e q om (N : ℝ)) false) N cap w z,
        d = a * b ∧ (a : ℝ) < L ∧
          fixedRoughCoefficient
            ((sixthPolicy n e q om (N : ℝ)) false) N cap w z b ≠ 0)
    ∨
    (∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ b ∈ fixedRoughSupport
          ((policy (width r) n e q om (N : ℝ)) false) N cap w z,
        d = a * b ∧ (a : ℝ) < L ∧
          fixedRoughCoefficient
            ((policy (width r) n e q om (N : ℝ)) false) N cap w z b ≠ 0) := by
  rcases original_full87_rho_change_ne_zero_old_or_new
    r n e q om N cap w z L d hd with h6 | h8
  · left
    exact actualSmallRoughRho_ne_zero_factors
      ((sixthPolicy n e q om (N : ℝ)) false) N cap w z L h6
  · right
    exact actualSmallRoughRho_ne_zero_factors
      ((policy (width r) n e q om (N : ℝ)) false) N cap w z L h8

end
end ImbalancedChen.P4AOriginalFull87LiveSharpFactors
