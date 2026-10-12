import ImbalancedChen.Part3LongSlotDistribution
import ImbalancedChen.BoundaryArbitraryLog

/-!
# The one-long error on the current manuscript's normalization

The elementary error is `2*M*D` for one-bounded short coefficients and
physical modulus weights.  A strict bound on this *actual product of
lengths* supplies arbitrary logarithmic accuracy and negligible error on
`singularNormalization N`, with one threshold before all boxes, intervals,
moving residues and coefficients.  No distribution premise is used.

For the frozen one-long branch the remaining insertion task is to derive
the displayed length product bound from `20*zeta + Theta_loc < 1` after
the stated short-factor and Brun costs, and to restore its chart-rough
long slot.  This module does not assert that those steps are already done.
-/

namespace ImbalancedChen

noncomputable section

open Filter
open scoped BigOperators

/-- Uniform arbitrary logarithmic accuracy for the literal long-slot
discrepancy once its short-length times physical-modulus cap has a fixed
power gap.  The interval and residue are unrestricted natural numbers. -/
theorem part3_eventually_longSlot_logAccuracy
    (theta : ℝ) (htheta : theta < 1) (K : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ M D L U a : ℕ, ∀ alpha rho : ℕ → ℂ,
      (M : ℝ) * (D : ℝ) ≤ (N : ℝ) ^ theta →
      (∀ m ∈ Finset.Icc 1 M, ‖alpha m‖ ≤ 1) →
      (∀ q ∈ (Finset.Icc 1 D).filter (fun q => a.Coprime q), ‖rho q‖ ≤ 1) →
      ‖part3LongSlotSignedError (Finset.Icc 1 M)
        ((Finset.Icc 1 D).filter (fun q => a.Coprime q)) alpha rho L U a‖ ≤
          epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ K := by
  filter_upwards [eventually_powerLog_le_logAccuracy
    2 theta 0 K htheta epsilon hepsilon] with N hN
  intro M D L U a alpha rho hMD halpha hrho
  calc
    _ ≤ 2 * (M : ℝ) * (D : ℝ) :=
      part3LongSlotSignedError_norm_le_box M D L U a alpha rho halpha hrho
    _ ≤ 2 * (N : ℝ) ^ theta := by nlinarith only [hMD]
    _ ≤ epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ K := by simpa using hN

/-- The exact same arithmetic error is negligible on the manuscript's
actual singular-series scale; its uniform positivity is already proved. -/
theorem part3_eventually_longSlot_singularNormalization
    (theta : ℝ) (htheta : theta < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ M D L U a : ℕ, ∀ alpha rho : ℕ → ℂ,
      (M : ℝ) * (D : ℝ) ≤ (N : ℝ) ^ theta →
      (∀ m ∈ Finset.Icc 1 M, ‖alpha m‖ ≤ 1) →
      (∀ q ∈ (Finset.Icc 1 D).filter (fun q => a.Coprime q), ‖rho q‖ ≤ 1) →
      ‖part3LongSlotSignedError (Finset.Icc 1 M)
        ((Finset.Icc 1 D).filter (fun q => a.Coprime q)) alpha rho L U a‖ ≤
          epsilon * singularNormalization N := by
  filter_upwards [eventually_powerLog_le_singularNormalization
    2 theta 0 htheta epsilon hepsilon] with N hN
  intro M D L U a alpha rho hMD halpha hrho
  calc
    _ ≤ 2 * (M : ℝ) * (D : ℝ) :=
      part3LongSlotSignedError_norm_le_box M D L U a alpha rho halpha hrho
    _ ≤ 2 * (N : ℝ) ^ theta := by nlinarith only [hMD]
    _ ≤ epsilon * singularNormalization N := by simpa using hN

end

end ImbalancedChen
