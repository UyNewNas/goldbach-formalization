import ImbalancedChen.P3HBUnsplitFrechetFourierAdmission
import ImbalancedChen.P3FourierActualInversion
import Mathlib.Tactic

/-!
P3.6 / frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
distribution-prime-product-completion-20261010 §4 (F), and original
signed PP/coprime-mean pairing in manuscript-body.tex (current-PP).

This connects the genuine fixed-six original HB group/slot/one-full-trim
weight to the genuine Fourier H-box error AND to the original finite
same-integer-rho signed-source ledger. It keeps the physical Q, source
occurrences, products and fullModulusMass, including product = T.
No assumption on a Fourier error, target PP estimate or modulus saving.

Only the fixed chosen smooth six-position geometry is admitted here.
The right-hand fullModulusMass still requires a complete arithmetic
payment; no uniform growing m(T) or all-W_T result is asserted.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBChosenSixSameRhoCutoff
noncomputable section

open MeasureTheory
open scoped Classical BigOperators FourierTransform
open ImbalancedChen.P3AffineTransitionJets
open ImbalancedChen.P3FourierDPointwise
open ImbalancedChen.P3FourierPointCoordinateBridge
open ImbalancedChen.P3FourierActualBoxTail
open ImbalancedChen.P3FourierActualInversion
open ImbalancedChen.P3FourierRestrictedBox
open ImbalancedChen.P3FullSignedModulusTail
open ImbalancedChen.P3HBUnsplitRealProfile
open ImbalancedChen.P3HBUnsplitRealFourierD
open ImbalancedChen.P3HBUnsplitFrechetFourierAdmission

/-- Genuine fixed-six original Fourier H-box tail. Unlike the generic
H-box theorem, no separate derivative-integrability or ContDiff
hypothesis remains: they come from the literal chosen smooth HB profile
with original repeated groups and one complete-product trim. -/
theorem chosen_six_fourier_Hbox_tail {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s H : ℝ) (hH : 0 < H) :
    (∫ eta in (fourierBox 6 H)ᶜ,
      ‖𝓕 (actualMixedFamily (realSixUnsplitWeight c J s) ∅) eta‖) ≤
      (6 : ℝ) * derivativeD 6
        (actualMixedFamily (realSixUnsplitWeight c J s)) / H := by
  exact actual_fourier_box_tail_bound (realSixUnsplitWeight c J s)
    (fun S => (chosen_chartLift_contDiff c J s).of_le (by simp))
    (fun S k hk => chosen_complexChartLift_iterated_integrable c J s k)
    H hH

/-- Actual Fourier inversion, for the original real six-position W,
at its true Euclidean frequency and the true physical 2π H-box.
This is a pointwise analytic estimate, not a PP discrepancy estimate. -/
theorem chosen_six_real_truncated_inverse_error {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s H : ℝ) (hH : 0 < H) (x : FourierSpace 6) :
    |realSixUnsplitWeight c J s (chartEquiv 6 x) -
      (actualTruncatedInverse (realSixUnsplitWeight c J s) H x).re| ≤
      (6 : ℝ) * derivativeD 6
        (actualMixedFamily (realSixUnsplitWeight c J s)) / H := by
  exact actual_real_truncated_inverse_error
    (realSixUnsplitWeight c J s)
    (fun S => (chosen_chartLift_contDiff c J s).of_le (by simp))
    (fun S k hk => chosen_complexChartLift_iterated_integrable c J s k)
    H hH x

/-- Quantified actual-source H-box Fourier norm tail:
the SAME fixed Cpoly from the real original 2S ledger precedes g,
every group incidence and scale, the complete-product trim and H.
No arbitrary Fourier-integral bound is introduced as a premise. -/
theorem exists_chosen_six_fourier_tail_poly12 :
    ∃ Cpoly : ℝ, 0 ≤ Cpoly ∧
      ∀ (g : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s H : ℝ), 0 < s → 0 < H →
          (∫ eta in (fourierBox 6 H)ᶜ,
            ‖𝓕 (actualMixedFamily
              (realSixUnsplitWeight c J s) ∅) eta‖) ≤
            (6 : ℝ) * Cpoly * (((g : ℝ) + 1) ^ 12) / H := by
  obtain ⟨Cpoly, hC, hfamily⟩ :=
    exists_chosen_original_six_fourierD_poly12
  refine ⟨Cpoly, hC, ?_⟩
  intro g c J hc s H hs hH
  obtain ⟨_, hD⟩ := hfamily g c J hc s hs
  calc
    (∫ eta in (fourierBox 6 H)ᶜ,
      ‖𝓕 (actualMixedFamily (realSixUnsplitWeight c J s) ∅) eta‖) ≤
        (6 : ℝ) * derivativeD 6
          (actualMixedFamily (realSixUnsplitWeight c J s)) / H :=
      chosen_six_fourier_Hbox_tail c J s H hH
    _ ≤ (6 : ℝ) * Cpoly * (((g : ℝ) + 1) ^ 12) / H := by
      apply (div_le_div_of_nonneg_right _ hH.le)
      calc
        (6 : ℝ) * derivativeD 6
          (actualMixedFamily (realSixUnsplitWeight c J s)) ≤
          (6 : ℝ) * (Cpoly * (((g : ℝ) + 1) ^ 12)) :=
            mul_le_mul_of_nonneg_left hD (by norm_num)
        _ = (6 : ℝ) * Cpoly * (((g : ℝ) + 1) ^ 12) := by ring

/-- Actual signed source cutoff at the SAME integer rho in both
congruence count and exact coprime mean, with the same full original
product and all source multiplicities. The arithmetic fullModulusMass
is deliberately NOT replaced by an assumed small discrepancy.
The cutoff H is selected from the proved-in-source real 2S D budget,
not from a hypothetical PP inequality. -/
theorem exists_chosen_six_same_rho_epsilon_cutoff :
    ∃ Cpoly : ℝ, 0 ≤ Cpoly ∧
      ∀ (g : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ∀ (ι : Type) (k : ℕ)
          (Q : Finset ℕ) (source : Finset ι)
          (rho : ℕ → ℝ) (coefficient : ι → ℝ)
          (T : ℕ) (originalProducts : ι → Fin k → ℕ)
          (point : ι → FourierSpace 6)
          (H eps : ℝ), 0 < H →
            (6 : ℝ) * Cpoly * (((g : ℝ) + 1) ^ 12) ≤ eps * H →
          |signedSource Q source rho coefficient
              (fun t => realSixUnsplitWeight c J s
                (chartEquiv 6 (point t))) T originalProducts -
            signedSource Q source rho coefficient
              (fun t => (actualTruncatedInverse
                (realSixUnsplitWeight c J s) H (point t)).re)
                T originalProducts| ≤
              eps * fullModulusMass Q source rho coefficient
                T originalProducts := by
  obtain ⟨Cpoly, hC, hfamily⟩ :=
    exists_chosen_original_six_fourierD_poly12
  refine ⟨Cpoly, hC, ?_⟩
  intro g c J hc s hs ι k Q source rho coefficient T originalProducts
    point H eps hH hcut
  let w := realSixUnsplitWeight c J s
  obtain ⟨_, hD⟩ := hfamily g c J hc s hs
  have hD0 : 0 ≤ derivativeD 6 (actualMixedFamily w) :=
    actual_derivativeD_nonneg w
  have hfrac0 : 0 ≤
      (6 : ℝ) * derivativeD 6 (actualMixedFamily w) / H :=
    div_nonneg (mul_nonneg (by norm_num) hD0) hH.le
  have hfrac :
      (6 : ℝ) * derivativeD 6 (actualMixedFamily w) / H ≤ eps := by
    apply (div_le_iff₀ hH).2
    calc
      (6 : ℝ) * derivativeD 6 (actualMixedFamily w) ≤
        (6 : ℝ) * (Cpoly * (((g : ℝ) + 1) ^ 12)) :=
          mul_le_mul_of_nonneg_left hD (by norm_num)
      _ = (6 : ℝ) * Cpoly * (((g : ℝ) + 1) ^ 12) := by ring
      _ ≤ eps * H := hcut
  have heps : 0 ≤ eps := hfrac0.trans hfrac
  apply signedSource_approximation Q source rho coefficient
    (fun t => w (chartEquiv 6 (point t)))
    (fun t => (actualTruncatedInverse w H (point t)).re)
    T originalProducts eps heps
  intro t ht
  exact (chosen_six_real_truncated_inverse_error
    c J s H hH (point t)).trans hfrac

end
end ImbalancedChen.P3HBChosenSixSameRhoCutoff
