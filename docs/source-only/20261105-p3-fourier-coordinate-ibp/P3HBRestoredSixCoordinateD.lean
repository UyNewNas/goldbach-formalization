import ImbalancedChen.P3HBOriginalRestoredTensorL1
import ImbalancedChen.P3FourierCoordinateIBP
import Mathlib.Tactic

/-!
P3.6, frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product-completion section 2 and section 4 (F).

A finite six-position bridge between the actual 729-child signed restoration
and the ORIGINAL doubled-subset derivative list used by the Fourier D ledger.
The finite set of 2S words is not replaced by coordinate sets or a new
frequency model. Its order is selected before group number and all scales.

This is only the six-position grouped geometry * one complete trim * unsplit
HB dyadic tensor. It is NOT the complete physical W_T family, the growing
HB-length m(T) uniformity, or the same-integer-rho arithmetic estimate.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBRestoredSixCoordinateD
noncomputable section

open MeasureTheory
open scoped Classical BigOperators
open P3FourierSubsetExpansion
open P3U5ChartMixedL1Budget
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
open ImbalancedChen.P3HBOriginalRestoredTensorL1

/-- The ACTUAL six-position unsplit dyadic tensor at zero initial
logarithmic orders, not an independently chosen geometric multiplier. -/
def unsplitSixLogTensor (chi : ℝ → ℂ) (u : Fin 6 → ℝ) : ℂ :=
  ∏ i : Fin 6,
    iteratedDeriv 0
      (fun v : ℝ => chi (Real.exp v) - chi (2 * Real.exp v))
      (u i)

/-- The 729 original positional children sum EXACTLY to the unsplit
six-position tensor before taking absolute values. -/
theorem unsplitSixLogTensor_eq_children (chi : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (u : Fin 6 → ℝ) :
    unsplitSixLogTensor chi u =
      ∑ child ∈ smoothChildren,
        logTensorMixed chi (fun _ => 0) child u := by
  exact (logTensorMixed_children_sum chi hchi (fun _ => 0) u).symm

/-- In degree zero the actual signed restoration is precisely the
original grouped weight times its one unsplit six-slot dyadic tensor. -/
theorem restored_zero_eq_unsplit {g : ℕ}
    (chi eta : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (u : Fin 6 → ℝ) :
    originalRestoredWholeDerivative chi eta c J s (fun _ => 0)
      (fun i : Fin 0 => Fin.elim0 i) u =
    originalGroupPhysicalTrim chi eta c J s u *
      unsplitSixLogTensor chi u := by
  change (∑ child ∈ smoothChildren,
    originalGroupPhysicalTrim chi eta c J s u *
      logTensorMixed chi (fun _ => 0) child u) =
    originalGroupPhysicalTrim chi eta c J s u *
      unsplitSixLogTensor chi u
  rw [← Finset.mul_sum, ← unsplitSixLogTensor_eq_children chi hchi u]

/-- The pinned, actual doubled S definition repeats each selected coordinate
in adjacent ordered positions; its length never exceeds 2*6=12.
This is the original Fourier order bound, not a surrogate coordinate set. -/
theorem doubled_six_length_le_twelve (S : Finset (Fin 6)) :
    (doubled S).length ≤ 12 := by
  simpa only [Nat.reduceMul] using
    (P3U5ChartMixedL1Budget.doubled_length_le S)

/-- The full finite 2S mixed-L1 ledger for the restored original
six-position tensor. Every repeated coordinate in the actual doubled
word is retained, and every term uses the same physical scale s. -/
def sixRestoredMixedD {g : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ) : ℝ :=
  ∑ S : Finset (Fin 6),
    ∫ u : Fin 6 → ℝ,
      ‖originalRestoredWholeDerivative chi eta c J s
        (fun _ => 0)
        (fun i : Fin (doubled S).length => (doubled S)[i]) u‖

/-- Genuine fixed-six-position ALL-2S finite L1 budget, obtained by
instantiating the existing 729-label integrated theorem separately for
each literal Fourier doubled word. No target L1 budget is assumed.
The result has a finite polynomial-in-g RHS with exponent bounded by
the fixed 12. This is not yet uniform in a growing m(T). -/
theorem sixRestoredMixedD_integrable_budget
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1) :
    ∃ B Ceta C : ℝ, 1 ≤ B ∧ 1 ≤ Ceta ∧ 0 ≤ C ∧
      ∀ (g : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        (∀ S : Finset (Fin 6),
          Integrable (fun u : Fin 6 → ℝ =>
            ‖originalRestoredWholeDerivative chi eta c J s
              (fun _ => 0)
              (fun i : Fin (doubled S).length => (doubled S)[i]) u‖)) ∧
        sixRestoredMixedD chi eta c J s ≤
          ∑ S : Finset (Fin 6),
            (2 : ℝ) ^ (doubled S).length *
              (((2 : ℝ) ^ (doubled S).length *
                  (((g : ℝ) + 1) * B) ^ (doubled S).length * Ceta) *
                ((smoothChildren.card : ℝ) *
                  ((2 * Real.log 2) * C) ^ 6)) := by
  classical
  obtain ⟨B, Ceta, C, hB, hCeta, hC, hbase⟩ :=
    originalRestoredWholeDerivative_integrable_polynomial
      chi eta hchi heta hsmall hlarge hpsi hetaSmall hetaLarge
      12
  refine ⟨B, Ceta, C, hB, hCeta, hC, ?_⟩
  intro g c J hc s hs
  have hS (S : Finset (Fin 6)) :
      Integrable (fun u : Fin 6 → ℝ =>
        ‖originalRestoredWholeDerivative chi eta c J s
          (fun _ => 0)
          (fun i : Fin (doubled S).length => (doubled S)[i]) u‖) ∧
      (∫ u : Fin 6 → ℝ,
        ‖originalRestoredWholeDerivative chi eta c J s
          (fun _ => 0)
          (fun i : Fin (doubled S).length => (doubled S)[i]) u‖) ≤
        (2 : ℝ) ^ (doubled S).length *
          (((2 : ℝ) ^ (doubled S).length *
              (((g : ℝ) + 1) * B) ^ (doubled S).length * Ceta) *
            ((smoothChildren.card : ℝ) *
              ((2 * Real.log 2) * C) ^ 6)) :=
    hbase g (doubled S).length c J hc s hs
      (fun i : Fin (doubled S).length => (doubled S)[i])
      (doubled_six_length_le_twelve S)
      (fun _ => 0) (fun _ => Nat.zero_le _)
  refine ⟨(fun S => (hS S).1), ?_⟩
  unfold sixRestoredMixedD
  apply Finset.sum_le_sum
  intro S _
  exact (hS S).2

end
end ImbalancedChen.P3HBRestoredSixCoordinateD
