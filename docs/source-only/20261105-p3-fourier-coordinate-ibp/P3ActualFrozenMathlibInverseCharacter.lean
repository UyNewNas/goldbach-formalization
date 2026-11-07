import ImbalancedChen.P3ActualFrozenOriginalSlotPhase
import Mathlib.Analysis.Fourier.FourierTransform

/-!
P3.6 / manuscript §4 (F): exact ORIGINAL SLOT Fourier-INVERSE
character, under the pinned Mathlib analyst normalization.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
The pinned Real.fourierChar_apply identifies the literal Mathlib
additive character with exp(2*pi*I*t). The forward Fourier transform
uses its negative pairing, while inversion uses the positive pairing.
Here no independent Fourier-representation assumption is made.

Original slot identities, the literal endpoint-frozen assignment,
group words, and the genuine original slotLog chart are unchanged.
This is a phase-identity bridge only: the real original W_T admission,
physical prime tuple dictionary, continuous inverse/Fubini, arithmetic
same-rho bounds, and complete PP assembly remain separate obligations.
-/

namespace ImbalancedChen.P3ActualFrozenMathlibInverseCharacter
noncomputable section

open scoped Classical BigOperators FourierTransform
open P3AffineTransitionJets
open ImbalancedChen.P3PhysicalOriginalW
open ImbalancedChen.P3ActualFrozenOriginalSlotPhase

/-- The literal REAL scalar pairing of numbered original HB slots.
No permutation of repeated prime values or labels occurs. -/
def originalSlotDot {n : ℕ} (eta : Fin n → ℝ)
    (z : Point n) : ℝ :=
  ∑ i : Fin n, eta i * z i

/-- The sum of genuine individual Fourier phases is exactly the
Mathlib analyst-convention exponent, on ANY selected slot-ID finset.
The result holds also for the empty set and zero-dimensional charts. -/
theorem original_slot_phase_sum {n : ℕ}
    (s : Finset (Fin n)) (eta : Fin n → ℝ) (z : Point n) :
    (∑ i ∈ s, originalSlotPhase eta z i) =
      (((2 * Real.pi * (∑ i ∈ s, eta i * z i) : ℝ) : ℂ) *
        Complex.I) := by
  have hreal :
      (∑ i ∈ s, 2 * Real.pi * eta i * z i) =
        2 * Real.pi * (∑ i ∈ s, eta i * z i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [originalSlotPhase]
  calc
    (∑ i ∈ s, ((2 * Real.pi * eta i * z i : ℝ) : ℂ) * Complex.I) =
        (∑ i ∈ s, ((2 * Real.pi * eta i * z i : ℝ) : ℂ)) * Complex.I := by
          rw [Finset.sum_mul]
    _ = (((∑ i ∈ s, 2 * Real.pi * eta i * z i : ℝ) : ℂ) *
        Complex.I) := by
          simp only [map_sum]
    _ = _ := by rw [hreal]

/-- The ACTUAL original-slot positive exponential is precisely the
pinned Mathlib FOURIER-INVERSE additive character, including 2*pi,
the sign, and the original coordinate order. -/
theorem originalSlotCharacter_eq_mathlib {n : ℕ}
    (eta : Fin n → ℝ) (z : Point n) :
    originalSlotCharacter eta z =
      ((𝐞 (originalSlotDot eta z) : Circle) : ℂ) := by
  unfold originalSlotCharacter originalSlotDot
  rw [Real.fourierChar_apply]
  exact congrArg Complex.exp
    (original_slot_phase_sum Finset.univ eta z)

/-- A genuine ordered physical WORD of original slot IDs uses the
same pinned character on precisely its ID set. This does not claim
that an untagged list of prime values determines positional modes. -/
theorem physicalWordCharacter_eq_mathlib {n : ℕ}
    (word : List (Fin n)) (eta : Fin n → ℝ) (z : Point n) :
    physicalWordCharacter word eta z =
      ((𝐞 (∑ i ∈ word.toFinset, eta i * z i) : Circle) : ℂ) := by
  unfold physicalWordCharacter
  rw [Real.fourierChar_apply]
  exact congrArg Complex.exp
    (original_slot_phase_sum word.toFinset eta z)

/-- The Mathlib positive inverse character factors along the ACTUAL
endpoint-frozen three ordered physical ID words. The only hypotheses
are the real slot-word distinctness and coverage already required by
the literal frozen assignment; no W_T separation hypothesis appears. -/
theorem actual_frozen_mathlib_inverse_character {n : ℕ}
    (D A : ℝ) (yz : Bool) (upper : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (hnodup : (p 0 :: p 1 :: p 2 :: tail).Nodup)
    (hcover : ∀ i, i ∈ p 0 :: p 1 :: p 2 :: tail)
    (eta : Fin n → ℝ) (z : Point n) :
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    ((𝐞 (originalSlotDot eta z) : Circle) : ℂ) =
      ((𝐞 (∑ i ∈ slots.1.toFinset, eta i * z i) : Circle) : ℂ) *
        (((𝐞 (∑ i ∈ slots.2.1.toFinset, eta i * z i) : Circle) : ℂ) *
          ((𝐞 (∑ i ∈ slots.2.2.toFinset, eta i * z i) : Circle) : ℂ)) := by
  simpa only [originalSlotCharacter_eq_mathlib,
    physicalWordCharacter_eq_mathlib] using
      (actual_frozen_original_phase_from_words
        D A yz upper p tail hnodup hcover eta z)

/-- Specialize the real pinned inverse character to the exact original
physical logarithmic coordinates log(value_i / U_i), not a synthetic
frequency chart or a group-product quotient. -/
theorem actual_frozen_slotLog_mathlib_inverse {n : ℕ}
    (D A : ℝ) (yz : Bool) (upper : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (hnodup : (p 0 :: p 1 :: p 2 :: tail).Nodup)
    (hcover : ∀ i, i ∈ p 0 :: p 1 :: p 2 :: tail)
    (eta U values : Fin n → ℝ) :
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    ((𝐞 (originalSlotDot eta (slotLog U values)) : Circle) : ℂ) =
      ((𝐞 (∑ i ∈ slots.1.toFinset,
        eta i * slotLog U values i) : Circle) : ℂ) *
        (((𝐞 (∑ i ∈ slots.2.1.toFinset,
          eta i * slotLog U values i) : Circle) : ℂ) *
          ((𝐞 (∑ i ∈ slots.2.2.toFinset,
            eta i * slotLog U values i) : Circle) : ℂ)) := by
  exact actual_frozen_mathlib_inverse_character
    D A yz upper p tail hnodup hcover eta (slotLog U values)

end
end ImbalancedChen.P3ActualFrozenMathlibInverseCharacter
