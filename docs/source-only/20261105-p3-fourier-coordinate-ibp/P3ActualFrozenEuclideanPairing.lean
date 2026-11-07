import ImbalancedChen.P3ActualFrozenMathlibInverseCharacter
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
P3.6 / fixed manuscript 9731290 §4 (F): the ORIGINAL numbered-slot
scalar pairing is the ACTUAL real EuclideanSpace Fourier pairing.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

The predecessor identifies the positive Mathlib Fourier-inverse
character with the original coordinate dot product. This file removes
the remaining dot-versus-inner-product normalization gap using the
PINNED EuclideanSpace.inner_toLp_toLp API. It then specializes the
literal THREE actual frozen ID words and the genuine physical slotLog
chart. No permutation of positional weights, untagged prime-tuple
dictionary, W_T Fourier admission, or modulus error estimate is assumed.

The real scalar pairing is symmetric, but the sign in the inverse
character is still POSITIVE. Physical frequencies are not silently
identified with Mathlib frequencies without their separate 2*pi scale.
-/

namespace ImbalancedChen.P3ActualFrozenEuclideanPairing
noncomputable section

open scoped Classical BigOperators FourierTransform RealInnerProductSpace
open P3AffineTransitionJets
open ImbalancedChen.P3PhysicalOriginalW
open ImbalancedChen.P3ActualFrozenOriginalSlotPhase
open ImbalancedChen.P3ActualFrozenMathlibInverseCharacter

/-- Exact pinned real Euclidean inner product of the actual ORIGINAL
numbered slots. The reverse-order dotProduct in Mathlib is paid by
commutativity in ℝ, with no conjugation or factor of 2*pi. This also
covers n=0 and duplicated VALUES on distinct original slot IDs. -/
theorem originalSlotDot_eq_euclidean_inner {n : ℕ}
    (eta : Fin n → ℝ) (z : Point n) :
    originalSlotDot eta z =
      ⟪(PiLp.toLp 2 eta : EuclideanSpace ℝ (Fin n)),
        (PiLp.toLp 2 z : EuclideanSpace ℝ (Fin n))⟫_ℝ := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [originalSlotDot, dotProduct, star_trivial, mul_comm]

/-- The true positive Fourier-INVERSE Euclidean pairing (not merely an
ad hoc coordinate phase) is the already proved original-slot character.
This is an algebraic character identity, NOT Fourier inversion of W_T. -/
theorem originalSlotCharacter_eq_euclidean_inverse {n : ℕ}
    (eta : Fin n → ℝ) (z : Point n) :
    originalSlotCharacter eta z =
      ((𝐞 (⟪(PiLp.toLp 2 eta : EuclideanSpace ℝ (Fin n)),
        (PiLp.toLp 2 z : EuclideanSpace ℝ (Fin n))⟫_ℝ) : Circle) : ℂ) := by
  simpa only [originalSlotDot_eq_euclidean_inner] using
    (originalSlotCharacter_eq_mathlib eta z)

/-- The genuine original Euclidean pairing factors over the THREE
endpoint-frozen physical ID words. This is exactly the previous
frozen-character identity, now at the literal Euclidean inner product,
under original-ID distinctness and coverage (not value distinctness). -/
theorem actual_frozen_euclidean_inverse_character {n : ℕ}
    (D A : ℝ) (yz : Bool) (upper : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (hnodup : (p 0 :: p 1 :: p 2 :: tail).Nodup)
    (hcover : ∀ i, i ∈ p 0 :: p 1 :: p 2 :: tail)
    (eta : Fin n → ℝ) (z : Point n) :
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    ((𝐞 (⟪(PiLp.toLp 2 eta : EuclideanSpace ℝ (Fin n)),
      (PiLp.toLp 2 z : EuclideanSpace ℝ (Fin n))⟫_ℝ) : Circle) : ℂ) =
      ((𝐞 (∑ i ∈ slots.1.toFinset, eta i * z i) : Circle) : ℂ) *
        (((𝐞 (∑ i ∈ slots.2.1.toFinset, eta i * z i) : Circle) : ℂ) *
          ((𝐞 (∑ i ∈ slots.2.2.toFinset, eta i * z i) : Circle) : ℂ)) := by
  simpa only [originalSlotDot_eq_euclidean_inner] using
    (actual_frozen_mathlib_inverse_character
      D A yz upper p tail hnodup hcover eta z)

/-- The same equality at literal original log(value_i/U_i) coordinates,
keeping the actual frozen slot IDs and all repeated prime values.
This does NOT yet map the tagged slots to untagged gamma group tuples. -/
theorem actual_frozen_slotLog_euclidean_inverse {n : ℕ}
    (D A : ℝ) (yz : Bool) (upper : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (hnodup : (p 0 :: p 1 :: p 2 :: tail).Nodup)
    (hcover : ∀ i, i ∈ p 0 :: p 1 :: p 2 :: tail)
    (eta U values : Fin n → ℝ) :
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    ((𝐞 (⟪(PiLp.toLp 2 eta : EuclideanSpace ℝ (Fin n)),
      (PiLp.toLp 2 (slotLog U values) :
        EuclideanSpace ℝ (Fin n))⟫_ℝ) : Circle) : ℂ) =
      ((𝐞 (∑ i ∈ slots.1.toFinset,
        eta i * slotLog U values i) : Circle) : ℂ) *
        (((𝐞 (∑ i ∈ slots.2.1.toFinset,
          eta i * slotLog U values i) : Circle) : ℂ) *
          ((𝐞 (∑ i ∈ slots.2.2.toFinset,
            eta i * slotLog U values i) : Circle) : ℂ)) := by
  exact actual_frozen_euclidean_inverse_character
    D A yz upper p tail hnodup hcover eta (slotLog U values)

end
end ImbalancedChen.P3ActualFrozenEuclideanPairing
