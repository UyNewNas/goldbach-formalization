import ImbalancedChen.P3HBLiteralFiniteBridge
import ImbalancedChen.P5ActualRoughHeathBrownWords

/-!
P3.6, pinned manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 exact rough HB and §4 (F) arithmetic tail.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

The actual STRICT rough projector z < p is the SAME factor on every
literal ordered HB tuple whose complete product is n. Consequently the
complex rough-HB absolute coefficient mass is EXACTLY the original
literal mass times the norm of the original rough projector at n.

The real cutoff y, one logarithm per original word, positional
multiplicities, and the absolute magnitudes 3,3,1 remain unchanged.
No prime-label/factorial compiler, near-linear shifted moment, or PP
distribution conclusion is asserted. In particular n = T is excluded
from the nonzero-shift moment, but not silently declared negligible.
-/

namespace ImbalancedChen.P3HBRoughLiteralMoment

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.RoughSlotCharacterLift20261026b
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords
open ImbalancedChen.P3HBOrderedFactorMajorant
open ImbalancedChen.P3HBLiteralWordMajorant
open ImbalancedChen.P3HBLiteralFiniteBridge

/-- Absolute mass of the literal complex, strictly rough-filtered
original HB occurrence word. This sums original ordered positions. -/
def roughLiteralHBAbsMass (z y : ℝ) (j n : ℕ) : ℝ :=
  ∑ ps ∈ factorTuples (2 * (j + 1)) n,
    ‖roughTupleWeight z y (roles j) ps‖

/-- The actual rough condition depends on the COMPLETE product n.
The equality holds even at n=0,1; no unit log is identified with
an empty Gamma mother word. -/
theorem roughLiteralHBAbsMass_eq_mask {z : ℝ} (hz : 0 ≤ z)
    (y : ℝ) (j n : ℕ) :
    roughLiteralHBAbsMass z y j n =
      ‖roughOneSlot z n‖ * literalHBAbsMass y j n := by
  unfold roughLiteralHBAbsMass
  calc
    (∑ ps ∈ factorTuples (2 * (j + 1)) n,
        ‖roughTupleWeight z y (roles j) ps‖) =
      ∑ ps ∈ factorTuples (2 * (j + 1)) n,
        |tupleWeight (hbWord y j) ps| * ‖roughOneSlot z n‖ := by
          apply Finset.sum_congr rfl
          intro ps hps
          rw [actual_word_mask hz y j n ps hps, norm_mul, norm_real]
    _ = (∑ ps ∈ factorTuples (2 * (j + 1)) n,
          |tupleWeight (hbWord y j) ps|) * ‖roughOneSlot z n‖ := by
          rw [Finset.sum_mul]
    _ = ‖roughOneSlot z n‖ * literalHBAbsMass y j n := by
          rw [literalHBAbsMass, mul_comm]

/-- The actual rough projector is one-bounded: it cannot enlarge a
literal HB fibre's absolute mass. -/
theorem roughLiteralHBAbsMass_le_literal {z : ℝ} (hz : 0 ≤ z)
    (y : ℝ) (j n : ℕ) :
    roughLiteralHBAbsMass z y j n ≤ literalHBAbsMass y j n := by
  rw [roughLiteralHBAbsMass_eq_mask hz]
  have hmass : 0 ≤ literalHBAbsMass y j n := by
    unfold literalHBAbsMass
    exact Finset.sum_nonneg (fun ps hps => abs_nonneg _)
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (roughOneSlot_norm_le z n) hmass

/-- Full integer product is retained, with fixed exponent 2(j+1).
No uniform unbounded-log hypothesis has been added. -/
theorem roughLiteralHBAbsMass_le_tau_pow {z : ℝ} (hz : 0 ≤ z)
    (y : ℝ) (j n : ℕ) (hn : n ≠ 0) :
    roughLiteralHBAbsMass z y j n ≤
      Real.log (n : ℝ) * ((n.divisors.card : ℝ) ^ (2 * (j + 1))) :=
  (roughLiteralHBAbsMass_le_literal hz y j n).trans
    (literalHBAbsMass_le_tau_pow y j n hn)

/-- Original three signed HB terms, after taking absolute magnitudes:
no new 1/3! factor, no replacement of the three 3,3,1 weights. -/
def roughLiteralThreeTermAbsMass (z y : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 3,
    (Nat.choose 3 (j + 1) : ℝ) * roughLiteralHBAbsMass z y j n

theorem roughLiteralThreeTermAbsMass_eq_mask {z : ℝ} (hz : 0 ≤ z)
    (y : ℝ) (n : ℕ) :
    roughLiteralThreeTermAbsMass z y n =
      ‖roughOneSlot z n‖ *
        (∑ j ∈ Finset.range 3,
          (Nat.choose 3 (j + 1) : ℝ) * literalHBAbsMass y j n) := by
  unfold roughLiteralThreeTermAbsMass
  calc
    (∑ j ∈ Finset.range 3,
       (Nat.choose 3 (j + 1) : ℝ) * roughLiteralHBAbsMass z y j n) =
      ∑ j ∈ Finset.range 3,
       (Nat.choose 3 (j + 1) : ℝ) *
         (‖roughOneSlot z n‖ * literalHBAbsMass y j n) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [roughLiteralHBAbsMass_eq_mask hz]
    _ = ‖roughOneSlot z n‖ *
      (∑ j ∈ Finset.range 3,
        (Nat.choose 3 (j + 1) : ℝ) * literalHBAbsMass y j n) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring

/-- The strict rough projector annihilates all originally disallowed
full products, including a prime exactly at the threshold. -/
theorem roughLiteralThreeTermAbsMass_zero_of_not_coprime {z : ℝ}
    (hz : 0 ≤ z) (y : ℝ) (n : ℕ)
    (hn : ¬ n.Coprime (smallProduct z)) :
    roughLiteralThreeTermAbsMass z y n = 0 := by
  rw [roughLiteralThreeTermAbsMass_eq_mask hz,
    roughOneSlot_eq_coprime_indicator hz]
  simp [hn]

theorem roughLiteralThreeTermAbsMass_le_literal {z : ℝ} (hz : 0 ≤ z)
    (y : ℝ) (n : ℕ) :
    roughLiteralThreeTermAbsMass z y n ≤
      ∑ j ∈ Finset.range 3,
        (Nat.choose 3 (j + 1) : ℝ) * literalHBAbsMass y j n := by
  rw [roughLiteralThreeTermAbsMass_eq_mask hz]
  have hmass : 0 ≤
      ∑ j ∈ Finset.range 3,
        (Nat.choose 3 (j + 1) : ℝ) * literalHBAbsMass y j n := by
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold literalHBAbsMass
    exact Finset.sum_nonneg (fun ps hps => abs_nonneg _)
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (roughOneSlot_norm_le z n) hmass

/-- Genuine rough HB, with the same fixed 2,4,6 divisor exponents. -/
theorem roughLiteralThreeTermAbsMass_le_tau_powers {z : ℝ}
    (hz : 0 ≤ z) (y : ℝ) (n : ℕ) (hn : n ≠ 0) :
    roughLiteralThreeTermAbsMass z y n ≤
      Real.log (n : ℝ) *
        (∑ j ∈ Finset.range 3,
          (Nat.choose 3 (j + 1) : ℝ) *
            ((n.divisors.card : ℝ) ^ (2 * (j + 1)))) :=
  (roughLiteralThreeTermAbsMass_le_literal hz y n).trans
    (literalHBThreeTermAbsMass_le_tau_powers y n hn)

/-- The rough-filtered literal HB moment is no larger than the
original, UNESTIMATED fixed-exponent shifted moment. The exceptional
complete product n=T is not put into tau(0). -/
theorem roughLiteralThreeTerm_off_shifted_le_mixed_tau {z : ℝ}
    (hz : 0 ≤ z) (y : ℝ) (T : ℕ) (ns : Finset ℕ) (L : ℝ)
    (hscale : ∀ n ∈ offProducts T ns, Real.log (n : ℝ) ≤ L) :
    (∑ n ∈ offProducts T ns,
      roughLiteralThreeTermAbsMass z y n * (offShiftTau T n : ℝ))
      ≤ L * (∑ n ∈ offProducts T ns,
        (∑ j ∈ Finset.range 3,
          (Nat.choose 3 (j + 1) : ℝ) *
            ((n.divisors.card : ℝ) ^ (2 * (j + 1)))) *
          (offShiftTau T n : ℝ)) := by
  calc
    _ ≤ ∑ n ∈ offProducts T ns,
        (∑ j ∈ Finset.range 3,
          (Nat.choose 3 (j + 1) : ℝ) * literalHBAbsMass y j n) *
          (offShiftTau T n : ℝ) := by
            apply Finset.sum_le_sum
            intro n hn
            exact mul_le_mul_of_nonneg_right
              (roughLiteralThreeTermAbsMass_le_literal hz y n)
              (Nat.cast_nonneg _)
    _ ≤ _ := literalHBThreeTerm_off_shifted_le_mixed_tau y T ns L hscale

end
end ImbalancedChen.P3HBRoughLiteralMoment
