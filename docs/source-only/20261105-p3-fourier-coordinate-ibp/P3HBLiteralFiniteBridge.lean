import ImbalancedChen.P3HBLiteralWordMajorant
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

/-!
P3.6, original order-three HB: literal List factor fibre to Fin-position fibre.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

For each nonzero COMPLETE natural product n, every literal ordered factorTuples
word maps to the existing orderedFactorTuples (Fin g) without identifying
different occurrence positions.  This pays a true tau(n)^g bound for
the actual literal HB words of lengths g=2,4,6 and keeps +3,-3,+1
as 3,3,1 in absolute mass. The shifted moment is still unestimated.

This is NOT a restoration of prime labels, factorial multiplicities,
rough projections, empty Gamma mother words, or an original-PP theorem.
-/

namespace ImbalancedChen.P3HBLiteralFiniteBridge

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P3HBOrderedFactorMajorant
open ImbalancedChen.P3HBLiteralWordMajorant

/-- Literal ordered List fibres inject into the image of the finite
Fin-position factor family. The positions (even equal-valued ones) are
retained: this is NOT an unordered multiset or a value-level quotient. -/
theorem literal_fibre_subset_ordered_image (g n : ℕ) (hn : n ≠ 0) :
    factorTuples g n ⊆
      (orderedFactorTuples g n).image (fun f => List.ofFn f) := by
  intro ps hps
  have hs := factorTuples_spec g n ps hps
  have hfin : ps.get ∈ orderedFactorTuples ps.length n := by
    apply (mem_orderedFactorTuples_iff hn ps.get).2
    calc
      (∏ i : Fin ps.length, ps.get i) = (List.ofFn ps.get).prod :=
        (Fin.prod_ofFn ps.get).symm
      _ = ps.prod := by rw [List.ofFn_get]
      _ = n := hs.2.1
  have himage :
      ps ∈ (orderedFactorTuples ps.length n).image (fun f => List.ofFn f) := by
    exact Finset.mem_image.mpr ⟨ps.get, hfin, by simp⟩
  simpa only [hs.1] using himage

/-- The true List fibre has no more positional occurrences than the
previous Fin family. The image estimate does not quotient equal entries. -/
theorem literal_factorTuples_card_le_ordered (g n : ℕ) (hn : n ≠ 0) :
    (factorTuples g n).card ≤ (orderedFactorTuples g n).card := by
  calc
    (factorTuples g n).card
        ≤ ((orderedFactorTuples g n).image (fun f => List.ofFn f)).card :=
          Finset.card_le_card (literal_fibre_subset_ordered_image g n hn)
    _ ≤ (orderedFactorTuples g n).card := Finset.card_image_le

/-- Fixed-exponent divisor bound for the literal, not surrogate, ordered
HB List fibre. No unjustified g-1 saving is taken. -/
theorem literal_factorTuples_card_le_tau_pow (g n : ℕ) (hn : n ≠ 0) :
    (factorTuples g n).card ≤ n.divisors.card ^ g := by
  exact (literal_factorTuples_card_le_ordered g n hn).trans
    (orderedFactorTuples_card_le_tau_pow g n)

/-- The true j-th real-cutoff HB word has g=2(j+1) occurrences and
a single log; its absolute fibre mass is bounded by log(n)*tau(n)^g. -/
theorem literalHBAbsMass_le_tau_pow (y : ℝ) (j n : ℕ)
    (hn : n ≠ 0) :
    literalHBAbsMass y j n ≤
      Real.log (n : ℝ) *
        ((n.divisors.card : ℝ) ^ (2 * (j + 1))) := by
  calc
    literalHBAbsMass y j n
        ≤ Real.log (n : ℝ) *
            ((factorTuples (2 * (j + 1)) n).card : ℝ) :=
          literalHBAbsMass_le_card_log y j n hn
    _ ≤ Real.log (n : ℝ) *
          ((n.divisors.card : ℝ) ^ (2 * (j + 1))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg n)
          exact_mod_cast
            literal_factorTuples_card_le_tau_pow (2 * (j + 1)) n hn

/-- Exact absolute magnitudes of the original three signed HB terms:
binom(3,1), binom(3,2), binom(3,3) = 3,3,1.
Only the true literal ordered fibre is bounded, with no added source label. -/
theorem literalHBThreeTermAbsMass_le_tau_powers (y : ℝ) (n : ℕ)
    (hn : n ≠ 0) :
    (∑ j ∈ Finset.range 3,
      (Nat.choose 3 (j + 1) : ℝ) * literalHBAbsMass y j n)
      ≤ Real.log (n : ℝ) *
          (∑ j ∈ Finset.range 3,
            (Nat.choose 3 (j + 1) : ℝ) *
              ((n.divisors.card : ℝ) ^ (2 * (j + 1)))) := by
  calc
    _ ≤ Real.log (n : ℝ) *
        (∑ j ∈ Finset.range 3,
          (Nat.choose 3 (j + 1) : ℝ) *
            ((factorTuples (2 * (j + 1)) n).card : ℝ)) :=
          literalHBThreeTermAbsMass_le y n hn
    _ ≤ Real.log (n : ℝ) *
        (∑ j ∈ Finset.range 3,
          (Nat.choose 3 (j + 1) : ℝ) *
            ((n.divisors.card : ℝ) ^ (2 * (j + 1)))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg n)
          apply Finset.sum_le_sum
          intro j hj
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact_mod_cast
            literal_factorTuples_card_le_tau_pow (2 * (j + 1)) n hn

/-- Literal original HB masses at FULL nonzero products n!=T feed
the finite shifted divisor moment with fixed exponents 2,4,6.
This is an exact internal reduction, NOT a near-linear shifted-moment
asymptotic; the complete-product=T case is deliberately absent. -/
theorem literalHBThreeTerm_off_shifted_le_mixed_tau
    (y : ℝ) (T : ℕ) (ns : Finset ℕ) (L : ℝ)
    (hscale : ∀ n ∈ offProducts T ns, Real.log (n : ℝ) ≤ L) :
    (∑ n ∈ offProducts T ns,
      (∑ j ∈ Finset.range 3,
        (Nat.choose 3 (j + 1) : ℝ) * literalHBAbsMass y j n) *
          (offShiftTau T n : ℝ))
      ≤ L * (∑ n ∈ offProducts T ns,
        (∑ j ∈ Finset.range 3,
          (Nat.choose 3 (j + 1) : ℝ) *
            ((n.divisors.card : ℝ) ^ (2 * (j + 1)))) *
          (offShiftTau T n : ℝ)) := by
  calc
    _ ≤ ∑ n ∈ offProducts T ns,
          (Real.log (n : ℝ) *
            (∑ j ∈ Finset.range 3,
              (Nat.choose 3 (j + 1) : ℝ) *
                ((n.divisors.card : ℝ) ^ (2 * (j + 1))))) *
              (offShiftTau T n : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnonzero : n ≠ 0 := (Finset.mem_filter.mp hn).2.1
        exact mul_le_mul_of_nonneg_right
          (literalHBThreeTermAbsMass_le_tau_powers y n hnonzero)
          (Nat.cast_nonneg _)
    _ ≤ ∑ n ∈ offProducts T ns,
          (L *
            (∑ j ∈ Finset.range 3,
              (Nat.choose 3 (j + 1) : ℝ) *
                ((n.divisors.card : ℝ) ^ (2 * (j + 1))))) *
              (offShiftTau T n : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnonneg : 0 ≤
            (∑ j ∈ Finset.range 3,
              (Nat.choose 3 (j + 1) : ℝ) *
                ((n.divisors.card : ℝ) ^ (2 * (j + 1)))) := by
          apply Finset.sum_nonneg
          intro j hj
          exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hscale n hn) hnonneg)
          (Nat.cast_nonneg _)
    _ = L * (∑ n ∈ offProducts T ns,
          (∑ j ∈ Finset.range 3,
            (Nat.choose 3 (j + 1) : ℝ) *
              ((n.divisors.card : ℝ) ^ (2 * (j + 1)))) *
                (offShiftTau T n : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring

end
end ImbalancedChen.P3HBLiteralFiniteBridge
