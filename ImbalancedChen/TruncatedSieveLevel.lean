import ImbalancedChen.FiniteSieveModel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Genuine finite level truncation for the actual lambda-square sieve

The coefficients here are mathlib's `BoundingSieve.lambdaSquared`, not a
replacement sieve predicate. If the input weights vanish above a natural
cutoff `L`, their lambda-square coefficients vanish above `L * L`.
Consequently both the main and error sums in the proved finite sieve
inequality can be restricted to divisors at most `L * L`.

The final source bound keeps the literal `halfProductCongruenceMass` and
the literal total source cardinality divided by the totient. It assumes
neither a distribution estimate nor an upper bound for the desired sifted
count. No optimized coefficient or asymptotic conclusion is claimed.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Mathlib uses the empty divisor set at zero, so the coefficient there
vanishes even if the input weight at zero is nonzero. -/
@[simp] theorem lambdaSquared_at_zero (w : ℕ → ℝ) :
    BoundingSieve.lambdaSquared w 0 = 0 := by
  simp [BoundingSieve.lambdaSquared]

/-- A cutoff at `L` for the input weights gives a cutoff at `L * L` for
mathlib's actual lambda-square coefficients. A nonzero summand requires
both factors at most `L`, while its modulus is their least common multiple. -/
theorem lambdaSquared_eq_zero_of_level
    (w : ℕ → ℝ) (L : ℕ) (hcut : ∀ n : ℕ, L < n → w n = 0)
    (d : ℕ) (hd : L * L < d) : BoundingSieve.lambdaSquared w d = 0 := by
  classical
  unfold BoundingSieve.lambdaSquared
  apply Finset.sum_eq_zero
  intro a _ha
  apply Finset.sum_eq_zero
  intro b _hb
  by_cases hab : d = Nat.lcm a b
  · rw [if_pos hab]
    by_cases haL : a ≤ L
    · have hbL : L < b := by
        by_contra hn
        have hb : b ≤ L := Nat.le_of_not_gt hn
        have hbound : d ≤ L * L := calc
          d = Nat.lcm a b := hab
          _ ≤ a * b := by
            rw [Nat.lcm_eq_mul_div]
            exact Nat.div_le_self _ _
          _ ≤ L * L := Nat.mul_le_mul haL hb
        exact (Nat.not_le_of_lt hd) hbound
      rw [hcut b hbL, mul_zero]
    · rw [hcut a (Nat.lt_of_not_ge haL), zero_mul]
  · exact if_neg hab

/-- Restriction of a finite sum is an equality when all omitted terms vanish. -/
private theorem sum_eq_sum_filter_of_zero_above
    (s : Finset ℕ) (B : ℕ) (f : ℕ → ℝ)
    (hf : ∀ d : ℕ, B < d → f d = 0) :
    (∑ d ∈ s, f d) = ∑ d ∈ s with d ≤ B, f d := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hdB : d ≤ B
  · rw [if_pos hdB]
  · rw [if_neg hdB]
    exact hf d (Nat.lt_of_not_ge hdB)

/-- The actual mathlib main sum, with its level restriction proved from the
support of the weights. -/
theorem boundingSieve_mainSum_lambdaSquared_truncated
    (s : BoundingSieve) (w : ℕ → ℝ) (L : ℕ)
    (hcut : ∀ n : ℕ, L < n → w n = 0) :
    s.mainSum (BoundingSieve.lambdaSquared w) =
      ∑ d ∈ s.prodPrimes.divisors with d ≤ L * L,
        BoundingSieve.lambdaSquared w d * s.nu d := by
  unfold BoundingSieve.mainSum
  apply sum_eq_sum_filter_of_zero_above
  intro d hd
  rw [lambdaSquared_eq_zero_of_level w L hcut d hd, zero_mul]

/-- The actual mathlib error sum has no contribution from moduli exceeding
`L * L`; the remainder itself need not vanish there. -/
theorem boundingSieve_errSum_lambdaSquared_truncated
    (s : BoundingSieve) (w : ℕ → ℝ) (L : ℕ)
    (hcut : ∀ n : ℕ, L < n → w n = 0) :
    s.errSum (BoundingSieve.lambdaSquared w) =
      ∑ d ∈ s.prodPrimes.divisors with d ≤ L * L,
        |BoundingSieve.lambdaSquared w d| * |s.rem d| := by
  unfold BoundingSieve.errSum
  apply sum_eq_sum_filter_of_zero_above
  intro d hd
  rw [lambdaSquared_eq_zero_of_level w L hcut d hd, abs_zero, zero_mul]

/-- Mathlib's finite upper-bound theorem with both sums genuinely truncated.
The upper-Moebius property is supplied by mathlib from `w 1 = 1`. -/
theorem boundingSieve_siftedSum_le_lambdaSquared_truncated
    (s : BoundingSieve) (w : ℕ → ℝ) (hw : w 1 = 1) (L : ℕ)
    (hcut : ∀ n : ℕ, L < n → w n = 0) :
    s.siftedSum ≤ s.totalMass *
        (∑ d ∈ s.prodPrimes.divisors with d ≤ L * L,
          BoundingSieve.lambdaSquared w d * s.nu d) +
      ∑ d ∈ s.prodPrimes.divisors with d ≤ L * L,
        |BoundingSieve.lambdaSquared w d| * |s.rem d| := by
  rw [← boundingSieve_mainSum_lambdaSquared_truncated s w L hcut,
    ← boundingSieve_errSum_lambdaSquared_truncated s w L hcut]
  exact BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
    (s := s) (BoundingSieve.lambdaSquared w)
    (BoundingSieve.upperMoebius_lambdaSquared w hw)

/-- A genuine finite level-`L * L` bound for the original sifted source.
Both sums run only over allowed divisors at most `L * L`. The discrepancy
is still the actual residue count minus the literal total mass over `φ(d)`. -/
theorem siftedHalfProductSource_card_le_lambdaSquared_truncated
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N)
    (w : ℕ → ℝ) (hw : w 1 = 1) (L : ℕ)
    (hcut : ∀ n : ℕ, L < n → w n = 0) :
    ((siftedHalfProductSource num den N T z).card : ℝ) ≤
      ((halfProductSource num den N T).card : ℝ) *
        (∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
          BoundingSieve.lambdaSquared w d / (Nat.totient d : ℝ)) +
      ∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
        |BoundingSieve.lambdaSquared w d| *
          |halfProductCongruenceMass num den N T d -
            ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ)| := by
  have hmain :
      (∑ d ∈ (sieveProduct N z).divisors,
        BoundingSieve.lambdaSquared w d / (Nat.totient d : ℝ)) =
      ∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
        BoundingSieve.lambdaSquared w d / (Nat.totient d : ℝ) := by
    apply sum_eq_sum_filter_of_zero_above
    intro d hd
    rw [lambdaSquared_eq_zero_of_level w L hcut d hd, zero_div]
  have herr :
      (∑ d ∈ (sieveProduct N z).divisors, |BoundingSieve.lambdaSquared w d| *
        |halfProductCongruenceMass num den N T d -
          ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ)|) =
      ∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
        |BoundingSieve.lambdaSquared w d| *
          |halfProductCongruenceMass num den N T d -
            ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ)| := by
    apply sum_eq_sum_filter_of_zero_above
    intro d hd
    rw [lambdaSquared_eq_zero_of_level w L hcut d hd, abs_zero, zero_mul]
  rw [← hmain, ← herr]
  exact siftedHalfProductSource_card_le_lambdaSquared num den N T z hN w hw

/-- A coarse coefficient bound using the number of ordered divisor pairs.
The bound on `w` is required only at divisors of this modulus. This is an
elementary error-weight estimate, not an optimized sieve coefficient. -/
theorem abs_lambdaSquared_le_divisor_card_sq
    (w : ℕ → ℝ) (d : ℕ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ n : ℕ, n ∈ d.divisors → |w n| ≤ W) :
    |BoundingSieve.lambdaSquared w d| ≤ (d.divisors.card : ℝ) ^ 2 * W ^ 2 := by
  classical
  unfold BoundingSieve.lambdaSquared
  calc
    |∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d = Nat.lcm a b then w a * w b else 0| ≤
        ∑ a ∈ d.divisors, |∑ b ∈ d.divisors,
          if d = Nat.lcm a b then w a * w b else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ d.divisors, ∑ _b ∈ d.divisors, W * W := by
      apply Finset.sum_le_sum
      intro a ha
      calc
        |∑ b ∈ d.divisors, if d = Nat.lcm a b then w a * w b else 0| ≤
            ∑ b ∈ d.divisors, |if d = Nat.lcm a b then w a * w b else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _b ∈ d.divisors, W * W := by
          apply Finset.sum_le_sum
          intro b hb
          by_cases hab : d = Nat.lcm a b
          · rw [if_pos hab, abs_mul]
            exact mul_le_mul (hw a ha) (hw b hb) (abs_nonneg (w b)) hW
          · rw [if_neg hab, abs_zero]
            exact mul_nonneg hW hW
    _ = (d.divisors.card : ℝ) ^ 2 * W ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

end

end ImbalancedChen
