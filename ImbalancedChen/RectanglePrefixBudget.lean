import ImbalancedChen.ResidueSelectorBudget

/-!
# Finite rectangle budgets from two raw prime-prefix budgets

For each of the two second-coordinate endpoints, the input is a bound on
the SUM of absolute raw prime-prefix AP errors, uniform over primitive
residue selectors. The main terms may depend on the modulus but not on
the residue. Finite recentering gives a factor two for each input budget;
exact prefix subtraction and the triangle inequality then give
`2 * Bhi + 2 * Blo` for the actual full rectangle discrepancy sum.

The target selector need only be primitive, with no canonical-range
restriction. The selected modulus set is any finite set of positive
moduli. The inclusive-interval forms also cover `D = 0`, and the actual
grid forms display the literal ceiling-minus-one endpoints.

All estimates are explicit hypotheses on the two input prefix AP counts,
never on the target rectangle discrepancy. No analytic distribution
estimate is asserted here. Full ordered-prime rectangles, their genuine
coprime masses, repeated products, squares, and exterior products are
retained by the existing exact identities.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Two selector-uniform raw prefix SUM budgets give the actual full
rectangle coprime-discrepancy SUM budget, with no modulus-count factor. -/
theorem sum_abs_primeIntervalRectangle_discrepancy_le_of_uniform_prefix_selectors
    (S : Finset ℕ) (L U Vlo Vhi : ℕ) (Mhi Mlo : ℕ → ℝ) (Bhi Blo : ℝ)
    (hV : Vlo ≤ Vhi) (hS : ∀ d ∈ S, 0 < d)
    (hhi : ∀ b : ℕ → ℕ, (∀ d ∈ S, b d < d ∧ Nat.Coprime (b d) d) →
      (∑ d ∈ S, |primeRectanglePrefixAPCount L U Vhi (b d) d - Mhi d|) ≤ Bhi)
    (hlo : ∀ b : ℕ → ℕ, (∀ d ∈ S, b d < d ∧ Nat.Coprime (b d) d) →
      (∑ d ∈ S, |primeRectanglePrefixAPCount L U Vlo (b d) d - Mlo d|) ≤ Blo)
    (a : ℕ → ℕ) (ha : ∀ d ∈ S, Nat.Coprime (a d) d) :
    (∑ d ∈ S,
      |(((primeIntervalRectangle L U Vlo Vhi).filter
          (fun p => Nat.ModEq d (p.1 * p.2) (a d))).card : ℝ) -
        (((primeIntervalRectangle L U Vlo Vhi).filter
          (fun p => Nat.Coprime (p.1 * p.2) d)).card : ℝ) / (Nat.totient d : ℝ)|) ≤
      2 * Bhi + 2 * Blo := by
  calc
    (∑ d ∈ S,
        |(((primeIntervalRectangle L U Vlo Vhi).filter
            (fun p => Nat.ModEq d (p.1 * p.2) (a d))).card : ℝ) -
          (((primeIntervalRectangle L U Vlo Vhi).filter
            (fun p => Nat.Coprime (p.1 * p.2) d)).card : ℝ) / (Nat.totient d : ℝ)|) ≤
        ∑ d ∈ S, (|primeRectanglePrefixDiscrepancy L U Vhi (a d) d| +
          |primeRectanglePrefixDiscrepancy L U Vlo (a d) d|) := by
      apply Finset.sum_le_sum
      intro d _
      rw [primeIntervalRectangle_discrepancy_eq_prefix_sub L U Vlo Vhi (a d) d hV]
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (primeRectanglePrefixDiscrepancy L U Vhi (a d) d) 0
          (primeRectanglePrefixDiscrepancy L U Vlo (a d) d))
    _ = (∑ d ∈ S, |primeRectanglePrefixDiscrepancy L U Vhi (a d) d|) +
        (∑ d ∈ S, |primeRectanglePrefixDiscrepancy L U Vlo (a d) d|) := by
      rw [Finset.sum_add_distrib]
    _ ≤ 2 * Bhi + 2 * Blo := add_le_add
      (sum_abs_primeRectanglePrefixDiscrepancy_le_two_mul_of_uniform_selector
        S L U Vhi Mhi Bhi hS hhi a ha)
      (sum_abs_primeRectanglePrefixDiscrepancy_le_two_mul_of_uniform_selector
        S L U Vlo Mlo Blo hS hlo a ha)

/-- The same full-rectangle transfer over the complete inclusive positive
modulus interval. No positivity assumption on `D` is required. -/
theorem sum_abs_primeIntervalRectangle_discrepancy_Icc_le_of_uniform_prefix_selectors
    (D L U Vlo Vhi : ℕ) (Mhi Mlo : ℕ → ℝ) (Bhi Blo : ℝ)
    (hV : Vlo ≤ Vhi)
    (hhi : ∀ b : ℕ → ℕ,
      (∀ d ∈ Finset.Icc 1 D, b d < d ∧ Nat.Coprime (b d) d) →
      (∑ d ∈ Finset.Icc 1 D,
        |primeRectanglePrefixAPCount L U Vhi (b d) d - Mhi d|) ≤ Bhi)
    (hlo : ∀ b : ℕ → ℕ,
      (∀ d ∈ Finset.Icc 1 D, b d < d ∧ Nat.Coprime (b d) d) →
      (∑ d ∈ Finset.Icc 1 D,
        |primeRectanglePrefixAPCount L U Vlo (b d) d - Mlo d|) ≤ Blo)
    (a : ℕ → ℕ) (ha : ∀ d ∈ Finset.Icc 1 D, Nat.Coprime (a d) d) :
    (∑ d ∈ Finset.Icc 1 D,
      |(((primeIntervalRectangle L U Vlo Vhi).filter
          (fun p => Nat.ModEq d (p.1 * p.2) (a d))).card : ℝ) -
        (((primeIntervalRectangle L U Vlo Vhi).filter
          (fun p => Nat.Coprime (p.1 * p.2) d)).card : ℝ) / (Nat.totient d : ℝ)|) ≤
      2 * Bhi + 2 * Blo := by
  apply sum_abs_primeIntervalRectangle_discrepancy_le_of_uniform_prefix_selectors
    (Finset.Icc 1 D) L U Vlo Vhi Mhi Mlo Bhi Blo hV ?_ hhi hlo a ha
  intro d hd
  exact (Finset.mem_Icc.mp hd).1

/-- Actual full grid rectangles inherit the two-prefix transfer at their
literal natural endpoints `ceil (κ ^ i) - 1`. Only `1 < κ` is needed. -/
theorem sum_abs_actualGridRectangleDiscrepancy_le_of_uniform_prefix_selectors
    (S : Finset ℕ) {κ : ℝ} (hκ : 1 < κ) (ij : ℕ × ℕ)
    (Mhi Mlo : ℕ → ℝ) (Bhi Blo : ℝ) (hS : ∀ d ∈ S, 0 < d)
    (hhi : ∀ b : ℕ → ℕ, (∀ d ∈ S, b d < d ∧ Nat.Coprime (b d) d) →
      (∑ d ∈ S,
        |primeRectanglePrefixAPCount
          (Nat.ceil (κ ^ ij.1) - 1) (Nat.ceil (κ ^ (ij.1 + 1)) - 1)
          (Nat.ceil (κ ^ (ij.2 + 1)) - 1) (b d) d - Mhi d|) ≤ Bhi)
    (hlo : ∀ b : ℕ → ℕ, (∀ d ∈ S, b d < d ∧ Nat.Coprime (b d) d) →
      (∑ d ∈ S,
        |primeRectanglePrefixAPCount
          (Nat.ceil (κ ^ ij.1) - 1) (Nat.ceil (κ ^ (ij.1 + 1)) - 1)
          (Nat.ceil (κ ^ ij.2) - 1) (b d) d - Mlo d|) ≤ Blo)
    (a : ℕ → ℕ) (ha : ∀ d ∈ S, Nat.Coprime (a d) d) :
    (∑ d ∈ S, |actualGridRectangleDiscrepancy κ ij (a d) d|) ≤
      2 * Bhi + 2 * Blo := by
  simpa only [actualGridRectangleDiscrepancy,
    actualGridPrimeRectangle_eq_primeIntervalRectangle hκ,
    multiplicativeGridIocEndpoint] using
    (sum_abs_primeIntervalRectangle_discrepancy_le_of_uniform_prefix_selectors
      S (Nat.ceil (κ ^ ij.1) - 1) (Nat.ceil (κ ^ (ij.1 + 1)) - 1)
      (Nat.ceil (κ ^ ij.2) - 1) (Nat.ceil (κ ^ (ij.2 + 1)) - 1)
      Mhi Mlo Bhi Blo (multiplicativeGridIocEndpoint_le_succ hκ ij.2)
      hS hhi hlo a ha)

/-- Application-facing grid specialization on every modulus from `1` to
`D`, including the empty case `D = 0`, with noncanonical primitive targets. -/
theorem sum_abs_actualGridRectangleDiscrepancy_Icc_le_of_uniform_prefix_selectors
    (D : ℕ) {κ : ℝ} (hκ : 1 < κ) (ij : ℕ × ℕ)
    (Mhi Mlo : ℕ → ℝ) (Bhi Blo : ℝ)
    (hhi : ∀ b : ℕ → ℕ,
      (∀ d ∈ Finset.Icc 1 D, b d < d ∧ Nat.Coprime (b d) d) →
      (∑ d ∈ Finset.Icc 1 D,
        |primeRectanglePrefixAPCount
          (Nat.ceil (κ ^ ij.1) - 1) (Nat.ceil (κ ^ (ij.1 + 1)) - 1)
          (Nat.ceil (κ ^ (ij.2 + 1)) - 1) (b d) d - Mhi d|) ≤ Bhi)
    (hlo : ∀ b : ℕ → ℕ,
      (∀ d ∈ Finset.Icc 1 D, b d < d ∧ Nat.Coprime (b d) d) →
      (∑ d ∈ Finset.Icc 1 D,
        |primeRectanglePrefixAPCount
          (Nat.ceil (κ ^ ij.1) - 1) (Nat.ceil (κ ^ (ij.1 + 1)) - 1)
          (Nat.ceil (κ ^ ij.2) - 1) (b d) d - Mlo d|) ≤ Blo)
    (a : ℕ → ℕ) (ha : ∀ d ∈ Finset.Icc 1 D, Nat.Coprime (a d) d) :
    (∑ d ∈ Finset.Icc 1 D, |actualGridRectangleDiscrepancy κ ij (a d) d|) ≤
      2 * Bhi + 2 * Blo := by
  apply sum_abs_actualGridRectangleDiscrepancy_le_of_uniform_prefix_selectors
    (Finset.Icc 1 D) hκ ij Mhi Mlo Bhi Blo ?_ hhi hlo a ha
  intro d hd
  exact (Finset.mem_Icc.mp hd).1

/-- The actual rectangle SUM on the empty positive-modulus interval is zero. -/
@[simp] theorem sum_abs_actualGridRectangleDiscrepancy_Icc_zero
    (κ : ℝ) (ij : ℕ × ℕ) (a : ℕ → ℕ) :
    (∑ d ∈ Finset.Icc 1 0, |actualGridRectangleDiscrepancy κ ij (a d) d|) = 0 := by
  simp

end

end ImbalancedChen
