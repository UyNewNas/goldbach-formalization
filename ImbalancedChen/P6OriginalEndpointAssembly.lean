import ImbalancedChen.P6RealUpperTerminalAdapter
import ImbalancedChen.P6CurrentCorollaryLiteral

/-!
# P6 source-only terminal assembly

These imports refer to the intended staged module paths listed in the P6
manifest.  The two actual analytic suppliers do not yet exist unconditionally.
Accordingly this assembly retains both analytic hypotheses explicitly, and
does not declare `current_theorem_1_1` or `current_corollary_simultaneous`.
-/

namespace ImbalancedChen.P6

noncomputable section

/-- Exact all-real upper interface to the original three literal corollaries.
Each exponent has its own witnesses and the original common threshold. -/
theorem current_literal_corollary_of_all_real_upper
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper : ∀ b : ℝ, (1 : ℝ) / 2 < b → b < 1 →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ N : ℕ in Filter.atTop, Even N →
          (RealB b N : ℝ) ≤
            (currentK * Real.log (1 / b) + epsilon) *
              singularNormalization N) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧
          (r : ℝ) ≤ (q : ℝ) ^ (18704241 / 25000000 : ℝ)) ∧
      (∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧
          (r : ℝ) ≤ (q : ℝ) ^ (14963373 / 20000000 : ℝ)) ∧
      (∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ (9 / 10 : ℝ)) := by
  exact current_corollary_literal_of_shared_counts
    (current_corollary_simultaneous_of_all_real_upper hLower hUpper)

end

end ImbalancedChen.P6
