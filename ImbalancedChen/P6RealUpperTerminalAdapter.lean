import ImbalancedChen.CurrentMainTheorem
import Mathlib.Tactic.FieldSimp

/-!
# P6: the exact real-upper to rational-corollary adapter

This file only connects the frozen all-real P4-B output type to the three
rational finite-count inputs of the already proved current corollary.  The
original constants, denominators and strict numerical margins are reused.
No unconditional lower or upper analytic estimate is asserted here.
-/

namespace ImbalancedChen.P6

noncomputable section

/-- At positive rational exponents the frozen P4-B output supplies the exact
`B` upper estimate consumed by `CurrentNumericalTransfer`. -/
theorem rational_bad_upper_of_real_bad_upper
    {num den : ℕ} (hnum : 0 < num) (hden : 0 < den)
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (RealB ((num : ℝ) / (den : ℝ)) N : ℝ) ≤
          (currentK * Real.log (1 / ((num : ℝ) / (den : ℝ))) + epsilon) *
            singularNormalization N) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (B num den N : ℝ) ≤
          (currentK * Real.log ((den : ℝ) / (num : ℝ)) + epsilon) *
            singularNormalization N := by
  intro epsilon hepsilon
  have hnumR : (num : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hnum
  have hdenR : (den : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hden
  have hrecip : (1 : ℝ) / ((num : ℝ) / (den : ℝ)) =
      (den : ℝ) / (num : ℝ) := by
    field_simp [hnumR, hdenR]
  filter_upwards [hUpper epsilon hepsilon] with N hN
  intro hEven
  simpa only [B_eq_RealB hden, hrecip] using hN hEven

/-- A quantified supplier with the literal frozen P4-B type gives the three
exact rational-count estimates needed by the existing simultaneous corollary.
The lower bound remains the literal P5 analytic obligation. -/
theorem current_corollary_simultaneous_of_all_real_upper
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper : ∀ b : ℝ, (1 : ℝ) / 2 < b → b < 1 →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ N : ℕ in Filter.atTop, Even N →
          (RealB b N : ℝ) ≤
            (currentK * Real.log (1 / b) + epsilon) *
              singularNormalization N) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      singularNormalization N / 100000 ≤
          (RealDb (18704241 / 25000000 : ℝ) N : ℝ) ∧
      singularNormalization N / 1000000 ≤
          (RealDb (14963373 / 20000000 : ℝ) N : ℝ) ∧
      (124889 / 100000 : ℝ) * singularNormalization N ≤
          (RealDb (9 / 10 : ℝ) N : ℝ) := by
  apply current_corollary_simultaneous_of_manuscript_bounds hLower
  · exact rational_bad_upper_of_real_bad_upper
      (num := 18704241) (den := 25000000) (by norm_num) (by norm_num)
      (hUpper _ (by norm_num) (by norm_num))
  · exact rational_bad_upper_of_real_bad_upper
      (num := 14963373) (den := 20000000) (by norm_num) (by norm_num)
      (hUpper _ (by norm_num) (by norm_num))
  · exact rational_bad_upper_of_real_bad_upper
      (num := 9) (den := 10) (by norm_num) (by norm_num)
      (hUpper _ (by norm_num) (by norm_num))

end

end ImbalancedChen.P6
