import ImbalancedChen.CurrentNumericalTransfer

/-!
# Literal representations from the current simultaneous count corollary

This source-only candidate consumes exactly the shared lower-count conclusion
already supplied by `current_corollary_simultaneous_of_manuscript_bounds`.
It introduces no analytic hypotheses. Eventual positivity of the concrete
singular normalization makes each of the three accepted finite sets nonempty.
All thresholds, count bounds, and literal factor witnesses are retained.
-/

namespace ImbalancedChen.P6

noncomputable section

/-- A positive accepted count gives a literal additive representation. -/
theorem exists_literal_representation_of_realDb_pos {b : ℝ} {N : ℕ}
    (hb : 0 ≤ b) (hCount : 0 < RealDb b N) :
    ∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
      N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ b := by
  change 0 < (realImbalancedPrimes b N).card at hCount
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hCount
  obtain ⟨r, q, hpPrime, hr, hq, hEquality, hPower⟩ :=
    exists_representation_of_mem_realImbalancedPrimes hb hp
  exact ⟨p, r, q, hpPrime, hr, hq, hEquality, hPower⟩

/-- Preserve all three current lower counts and extract all three literal
representations at one common threshold, which is at least four.

The hypothesis is the exact conclusion of the existing current simultaneous
count corollary. In particular it is not a restatement of the lower or upper
analytic estimates that feed that corollary. -/
theorem current_corollary_counts_and_literal_of_shared_counts
    (hCounts : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      singularNormalization N / 100000 ≤
          (RealDb (18704241 / 25000000 : ℝ) N : ℝ) ∧
      singularNormalization N / 1000000 ≤
          (RealDb (14963373 / 20000000 : ℝ) N : ℝ) ∧
      (124889 / 100000 : ℝ) * singularNormalization N ≤
          (RealDb (9 / 10 : ℝ) N : ℝ)) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      4 ≤ N ∧
      (singularNormalization N / 100000 ≤
          (RealDb (18704241 / 25000000 : ℝ) N : ℝ) ∧
       singularNormalization N / 1000000 ≤
          (RealDb (14963373 / 20000000 : ℝ) N : ℝ) ∧
       (124889 / 100000 : ℝ) * singularNormalization N ≤
          (RealDb (9 / 10 : ℝ) N : ℝ)) ∧
      (∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧
          (r : ℝ) ≤ (q : ℝ) ^ (18704241 / 25000000 : ℝ)) ∧
      (∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧
          (r : ℝ) ≤ (q : ℝ) ^ (14963373 / 20000000 : ℝ)) ∧
      (∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ (9 / 10 : ℝ)) := by
  obtain ⟨Nc, hCounts⟩ := hCounts
  obtain ⟨Np, hPos⟩ :=
    Filter.eventually_atTop.mp eventually_singularNormalization_pos
  refine ⟨max 4 (max Nc Np), le_max_left _ _, ?_⟩
  intro N hN hEven
  have hNc : Nc ≤ N :=
    le_trans (le_trans (le_max_left Nc Np) (le_max_right 4 (max Nc Np))) hN
  have hNp : Np ≤ N :=
    le_trans (le_trans (le_max_right Nc Np) (le_max_right 4 (max Nc Np))) hN
  have h4 : 4 ≤ N := le_trans (le_max_left 4 (max Nc Np)) hN
  have hPositive : 0 < singularNormalization N := hPos N hNp
  have hCurrent := hCounts N hNc hEven
  have hReal₁ : (0 : ℝ) < (RealDb (18704241 / 25000000 : ℝ) N : ℝ) :=
    lt_of_lt_of_le
      (div_pos hPositive (by norm_num : (0 : ℝ) < 100000)) hCurrent.1
  have hCount₁ : 0 < RealDb (18704241 / 25000000 : ℝ) N := by
    exact_mod_cast hReal₁
  have hReal₂ : (0 : ℝ) < (RealDb (14963373 / 20000000 : ℝ) N : ℝ) :=
    lt_of_lt_of_le
      (div_pos hPositive (by norm_num : (0 : ℝ) < 1000000)) hCurrent.2.1
  have hCount₂ : 0 < RealDb (14963373 / 20000000 : ℝ) N := by
    exact_mod_cast hReal₂
  have hReal₃ : (0 : ℝ) < (RealDb (9 / 10 : ℝ) N : ℝ) :=
    lt_of_lt_of_le
      (mul_pos (by norm_num : (0 : ℝ) < 124889 / 100000) hPositive)
      hCurrent.2.2
  have hCount₃ : 0 < RealDb (9 / 10 : ℝ) N := by
    exact_mod_cast hReal₃
  exact ⟨h4, hCurrent,
    exists_literal_representation_of_realDb_pos
      (by norm_num : (0 : ℝ) ≤ 18704241 / 25000000) hCount₁,
    exists_literal_representation_of_realDb_pos
      (by norm_num : (0 : ℝ) ≤ 14963373 / 20000000) hCount₂,
    exists_literal_representation_of_realDb_pos
      (by norm_num : (0 : ℝ) ≤ 9 / 10) hCount₃⟩

/-- Literal-only form of the same simultaneous current corollary. Each
exponent has its own factor witnesses, and all three share one threshold. -/
theorem current_corollary_literal_of_shared_counts
    (hCounts : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      singularNormalization N / 100000 ≤
          (RealDb (18704241 / 25000000 : ℝ) N : ℝ) ∧
      singularNormalization N / 1000000 ≤
          (RealDb (14963373 / 20000000 : ℝ) N : ℝ) ∧
      (124889 / 100000 : ℝ) * singularNormalization N ≤
          (RealDb (9 / 10 : ℝ) N : ℝ)) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧
          (r : ℝ) ≤ (q : ℝ) ^ (18704241 / 25000000 : ℝ)) ∧
      (∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧
          (r : ℝ) ≤ (q : ℝ) ^ (14963373 / 20000000 : ℝ)) ∧
      (∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ (9 / 10 : ℝ)) := by
  obtain ⟨N₀, h4, hAll⟩ :=
    current_corollary_counts_and_literal_of_shared_counts hCounts
  refine ⟨N₀, h4, ?_⟩
  intro N hN hEven
  exact (hAll N hN hEven).2.2

end

end ImbalancedChen.P6
