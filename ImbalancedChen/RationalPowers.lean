import ImbalancedChen.Counting

/-!
# Exact rational exponents and the real-power receiver condition

For a positive natural denominator, the integer-power inequality used by
`ImbalancedReceiver` is equivalent to the literal real-power inequality
`(r : ℝ) ≤ (q : ℝ) ^ ((num : ℝ) / (den : ℝ))`.

The power equivalence holds for all natural bases and numerators, including
zero; primality is needed only in the receiver definition. The denominator
hypothesis is essential. This file introduces no analytic estimates.
-/

namespace ImbalancedChen

/-- Clearing a positive natural denominator in a real-power inequality.
Both bases may be zero, and the numerator may be zero. -/
theorem real_pow_le_iff_le_rpow {r q : ℝ} {num den : ℕ}
    (hr : 0 ≤ r) (hq : 0 ≤ q) (hden : 0 < den) :
    r ^ den ≤ q ^ num ↔ r ≤ q ^ ((num : ℝ) / (den : ℝ)) := by
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  rw [div_eq_mul_inv, Real.rpow_natCast_mul hq,
    Real.le_rpow_inv_iff_of_pos hr (pow_nonneg hq num) hdenR,
    Real.rpow_natCast]

/-- The exact natural-number test agrees with the real-power condition.
No positivity or primality hypotheses on the natural bases are necessary. -/
theorem nat_pow_le_iff_le_rpow {r q num den : ℕ} (hden : 0 < den) :
    r ^ den ≤ q ^ num ↔
      (r : ℝ) ≤ (q : ℝ) ^ ((num : ℝ) / (den : ℝ)) := by
  calc
    r ^ den ≤ q ^ num ↔ (r : ℝ) ^ den ≤ (q : ℝ) ^ num := by norm_cast
    _ ↔ (r : ℝ) ≤ (q : ℝ) ^ ((num : ℝ) / (den : ℝ)) :=
      real_pow_le_iff_le_rpow (Nat.cast_nonneg r) (Nat.cast_nonneg q) hden

/-- Prime or semiprime receivers satisfying the literal real-exponent
imbalance condition. As in `ImbalancedReceiver`, the receiver `1` is excluded. -/
def RealImbalancedReceiver (b : ℝ) (m : ℕ) : Prop :=
  Nat.Prime m ∨
    ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ b

/-- The integer-power receiver definition is exactly the real-exponent
definition at a rational exponent with positive denominator. -/
theorem imbalancedReceiver_iff_realImbalancedReceiver {num den m : ℕ}
    (hden : 0 < den) :
    ImbalancedReceiver num den m ↔
      RealImbalancedReceiver ((num : ℝ) / (den : ℝ)) m := by
  constructor
  · rintro (hm | ⟨r, q, hr, hq, hm, hpow⟩)
    · exact Or.inl hm
    · exact Or.inr ⟨r, q, hr, hq, hm, (nat_pow_le_iff_le_rpow hden).mp hpow⟩
  · rintro (hm | ⟨r, q, hr, hq, hm, hpow⟩)
    · exact Or.inl hm
    · exact Or.inr ⟨r, q, hr, hq, hm, (nat_pow_le_iff_le_rpow hden).mpr hpow⟩

/-- The separate-input manuscript exponent, with division explicitly in `ℝ`. -/
theorem imbalancedReceiver_76407_iff (m : ℕ) :
    ImbalancedReceiver 76407 100000 m ↔
      RealImbalancedReceiver (76407 / 100000 : ℝ) m := by
  exact imbalancedReceiver_iff_realImbalancedReceiver (by norm_num)

/-- The external-input manuscript exponent, with division explicitly in `ℝ`. -/
theorem imbalancedReceiver_74774_iff (m : ℕ) :
    ImbalancedReceiver 74774 100000 m ↔
      RealImbalancedReceiver (74774 / 100000 : ℝ) m := by
  exact imbalancedReceiver_iff_realImbalancedReceiver (by norm_num)

noncomputable section

/-- Additive primes satisfying the literal real-exponent receiver condition,
still counted once per additive prime rather than once per factor witness. -/
def realImbalancedPrimes (b : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun p => Nat.Prime p ∧ RealImbalancedReceiver b (N - p)

/-- Real-exponent version of the imbalanced representation count. -/
def RealDb (b : ℝ) (N : ℕ) : ℕ := (realImbalancedPrimes b N).card

@[simp] theorem mem_realImbalancedPrimes {b : ℝ} {N p : ℕ} :
    p ∈ realImbalancedPrimes b N ↔
      p < N ∧ Nat.Prime p ∧ RealImbalancedReceiver b (N - p) := by
  classical
  simp [realImbalancedPrimes]

theorem imbalancedPrimes_eq_realImbalancedPrimes {num den N : ℕ}
    (hden : 0 < den) :
    imbalancedPrimes num den N = realImbalancedPrimes ((num : ℝ) / (den : ℝ)) N := by
  classical
  ext p
  rw [mem_imbalancedPrimes, mem_realImbalancedPrimes,
    imbalancedReceiver_iff_realImbalancedReceiver hden]

/-- Consequently all bounds for the integer-power count transfer without
loss to the literal real-exponent count. -/
theorem Db_eq_RealDb {num den N : ℕ} (hden : 0 < den) :
    Db num den N = RealDb ((num : ℝ) / (den : ℝ)) N := by
  unfold Db RealDb
  rw [imbalancedPrimes_eq_realImbalancedPrimes hden]

/-- The exact finite counting identity, now with the manuscript's real-power
condition in the accepted count. It still uses the receiver convention that
excludes `1`; the exceptional receiver is handled in `Multiplicity.lean`. -/
theorem D12_eq_RealDb_add_B {num den N : ℕ} (hden : 0 < den) :
    D12 N = RealDb ((num : ℝ) / (den : ℝ)) N + B num den N := by
  rw [← Db_eq_RealDb hden]
  exact D12_eq_Db_add_B num den N

end

end ImbalancedChen
