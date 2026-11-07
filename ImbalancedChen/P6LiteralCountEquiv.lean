import ImbalancedChen.RationalPowers

/-!
# P6: literal representations and the real-exponent count

This draft supplies the converse of the existing membership-to-representation
theorem and packages the resulting equivalence as positivity and vanishing
criteria for `RealDb`. The finite set still counts distinct additive primes.
The nonnegative-exponent hypothesis is needed only in the existing forward
direction, which represents a prime receiver using the factor `r = 1`.

This file is an uncompiled source-review draft.
-/

namespace ImbalancedChen.P6

noncomputable section

/-- A literal representation gives membership. In particular the two allowed
forms of `r` make the receiver positive, which supplies the finite range bound.
This direction does not require a sign hypothesis on the exponent. -/
theorem P6_mem_realImbalancedPrimes_of_literal
    {b : ℝ} {N p r q : ℕ}
    (hp : Nat.Prime p) (hr : r = 1 ∨ Nat.Prime r)
    (hq : Nat.Prime q) (hN : N = p + r * q)
    (hpow : (r : ℝ) ≤ (q : ℝ) ^ b) :
    p ∈ realImbalancedPrimes b N := by
  have hrpos : 0 < r := by
    rcases hr with hrOne | hrPrime
    · omega
    · exact hrPrime.pos
  have hreceiverpos : 0 < r * q := mul_pos hrpos hq.pos
  have hpN : p < N := by omega
  have hsub : N - p = r * q := by omega
  apply mem_realImbalancedPrimes.mpr
  refine ⟨hpN, hp, ?_⟩
  rcases hr with hrOne | hrPrime
  · apply Or.inl
    rw [hsub, hrOne, one_mul]
    exact hq
  · exact Or.inr ⟨r, q, hrPrime, hq, hsub, hpow⟩

/-- Membership is necessary and sufficient for the manuscript's literal
representation at a nonnegative exponent. The forward implication reuses the
existing theorem rather than reproving it. -/
theorem P6_mem_realImbalancedPrimes_iff_literal
    {b : ℝ} {N p : ℕ} (hb : 0 ≤ b) :
    p ∈ realImbalancedPrimes b N ↔
      ∃ r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ b := by
  constructor
  · exact exists_representation_of_mem_realImbalancedPrimes hb
  · rintro ⟨r, q, hp, hr, hq, hN, hpow⟩
    exact P6_mem_realImbalancedPrimes_of_literal hp hr hq hN hpow

/-- A positive real-exponent count is equivalent to an actual literal
representation. The existential quantifiers assert existence, and do not
change the convention of counting each additive prime only once. -/
theorem P6_RealDb_pos_iff_literal
    {b : ℝ} {N : ℕ} (hb : 0 ≤ b) :
    0 < RealDb b N ↔
      ∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ b := by
  classical
  constructor
  · intro hpos
    change 0 < (realImbalancedPrimes b N).card at hpos
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    obtain ⟨r, q, hpPrime, hr, hq, hN, hpow⟩ :=
      (P6_mem_realImbalancedPrimes_iff_literal hb).mp hp
    exact ⟨p, r, q, hpPrime, hr, hq, hN, hpow⟩
  · rintro ⟨p, r, q, hp, hr, hq, hN, hpow⟩
    change 0 < (realImbalancedPrimes b N).card
    apply Finset.card_pos.mpr
    exact ⟨p, P6_mem_realImbalancedPrimes_of_literal hp hr hq hN hpow⟩

/-- The real-exponent count vanishes exactly when no literal representation
exists. No lower bound on `N`, parity hypothesis, or analytic estimate is used. -/
theorem P6_RealDb_eq_zero_iff_no_literal
    {b : ℝ} {N : ℕ} (hb : 0 ≤ b) :
    RealDb b N = 0 ↔
      ¬ ∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ b := by
  constructor
  · intro hzero hliteral
    have hpos : 0 < RealDb b N :=
      (P6_RealDb_pos_iff_literal hb).mpr hliteral
    omega
  · intro hnone
    have hnpos : ¬ 0 < RealDb b N := by
      intro hpos
      exact hnone ((P6_RealDb_pos_iff_literal hb).mp hpos)
    omega

end

end ImbalancedChen.P6
