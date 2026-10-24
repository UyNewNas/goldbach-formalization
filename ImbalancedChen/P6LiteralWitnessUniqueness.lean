import ImbalancedChen.P6LiteralCountEquiv
import ImbalancedChen.P6AcceptedOrderedFactors

/-!
# Unique literal factor witnesses below exponent one

The unit-factor witnesses representing prime receivers cannot coincide with
products of two primes. In the two-prime branch, acceptance below exponent one
already determines the factor order, so the existing accepted-factor uniqueness
lemma applies. Thus at `0 ≤ b < 1`, membership has exactly one literal pair.

Source-only draft. Its two imports name intended staged modules; the checkpoint
records the current draft source locations and hashes.
-/

namespace ImbalancedChen.P6

/-- For fixed `N` and additive prime position `p`, any two literal factor
witnesses agree below exponent one, including the unit-factor prime case.
Only uniqueness is asserted here, so nonnegativity of `b` is unnecessary. -/
theorem P6_literal_factors_unique
    {b : ℝ} {N p r q s t : ℕ} (hb : b < 1)
    (hr : r = 1 ∨ Nat.Prime r) (hq : Nat.Prime q)
    (hs : s = 1 ∨ Nat.Prime s) (ht : Nat.Prime t)
    (hNrq : N = p + r * q) (hNst : N = p + s * t)
    (hrpow : (r : ℝ) ≤ (q : ℝ) ^ b)
    (hspow : (s : ℝ) ≤ (t : ℝ) ^ b) :
    r = s ∧ q = t := by
  have hprod : r * q = s * t := by omega
  rcases hr with rfl | hr
  · rcases hs with rfl | hs
    · exact ⟨rfl, by simpa only [one_mul] using hprod⟩
    · have hqeq : q = s * t := by simpa only [one_mul] using hprod
      have hprime : Nat.Prime (s * t) := by
        rw [← hqeq]
        exact hq
      exact ((Nat.not_prime_mul hs.ne_one ht.ne_one) hprime).elim
  · rcases hs with rfl | hs
    · have hteq : r * q = t := by simpa only [one_mul] using hprod
      have hprime : Nat.Prime (r * q) := by
        rw [hteq]
        exact ht
      exact ((Nat.not_prime_mul hr.ne_one hq.ne_one) hprime).elim
    · exact accepted_prime_factors_unique hb hr hq hs ht
        (rfl : r * q = r * q) hprod hrpow hspow

/-- At a nonnegative exponent below one, each additive prime counted by
`RealDb` has one and only one manuscript literal factor pair. The converse
uses the earlier literal membership bridge. -/
theorem P6_mem_realImbalancedPrimes_iff_existsUnique_literal
    {b : ℝ} {N p : ℕ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    p ∈ realImbalancedPrimes b N ↔
      ∃! factors : ℕ × ℕ,
        Nat.Prime p ∧ (factors.1 = 1 ∨ Nat.Prime factors.1) ∧
          Nat.Prime factors.2 ∧ N = p + factors.1 * factors.2 ∧
            (factors.1 : ℝ) ≤ (factors.2 : ℝ) ^ b := by
  constructor
  · intro hmem
    obtain ⟨r, q, hp, hr, hq, hNrq, hrpow⟩ :=
      (P6_mem_realImbalancedPrimes_iff_literal hb0).mp hmem
    refine ⟨(r, q), ⟨hp, hr, hq, hNrq, hrpow⟩, ?_⟩
    rintro ⟨s, t⟩ ⟨_, hs, ht, hNst, hspow⟩
    have hsame : r = s ∧ q = t :=
      P6_literal_factors_unique hb1 hr hq hs ht hNrq hNst hrpow hspow
    exact Prod.ext hsame.1.symm hsame.2.symm
  · rintro ⟨⟨r, q⟩, ⟨hp, hr, hq, hNrq, hrpow⟩, _⟩
    exact P6_mem_realImbalancedPrimes_of_literal hp hr hq hNrq hrpow

end ImbalancedChen.P6
