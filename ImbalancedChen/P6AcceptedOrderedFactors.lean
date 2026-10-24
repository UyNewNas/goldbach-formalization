import ImbalancedChen.CurrentMainTheorem

/-!
# Canonical accepted prime factors below exponent one

Acceptance forces the first prime factor to be strictly smaller than the
second. Thus ordering the accepted region costs no witnesses, prime squares
cannot be accepted, and its ordered prime factors are unique. These arithmetic
statements need only `b < 1`; in particular they apply throughout `0 ≤ b < 1`.

Source-only draft: not compiled or kernel checked in this continuation.
-/

namespace ImbalancedChen.P6

/-- Every accepted two-prime witness below exponent one is already strictly
ordered. In fact only primality of the second factor is needed. -/
theorem accepted_prime_factors_lt {b : ℝ} {r q : ℕ}
    (hb : b < 1) (hq : Nat.Prime q)
    (haccepted : (r : ℝ) ≤ (q : ℝ) ^ b) : r < q := by
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq.one_lt
  have hpow : (q : ℝ) ^ b < (q : ℝ) :=
    Real.rpow_lt_self_of_one_lt hqR hb
  have hrqR : (r : ℝ) < (q : ℝ) := haccepted.trans_lt hpow
  exact_mod_cast hrqR

/-- An accepted receiver has canonical ordered prime factors, or is prime.
The result holds for every exponent below one, including `0 ≤ b < 1`. -/
theorem realImbalancedReceiver_iff_prime_or_ordered_factors
    {b : ℝ} {m : ℕ} (hb : b < 1) :
    RealImbalancedReceiver b m ↔
      Nat.Prime m ∨
        ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧ r ≤ q ∧
          (r : ℝ) ≤ (q : ℝ) ^ b := by
  constructor
  · rintro (hm | ⟨r, q, hr, hq, hm, haccepted⟩)
    · exact Or.inl hm
    · exact Or.inr ⟨r, q, hr, hq, hm,
        (accepted_prime_factors_lt hb hq haccepted).le, haccepted⟩
  · rintro (hm | ⟨r, q, hr, hq, hm, _, haccepted⟩)
    · exact Or.inl hm
    · exact Or.inr ⟨r, q, hr, hq, hm, haccepted⟩

/-- The accepted two-prime region can equivalently use strict ordering. -/
theorem realImbalancedReceiver_iff_prime_or_strict_factors
    {b : ℝ} {m : ℕ} (hb : b < 1) :
    RealImbalancedReceiver b m ↔
      Nat.Prime m ∨
        ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧ r < q ∧
          (r : ℝ) ≤ (q : ℝ) ^ b := by
  constructor
  · rintro (hm | ⟨r, q, hr, hq, hm, haccepted⟩)
    · exact Or.inl hm
    · exact Or.inr ⟨r, q, hr, hq, hm,
        accepted_prime_factors_lt hb hq haccepted, haccepted⟩
  · rintro (hm | ⟨r, q, hr, hq, hm, _, haccepted⟩)
    · exact Or.inl hm
    · exact Or.inr ⟨r, q, hr, hq, hm, haccepted⟩

/-- Ordered accepted prime factors are unique, independently of the exponent.
This reuses uniqueness of multiplication of two primes. -/
theorem ordered_accepted_prime_factors_unique
    {b : ℝ} {m r q s t : ℕ}
    (hr : Nat.Prime r) (hq : Nat.Prime q)
    (hs : Nat.Prime s) (ht : Nat.Prime t)
    (hmrq : m = r * q) (hmst : m = s * t)
    (hrq : r ≤ q) (hst : s ≤ t)
    (_hrpow : (r : ℝ) ≤ (q : ℝ) ^ b)
    (_hspow : (s : ℝ) ≤ (t : ℝ) ^ b) :
    r = s ∧ q = t := by
  exact ordered_prime_factors_unique hr hq hs ht hrq hst
    (hmrq.symm.trans hmst)

/-- Below exponent one, acceptance alone supplies both order hypotheses, so
any two accepted prime-factor witnesses agree without an explicit ordering. -/
theorem accepted_prime_factors_unique
    {b : ℝ} {m r q s t : ℕ} (hb : b < 1)
    (hr : Nat.Prime r) (hq : Nat.Prime q)
    (hs : Nat.Prime s) (ht : Nat.Prime t)
    (hmrq : m = r * q) (hmst : m = s * t)
    (hrpow : (r : ℝ) ≤ (q : ℝ) ^ b)
    (hspow : (s : ℝ) ≤ (t : ℝ) ^ b) :
    r = s ∧ q = t := by
  exact ordered_accepted_prime_factors_unique hr hq hs ht hmrq hmst
    (accepted_prime_factors_lt hb hq hrpow).le
    (accepted_prime_factors_lt hb ht hspow).le hrpow hspow

/-- A prime square cannot be an accepted receiver below exponent one. The
proof excludes every possible prime-factor witness using factor uniqueness. -/
theorem prime_square_not_realImbalancedReceiver
    {b : ℝ} {r : ℕ} (hb : b < 1) (hr : Nat.Prime r) :
    ¬ RealImbalancedReceiver b (r * r) := by
  rintro (hprime | ⟨s, t, hs, ht, hst, haccepted⟩)
  · exact (Nat.not_prime_mul hr.ne_one hr.ne_one) hprime
  · have hlt : s < t := accepted_prime_factors_lt hb ht haccepted
    have hsame : s = r ∧ t = r :=
      ordered_prime_factors_unique hs ht hr hr hlt.le (le_refl r) hst.symm
    omega

/-- The accepted semiprime branch has a unique ordered factor pair. This
states uniqueness of witnesses explicitly, rather than only pairwise equality. -/
theorem realImbalancedReceiver_iff_prime_or_existsUnique_ordered_factors
    {b : ℝ} {m : ℕ} (hb : b < 1) :
    RealImbalancedReceiver b m ↔
      Nat.Prime m ∨
        ∃! factors : ℕ × ℕ,
          Nat.Prime factors.1 ∧ Nat.Prime factors.2 ∧
            m = factors.1 * factors.2 ∧ factors.1 ≤ factors.2 ∧
              (factors.1 : ℝ) ≤ (factors.2 : ℝ) ^ b := by
  rw [realImbalancedReceiver_iff_prime_or_ordered_factors hb]
  constructor
  · rintro (hm | ⟨r, q, hr, hq, hm, hrq, hrpow⟩)
    · exact Or.inl hm
    · apply Or.inr
      refine ⟨(r, q), ⟨hr, hq, hm, hrq, hrpow⟩, ?_⟩
      rintro ⟨s, t⟩ ⟨hs, ht, hmst, hst, hspow⟩
      have hsame : r = s ∧ q = t :=
        ordered_accepted_prime_factors_unique hr hq hs ht hm hmst
          hrq hst hrpow hspow
      exact Prod.ext hsame.1.symm hsame.2.symm
  · rintro (hm | ⟨⟨r, q⟩, ⟨hr, hq, hm, hrq, hrpow⟩, _⟩)
    · exact Or.inl hm
    · exact Or.inr ⟨r, q, hr, hq, hm, hrq, hrpow⟩

end ImbalancedChen.P6
