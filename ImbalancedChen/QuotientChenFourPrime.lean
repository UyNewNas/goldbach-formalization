import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# The actual four-prime quotient switch in the repaired Chen weight

The roughness condition below is imposed on `n / b`, not on `n`.  In
particular, `1` is rough at every real threshold.  For four distinct increasing
prime factors of a squarefree integer, quotient roughness at the second prime
is equivalent to the first two primes being the smallest two prime divisors.

The two finite tuple sets are exactly the nonzero domains of the manuscript's
`Y10` and `Y11 full`: they retain strict ordering and strict upper endpoints.
The last endpoint is a free parameter `D`, to be specialized to `N ^ d`; no
fourth-prime contraction is made.  The membership theorems explicitly bridge
the finite prime-factor carrier to the literal divisibility/quotient predicates.
No analytic estimate or scalar replacement of a tuple count is assumed.
-/

namespace ImbalancedChen

/-- Prime-divisor roughness, with the usual vacuous convention at `1`. -/
def ChenPrimeRough (y : ℝ) (m : ℕ) : Prop :=
  ∀ q : ℕ, Nat.Prime q → q ∣ m → y ≤ (q : ℝ)

/-- The support of the manuscript's actual quotient indicator `Q_b(y;n)`. -/
def ChenQuotient (b : ℕ) (y : ℝ) (n : ℕ) : Prop :=
  b ∣ n ∧ ChenPrimeRough y (n / b)

@[simp] theorem chenPrimeRough_one (y : ℝ) : ChenPrimeRough y 1 := by
  intro q hq hq1
  exact (hq.ne_one (Nat.dvd_one.mp hq1)).elim

/-- An intrinsic characterization of the smallest two distinct prime divisors. -/
structure ChenSmallestTwo (n p₁ p₂ : ℕ) : Prop where
  first_prime : Nat.Prime p₁
  second_prime : Nat.Prime p₂
  first_dvd : p₁ ∣ n
  second_dvd : p₂ ∣ n
  increasing : p₁ < p₂
  least_other : ∀ q : ℕ, Nat.Prime q → q ∣ n → q = p₁ ∨ p₂ ≤ q

theorem ChenSmallestTwo.unique {n p₁ p₂ q₁ q₂ : ℕ}
    (hp : ChenSmallestTwo n p₁ p₂) (hq : ChenSmallestTwo n q₁ q₂) :
    p₁ = q₁ ∧ p₂ = q₂ := by
  have hq₁ := hp.least_other q₁ hq.first_prime hq.first_dvd
  have hp₁ := hq.least_other p₁ hp.first_prime hp.first_dvd
  have hfirst : p₁ = q₁ := by
    have hpi := hp.increasing
    have hqi := hq.increasing
    omega
  have hq₂ := hp.least_other q₂ hq.second_prime hq.second_dvd
  have hp₂ := hq.least_other p₂ hp.second_prime hp.second_dvd
  have hpi := hp.increasing
  have hqi := hq.increasing
  exact ⟨hfirst, by omega⟩

/-- Multiplying distinct prime divisors does not assume the desired quotient
condition. This is the ordinary coprime-divisibility bridge. -/
theorem chen_four_prime_product_dvd {n p₁ p₂ p₃ p₄ : ℕ}
    (h₁ : Nat.Prime p₁) (h₂ : Nat.Prime p₂)
    (h₃ : Nat.Prime p₃) (h₄ : Nat.Prime p₄)
    (h₁₂ : p₁ < p₂) (h₂₃ : p₂ < p₃) (h₃₄ : p₃ < p₄)
    (hd₁ : p₁ ∣ n) (hd₂ : p₂ ∣ n) (hd₃ : p₃ ∣ n) (hd₄ : p₄ ∣ n) :
    p₁ * p₂ * p₃ * p₄ ∣ n := by
  have hc₁₂ : p₁.Coprime p₂ :=
    (Nat.coprime_primes h₁ h₂).mpr (ne_of_lt h₁₂)
  have hc₁₃ : p₁.Coprime p₃ :=
    (Nat.coprime_primes h₁ h₃).mpr (ne_of_lt (lt_trans h₁₂ h₂₃))
  have hc₂₃ : p₂.Coprime p₃ :=
    (Nat.coprime_primes h₂ h₃).mpr (ne_of_lt h₂₃)
  have hc₁₄ : p₁.Coprime p₄ :=
    (Nat.coprime_primes h₁ h₄).mpr (ne_of_lt (lt_trans (lt_trans h₁₂ h₂₃) h₃₄))
  have hc₂₄ : p₂.Coprime p₄ :=
    (Nat.coprime_primes h₂ h₄).mpr (ne_of_lt (lt_trans h₂₃ h₃₄))
  have hc₃₄ : p₃.Coprime p₄ :=
    (Nat.coprime_primes h₃ h₄).mpr (ne_of_lt h₃₄)
  have hd₁₂ : p₁ * p₂ ∣ n := hc₁₂.mul_dvd_of_dvd_of_dvd hd₁ hd₂
  have hc₁₂₃ : (p₁ * p₂).Coprime p₃ :=
    Nat.coprime_mul_iff_left.mpr ⟨hc₁₃, hc₂₃⟩
  have hd₁₂₃ : p₁ * p₂ * p₃ ∣ n := hc₁₂₃.mul_dvd_of_dvd_of_dvd hd₁₂ hd₃
  have hc₁₂₃₄ : (p₁ * p₂ * p₃).Coprime p₄ :=
    Nat.coprime_mul_iff_left.mpr
      ⟨Nat.coprime_mul_iff_left.mpr ⟨hc₁₄, hc₂₄⟩, hc₃₄⟩
  exact hc₁₂₃₄.mul_dvd_of_dvd_of_dvd hd₁₂₃ hd₄

/-- The actual quotient condition forces the first two selected primes to be
the smallest two. Squarefreeness is needed for the converse: the removed first
prime cannot still divide the quotient. -/
theorem chenQuotient_four_iff_smallestTwo {n p₁ p₂ p₃ p₄ : ℕ}
    (hn : Squarefree n)
    (h₁ : Nat.Prime p₁) (h₂ : Nat.Prime p₂)
    (h₃ : Nat.Prime p₃) (h₄ : Nat.Prime p₄)
    (h₁₂ : p₁ < p₂) (h₂₃ : p₂ < p₃) (h₃₄ : p₃ < p₄)
    (hd : p₁ * p₂ * p₃ * p₄ ∣ n) :
    ChenQuotient (p₁ * p₂ * p₃ * p₄) (p₂ : ℝ) n ↔
      ChenSmallestTwo n p₁ p₂ := by
  have hd₁ : p₁ ∣ p₁ * p₂ * p₃ * p₄ := by
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right p₁ p₂) p₃) p₄
  have hd₂ : p₂ ∣ p₁ * p₂ * p₃ * p₄ := by
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left p₂ p₁) p₃) p₄
  have hprod : (p₁ * p₂ * p₃ * p₄) * (n / (p₁ * p₂ * p₃ * p₄)) = n :=
    Nat.mul_div_cancel' hd
  constructor
  · rintro ⟨_, hrough⟩
    refine ⟨h₁, h₂, hd₁.trans hd, hd₂.trans hd, h₁₂, ?_⟩
    intro q hq hqn
    have hqprod : q ∣ (p₁ * p₂ * p₃ * p₄) * (n / (p₁ * p₂ * p₃ * p₄)) := by
      rwa [hprod]
    rcases hq.dvd_mul.mp hqprod with hprefix | hquotient
    · have hcases : q = p₁ ∨ q = p₂ ∨ q = p₃ ∨ q = p₄ := by
        simpa only [hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq h₁,
          Nat.prime_dvd_prime_iff_eq hq h₂, Nat.prime_dvd_prime_iff_eq hq h₃,
          Nat.prime_dvd_prime_iff_eq hq h₄, or_assoc] using hprefix
      rcases hcases with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr le_rfl
      · exact Or.inr (le_of_lt h₂₃)
      · exact Or.inr (le_of_lt (lt_trans h₂₃ h₃₄))
    · exact Or.inr (by exact_mod_cast hrough q hq hquotient)
  · intro hsmall
    refine ⟨hd, ?_⟩
    intro q hq hquotient
    have hqn : q ∣ n := by
      rw [← hprod]
      exact dvd_mul_of_dvd_right hquotient _
    rcases hsmall.least_other q hq hqn with heq | hle
    · subst q
      have hsquare : p₁ * p₁ ∣ n := by
        rw [← hprod]
        exact mul_dvd_mul hd₁ hquotient
      exact (Nat.squarefree_iff_prime_squarefree.mp hn p₁ h₁ hsquare).elim
    · exact_mod_cast hle

noncomputable section

/-- Four selected prime divisors, grouped as the first pair and the last pair. -/
def chenFourPrimeCarrier (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (n.primeFactors ×ˢ n.primeFactors) ×ˢ (n.primeFactors ×ˢ n.primeFactors)

/-- The literal nonzero tuple support of `Y10`, with cutoffs `A = N^a`,
`H = N^h`. The quotient condition has not been replaced by scalar data. -/
def chenY10Tuples (n : ℕ) (A H : ℝ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := by
  classical
  exact (chenFourPrimeCarrier n).filter fun t =>
    A ≤ (t.1.1 : ℝ) ∧ t.1.1 < t.1.2 ∧ t.1.2 < t.2.1 ∧ t.2.1 < t.2.2 ∧
    (t.2.2 : ℝ) < H ∧
    ChenQuotient (t.1.1 * t.1.2 * t.2.1 * t.2.2) (t.1.2 : ℝ) n

/-- The literal full `Y11` support. The fourth factor ranges over `[H,D)`;
specializing `D = N^d` retains the manuscript's full endpoint. -/
def chenY11FullTuples (n : ℕ) (A H D : ℝ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := by
  classical
  exact (chenFourPrimeCarrier n).filter fun t =>
    A ≤ (t.1.1 : ℝ) ∧ t.1.1 < t.1.2 ∧ t.1.2 < t.2.1 ∧
    (t.2.1 : ℝ) < H ∧ H ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < D ∧
    ChenQuotient (t.1.1 * t.1.2 * t.2.1 * t.2.2) (t.1.2 : ℝ) n

theorem mem_chenFourPrimeCarrier {n p₁ p₂ p₃ p₄ : ℕ} (hn : n ≠ 0) :
    ((p₁, p₂), (p₃, p₄)) ∈ chenFourPrimeCarrier n ↔
      (Nat.Prime p₁ ∧ p₁ ∣ n) ∧ (Nat.Prime p₂ ∧ p₂ ∣ n) ∧
      (Nat.Prime p₃ ∧ p₃ ∣ n) ∧ (Nat.Prime p₄ ∧ p₄ ∣ n) := by
  simp only [chenFourPrimeCarrier, Finset.mem_product]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    obtain ⟨hp₁, hd₁, _⟩ := Nat.mem_primeFactors.mp h₁
    obtain ⟨hp₂, hd₂, _⟩ := Nat.mem_primeFactors.mp h₂
    obtain ⟨hp₃, hd₃, _⟩ := Nat.mem_primeFactors.mp h₃
    obtain ⟨hp₄, hd₄, _⟩ := Nat.mem_primeFactors.mp h₄
    exact ⟨⟨hp₁, hd₁⟩, ⟨hp₂, hd₂⟩, ⟨hp₃, hd₃⟩, ⟨hp₄, hd₄⟩⟩
  · rintro ⟨⟨hp₁, hd₁⟩, ⟨hp₂, hd₂⟩, ⟨hp₃, hd₃⟩, ⟨hp₄, hd₄⟩⟩
    exact ⟨⟨Nat.mem_primeFactors.mpr ⟨hp₁, hd₁, hn⟩,
      Nat.mem_primeFactors.mpr ⟨hp₂, hd₂, hn⟩⟩,
      Nat.mem_primeFactors.mpr ⟨hp₃, hd₃, hn⟩,
      Nat.mem_primeFactors.mpr ⟨hp₄, hd₄, hn⟩⟩

/-- Exact bridge to the manuscript's `Y10` summand: no ambient carrier
restriction remains on the right-hand side. -/
theorem mem_chenY10Tuples_iff {n p₁ p₂ p₃ p₄ : ℕ} {A H : ℝ}
    (hn : n ≠ 0) :
    ((p₁, p₂), (p₃, p₄)) ∈ chenY10Tuples n A H ↔
      Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ Nat.Prime p₃ ∧ Nat.Prime p₄ ∧
      A ≤ (p₁ : ℝ) ∧ p₁ < p₂ ∧ p₂ < p₃ ∧ p₃ < p₄ ∧ (p₄ : ℝ) < H ∧
      ChenQuotient (p₁ * p₂ * p₃ * p₄) (p₂ : ℝ) n := by
  classical
  rw [chenY10Tuples, Finset.mem_filter, mem_chenFourPrimeCarrier hn]
  constructor
  · rintro ⟨⟨⟨h₁, _⟩, ⟨h₂, _⟩, ⟨h₃, _⟩, ⟨h₄, _⟩⟩, hrest⟩
    exact ⟨h₁, h₂, h₃, h₄, hrest⟩
  · rintro ⟨h₁, h₂, h₃, h₄, hrest⟩
    have hd := hrest.2.2.2.2.2.1
    refine ⟨⟨⟨h₁, ?_⟩, ⟨h₂, ?_⟩, ⟨h₃, ?_⟩, ⟨h₄, ?_⟩⟩, hrest⟩
    · exact (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right p₁ p₂) p₃) p₄).trans hd
    · exact (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left p₂ p₁) p₃) p₄).trans hd
    · exact (dvd_mul_of_dvd_left (dvd_mul_left p₃ (p₁ * p₂)) p₄).trans hd
    · exact (dvd_mul_left p₄ (p₁ * p₂ * p₃)).trans hd

/-- On squarefree integers, the actual `Y10` support is exactly the smallest
two factors followed by any two increasing prime factors below `H`. -/
theorem mem_chenY10Tuples_iff_smallestTwo {n p₁ p₂ p₃ p₄ : ℕ} {A H : ℝ}
    (hn : Squarefree n) :
    ((p₁, p₂), (p₃, p₄)) ∈ chenY10Tuples n A H ↔
      ChenSmallestTwo n p₁ p₂ ∧
      (Nat.Prime p₃ ∧ p₃ ∣ n) ∧ (Nat.Prime p₄ ∧ p₄ ∣ n) ∧
      A ≤ (p₁ : ℝ) ∧ p₂ < p₃ ∧ p₃ < p₄ ∧ (p₄ : ℝ) < H := by
  classical
  rw [chenY10Tuples, Finset.mem_filter, mem_chenFourPrimeCarrier hn.ne_zero]
  constructor
  · rintro ⟨⟨⟨h₁, hd₁⟩, ⟨h₂, hd₂⟩, ⟨h₃, hd₃⟩, ⟨h₄, hd₄⟩⟩,
      hA, h₁₂, h₂₃, h₃₄, hH, hQ⟩
    exact ⟨(chenQuotient_four_iff_smallestTwo hn h₁ h₂ h₃ h₄ h₁₂ h₂₃ h₃₄ hQ.1).mp hQ,
      ⟨h₃, hd₃⟩, ⟨h₄, hd₄⟩, hA, h₂₃, h₃₄, hH⟩
  · rintro ⟨hsmall, ⟨h₃, hd₃⟩, ⟨h₄, hd₄⟩, hA, h₂₃, h₃₄, hH⟩
    have hd := chen_four_prime_product_dvd hsmall.first_prime hsmall.second_prime h₃ h₄
      hsmall.increasing h₂₃ h₃₄ hsmall.first_dvd hsmall.second_dvd hd₃ hd₄
    refine ⟨⟨⟨hsmall.first_prime, hsmall.first_dvd⟩,
      ⟨hsmall.second_prime, hsmall.second_dvd⟩, ⟨h₃, hd₃⟩, ⟨h₄, hd₄⟩⟩,
      hA, hsmall.increasing, h₂₃, h₃₄, hH, ?_⟩
    exact (chenQuotient_four_iff_smallestTwo hn hsmall.first_prime hsmall.second_prime
      h₃ h₄ hsmall.increasing h₂₃ h₃₄ hd).mpr hsmall

/-- The full `Y11` support is the smallest two factors, one later factor
strictly below `H`, and one factor in the complete interval `[H,D)`. -/
theorem mem_chenY11FullTuples_iff_smallestTwo {n p₁ p₂ p₃ p₄ : ℕ} {A H D : ℝ}
    (hn : Squarefree n) :
    ((p₁, p₂), (p₃, p₄)) ∈ chenY11FullTuples n A H D ↔
      ChenSmallestTwo n p₁ p₂ ∧
      (Nat.Prime p₃ ∧ p₃ ∣ n) ∧ (Nat.Prime p₄ ∧ p₄ ∣ n) ∧
      A ≤ (p₁ : ℝ) ∧ p₂ < p₃ ∧ (p₃ : ℝ) < H ∧ H ≤ (p₄ : ℝ) ∧ (p₄ : ℝ) < D := by
  classical
  rw [chenY11FullTuples, Finset.mem_filter, mem_chenFourPrimeCarrier hn.ne_zero]
  constructor
  · rintro ⟨⟨⟨h₁, hd₁⟩, ⟨h₂, hd₂⟩, ⟨h₃, hd₃⟩, ⟨h₄, hd₄⟩⟩,
      hA, h₁₂, h₂₃, h₃H, hH₄, h₄D, hQ⟩
    have h₃₄ : p₃ < p₄ := by exact_mod_cast (lt_of_lt_of_le h₃H hH₄)
    exact ⟨(chenQuotient_four_iff_smallestTwo hn h₁ h₂ h₃ h₄ h₁₂ h₂₃ h₃₄ hQ.1).mp hQ,
      ⟨h₃, hd₃⟩, ⟨h₄, hd₄⟩, hA, h₂₃, h₃H, hH₄, h₄D⟩
  · rintro ⟨hsmall, ⟨h₃, hd₃⟩, ⟨h₄, hd₄⟩, hA, h₂₃, h₃H, hH₄, h₄D⟩
    have h₃₄ : p₃ < p₄ := by exact_mod_cast (lt_of_lt_of_le h₃H hH₄)
    have hd := chen_four_prime_product_dvd hsmall.first_prime hsmall.second_prime h₃ h₄
      hsmall.increasing h₂₃ h₃₄ hsmall.first_dvd hsmall.second_dvd hd₃ hd₄
    refine ⟨⟨⟨hsmall.first_prime, hsmall.first_dvd⟩,
      ⟨hsmall.second_prime, hsmall.second_dvd⟩, ⟨h₃, hd₃⟩, ⟨h₄, hd₄⟩⟩,
      hA, hsmall.increasing, h₂₃, h₃H, hH₄, h₄D, ?_⟩
    exact (chenQuotient_four_iff_smallestTwo hn hsmall.first_prime hsmall.second_prime
      h₃ h₄ hsmall.increasing h₂₃ h₃₄ hd).mpr hsmall

end

end ImbalancedChen
