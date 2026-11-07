import ImbalancedChen.QuotientChenFourCounts
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Find

/-!
# Actual two-prime switching geometry for the repaired Chen weight

The finite sets below are the literal quotient supports of `Y7` and `Y8`.
Their quotient cutoff is the second selected prime, and every upper square-
root endpoint is strict. The actual quotient support forces the selected
pair to be the unique smallest two prime divisors. Squarefreeness supplies
the converse, including the vacuous roughness condition at quotient one.

The strict square-root cap is proved from an actual third prime divisor,
not assumed as part of a scalar count identity. A cardinality hypothesis on
`n.primeFactors` constructs both the smallest pair and that third divisor.
Consequently the final indicator identities count the actual tuple sets.

`Y9` has a different quotient cutoff and is deliberately not included in
these smallest-two or indicator identities. The full `Y11` definition is
imported unchanged.
-/

namespace ImbalancedChen

/-- Distinct actual prime divisors give divisibility of their product. -/
theorem chen_switch_pair_product_dvd {n p₁ p₂ : ℕ}
    (h₁ : Nat.Prime p₁) (h₂ : Nat.Prime p₂) (h₁₂ : p₁ < p₂)
    (hd₁ : p₁ ∣ n) (hd₂ : p₂ ∣ n) : p₁ * p₂ ∣ n := by
  exact ((Nat.coprime_primes h₁ h₂).mpr (ne_of_lt h₁₂)).mul_dvd_of_dvd_of_dvd hd₁ hd₂

/-- A third distinct prime divisor supplies the genuine size product. -/
theorem chen_switch_triple_product_dvd {n p₁ p₂ p₃ : ℕ}
    (h₁ : Nat.Prime p₁) (h₂ : Nat.Prime p₂) (h₃ : Nat.Prime p₃)
    (h₁₂ : p₁ < p₂) (h₂₃ : p₂ < p₃)
    (hd₁ : p₁ ∣ n) (hd₂ : p₂ ∣ n) (hd₃ : p₃ ∣ n) :
    p₁ * p₂ * p₃ ∣ n := by
  have hc₁₃ : p₁.Coprime p₃ :=
    (Nat.coprime_primes h₁ h₃).mpr (ne_of_lt (lt_trans h₁₂ h₂₃))
  have hc₂₃ : p₂.Coprime p₃ :=
    (Nat.coprime_primes h₂ h₃).mpr (ne_of_lt h₂₃)
  exact (Nat.coprime_mul_iff_left.mpr ⟨hc₁₃, hc₂₃⟩).mul_dvd_of_dvd_of_dvd
    (chen_switch_pair_product_dvd h₁ h₂ h₁₂ hd₁ hd₂) hd₃

/-- The forward implication does not need squarefreeness. -/
theorem chenSmallestTwo_of_quotient_pair {n p₁ p₂ : ℕ}
    (h₁ : Nat.Prime p₁) (h₂ : Nat.Prime p₂) (h₁₂ : p₁ < p₂)
    (hQ : ChenQuotient (p₁ * p₂) (p₂ : ℝ) n) :
    ChenSmallestTwo n p₁ p₂ := by
  have hd₁ : p₁ ∣ p₁ * p₂ := dvd_mul_right p₁ p₂
  have hd₂ : p₂ ∣ p₁ * p₂ := dvd_mul_left p₂ p₁
  have hprod : (p₁ * p₂) * (n / (p₁ * p₂)) = n := Nat.mul_div_cancel' hQ.1
  refine ⟨h₁, h₂, hd₁.trans hQ.1, hd₂.trans hQ.1, h₁₂, ?_⟩
  intro q hq hqn
  have hqprod : q ∣ (p₁ * p₂) * (n / (p₁ * p₂)) := by rwa [hprod]
  rcases hq.dvd_mul.mp hqprod with hprefix | hquotient
  · have hcases : q = p₁ ∨ q = p₂ := by
      simpa only [hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq h₁,
        Nat.prime_dvd_prime_iff_eq hq h₂] using hprefix
    rcases hcases with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr le_rfl
  · exact Or.inr (by exact_mod_cast hQ.2 q hq hquotient)

/-- Removing the smallest pair of a squarefree integer leaves a quotient
rough at the second prime. This also covers a residual quotient of one. -/
theorem ChenSmallestTwo.quotient_pair {n p₁ p₂ : ℕ}
    (hsmall : ChenSmallestTwo n p₁ p₂) (hn : Squarefree n) :
    ChenQuotient (p₁ * p₂) (p₂ : ℝ) n := by
  have hd := chen_switch_pair_product_dvd hsmall.first_prime hsmall.second_prime
    hsmall.increasing hsmall.first_dvd hsmall.second_dvd
  have hprod : (p₁ * p₂) * (n / (p₁ * p₂)) = n := Nat.mul_div_cancel' hd
  refine ⟨hd, ?_⟩
  intro q hq hquotient
  have hqn : q ∣ n := by
    rw [← hprod]
    exact dvd_mul_of_dvd_right hquotient _
  rcases hsmall.least_other q hq hqn with heq | hle
  · subst q
    have hsquare : p₁ * p₁ ∣ n := by
      rw [← hprod]
      exact mul_dvd_mul (dvd_mul_right p₁ p₂) hquotient
    exact (Nat.squarefree_iff_prime_squarefree.mp hn p₁ hsmall.first_prime hsquare).elim
  · exact_mod_cast hle

theorem chenQuotient_pair_iff_smallestTwo {n p₁ p₂ : ℕ}
    (hn : Squarefree n) (h₁ : Nat.Prime p₁) (h₂ : Nat.Prime p₂) (h₁₂ : p₁ < p₂) :
    ChenQuotient (p₁ * p₂) (p₂ : ℝ) n ↔ ChenSmallestTwo n p₁ p₂ := by
  exact ⟨chenSmallestTwo_of_quotient_pair h₁ h₂ h₁₂, fun h => h.quotient_pair hn⟩

/-- Construct the smallest pair from the actual finite prime-factor carrier.
No existence or uniqueness of a desired tuple is supplied as a hypothesis. -/
theorem chen_exists_smallestTwo {n : ℕ} (hcard : 2 ≤ n.primeFactors.card) :
    ∃ p₁ p₂ : ℕ, ChenSmallestTwo n p₁ p₂ := by
  classical
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (by omega : 0 < n.primeFactors.card)
  have hex₁ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ n :=
    ⟨q, (Nat.mem_primeFactors.mp hq).1, (Nat.mem_primeFactors.mp hq).2.1⟩
  let p₁ := Nat.find hex₁
  have hp₁ : Nat.Prime p₁ ∧ p₁ ∣ n := Nat.find_spec hex₁
  have hleast₁ : ∀ p : ℕ, Nat.Prime p → p ∣ n → p₁ ≤ p := by
    intro p hp hpd
    exact Nat.find_min' hex₁ ⟨hp, hpd⟩
  have hex₂ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ p ≠ p₁ := by
    by_contra hnone
    have hsub : n.primeFactors ⊆ {p₁} := by
      intro p hp
      have hprime := (Nat.mem_primeFactors.mp hp).1
      have hdvd := (Nat.mem_primeFactors.mp hp).2.1
      have heq : p = p₁ := by
        by_contra hne
        exact hnone ⟨p, hprime, hdvd, hne⟩
      simpa only [Finset.mem_singleton] using heq
    have hle := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hle
    omega
  let p₂ := Nat.find hex₂
  have hp₂ : Nat.Prime p₂ ∧ p₂ ∣ n ∧ p₂ ≠ p₁ := Nat.find_spec hex₂
  refine ⟨p₁, p₂, hp₁.1, hp₂.1, hp₁.2, hp₂.2.1, ?_, ?_⟩
  · have hle := hleast₁ p₂ hp₂.1 hp₂.2.1
    have hne := hp₂.2.2
    omega
  · intro p hp hpd
    by_cases heq : p = p₁
    · exact Or.inl heq
    · exact Or.inr (Nat.find_min' hex₂ ⟨hp, hpd, heq⟩)

/-- At least three actual prime factors supply an actual later prime. -/
theorem ChenSmallestTwo.exists_third {n p₁ p₂ : ℕ}
    (hsmall : ChenSmallestTwo n p₁ p₂) (hcard : 3 ≤ n.primeFactors.card) :
    ∃ p₃ : ℕ, Nat.Prime p₃ ∧ p₃ ∣ n ∧ p₂ < p₃ := by
  classical
  have hex : ∃ q ∈ n.primeFactors, q ≠ p₁ ∧ q ≠ p₂ := by
    by_contra hnone
    have hsub : n.primeFactors ⊆ {p₁, p₂} := by
      intro q hq
      by_cases h₁ : q = p₁
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl h₁
      · have h₂ : q = p₂ := by
          by_contra h₂
          exact hnone ⟨q, hq, h₁, h₂⟩
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr h₂
    have hle : n.primeFactors.card ≤ 2 :=
      (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  obtain ⟨p₃, hmem, hne₁, hne₂⟩ := hex
  have hp₃ := (Nat.mem_primeFactors.mp hmem).1
  have hd₃ := (Nat.mem_primeFactors.mp hmem).2.1
  refine ⟨p₃, hp₃, hd₃, ?_⟩
  rcases hsmall.least_other p₃ hp₃ hd₃ with heq | hle
  · exact (hne₁ heq).elim
  · omega

/-- The strict switching cap follows from three actual distinct prime
factors and the receiver bound. It does not need a quotient-count premise. -/
theorem chen_switch_strict_sqrt_cap {n p₁ p₂ p₃ : ℕ} {N : ℝ}
    (hn : n ≠ 0) (hnN : (n : ℝ) ≤ N)
    (h₁ : Nat.Prime p₁) (h₂ : Nat.Prime p₂) (h₃ : Nat.Prime p₃)
    (h₁₂ : p₁ < p₂) (h₂₃ : p₂ < p₃)
    (hd₁ : p₁ ∣ n) (hd₂ : p₂ ∣ n) (hd₃ : p₃ ∣ n) :
    (p₂ : ℝ) < Real.sqrt (N / (p₁ : ℝ)) := by
  have hd := chen_switch_triple_product_dvd h₁ h₂ h₃ h₁₂ h₂₃ hd₁ hd₂ hd₃
  have hprod : (p₁ : ℝ) * (p₂ : ℝ) * (p₃ : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have hp₁ : 0 < (p₁ : ℝ) := by exact_mod_cast h₁.pos
  have hp₂ : 0 < (p₂ : ℝ) := by exact_mod_cast h₂.pos
  have h₂₃R : (p₂ : ℝ) < (p₃ : ℝ) := by exact_mod_cast h₂₃
  have hstrict := mul_lt_mul_of_pos_left h₂₃R (mul_pos hp₁ hp₂)
  have hsq : (p₂ : ℝ) ^ 2 < N / (p₁ : ℝ) := by
    apply (lt_div_iff₀ hp₁).mpr
    nlinarith [hprod.trans hnN]
  have hnonneg : 0 ≤ N / (p₁ : ℝ) := (sq_nonneg (p₂ : ℝ)).trans hsq.le
  have hsqrt := Real.sq_sqrt hnonneg
  have hsqrt_nonneg := Real.sqrt_nonneg (N / (p₁ : ℝ))
  nlinarith

/-- The square-root cap is automatic for the actual smallest two when there
are at least three distinct prime factors. -/
theorem ChenSmallestTwo.strict_sqrt_cap {n p₁ p₂ : ℕ} {N : ℝ}
    (hsmall : ChenSmallestTwo n p₁ p₂) (hn : n ≠ 0)
    (hcard : 3 ≤ n.primeFactors.card) (hnN : (n : ℝ) ≤ N) :
    (p₂ : ℝ) < Real.sqrt (N / (p₁ : ℝ)) := by
  obtain ⟨p₃, hp₃, hd₃, h₂₃⟩ := hsmall.exists_third hcard
  exact chen_switch_strict_sqrt_cap hn hnN hsmall.first_prime hsmall.second_prime hp₃
    hsmall.increasing h₂₃ hsmall.first_dvd hsmall.second_dvd hd₃

noncomputable section

/-- Literal finite support of `Y7`: `D ≤ p₁ < p₂ < sqrt(N/p₁)` and the
actual quotient by `p₁*p₂` is `p₂`-rough. -/
def chenY7Tuples (n : ℕ) (N D : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (n.primeFactors ×ˢ n.primeFactors).filter fun t =>
    D ≤ (t.1 : ℝ) ∧ t.1 < t.2 ∧
    (t.2 : ℝ) < Real.sqrt (N / (t.1 : ℝ)) ∧
    ChenQuotient (t.1 * t.2) (t.2 : ℝ) n

/-- Literal finite support of `Y8`, preserving the lower ownership at `C`. -/
def chenY8Tuples (n : ℕ) (N A C : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (n.primeFactors ×ˢ n.primeFactors).filter fun t =>
    A ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < C ∧ C ≤ (t.2 : ℝ) ∧
    (t.2 : ℝ) < Real.sqrt (N / (t.1 : ℝ)) ∧
    ChenQuotient (t.1 * t.2) (t.2 : ℝ) n

def chenY7 (n : ℕ) (N D : ℝ) : ℕ := (chenY7Tuples n N D).card

def chenY8 (n : ℕ) (N A C : ℝ) : ℕ := (chenY8Tuples n N A C).card

theorem mem_chenY7Tuples_iff {n p₁ p₂ : ℕ} {N D : ℝ} (hn : n ≠ 0) :
    (p₁, p₂) ∈ chenY7Tuples n N D ↔
      Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ D ≤ (p₁ : ℝ) ∧ p₁ < p₂ ∧
      (p₂ : ℝ) < Real.sqrt (N / (p₁ : ℝ)) ∧
      ChenQuotient (p₁ * p₂) (p₂ : ℝ) n := by
  classical
  rw [chenY7Tuples, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hrest⟩
    exact ⟨(Nat.mem_primeFactors.mp h₁).1, (Nat.mem_primeFactors.mp h₂).1, hrest⟩
  · rintro ⟨h₁, h₂, hD, h₁₂, hcap, hQ⟩
    refine ⟨⟨?_, ?_⟩, hD, h₁₂, hcap, hQ⟩
    · exact Nat.mem_primeFactors.mpr ⟨h₁, (dvd_mul_right p₁ p₂).trans hQ.1, hn⟩
    · exact Nat.mem_primeFactors.mpr ⟨h₂, (dvd_mul_left p₂ p₁).trans hQ.1, hn⟩

theorem mem_chenY8Tuples_iff {n p₁ p₂ : ℕ} {N A C : ℝ} (hn : n ≠ 0) :
    (p₁, p₂) ∈ chenY8Tuples n N A C ↔
      Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ A ≤ (p₁ : ℝ) ∧ (p₁ : ℝ) < C ∧
      C ≤ (p₂ : ℝ) ∧ (p₂ : ℝ) < Real.sqrt (N / (p₁ : ℝ)) ∧
      ChenQuotient (p₁ * p₂) (p₂ : ℝ) n := by
  classical
  rw [chenY8Tuples, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hrest⟩
    exact ⟨(Nat.mem_primeFactors.mp h₁).1, (Nat.mem_primeFactors.mp h₂).1, hrest⟩
  · rintro ⟨h₁, h₂, hA, h₁C, hC₂, hcap, hQ⟩
    refine ⟨⟨?_, ?_⟩, hA, h₁C, hC₂, hcap, hQ⟩
    · exact Nat.mem_primeFactors.mpr ⟨h₁, (dvd_mul_right p₁ p₂).trans hQ.1, hn⟩
    · exact Nat.mem_primeFactors.mpr ⟨h₂, (dvd_mul_left p₂ p₁).trans hQ.1, hn⟩

/-- Exact support reduction, still displaying the actual strict upper cap. -/
theorem mem_chenY7Tuples_iff_smallestTwo {n p₁ p₂ : ℕ} {N D : ℝ}
    (hn : Squarefree n) :
    (p₁, p₂) ∈ chenY7Tuples n N D ↔
      ChenSmallestTwo n p₁ p₂ ∧ D ≤ (p₁ : ℝ) ∧
      (p₂ : ℝ) < Real.sqrt (N / (p₁ : ℝ)) := by
  rw [mem_chenY7Tuples_iff hn.ne_zero]
  constructor
  · rintro ⟨h₁, h₂, hD, h₁₂, hcap, hQ⟩
    exact ⟨chenSmallestTwo_of_quotient_pair h₁ h₂ h₁₂ hQ, hD, hcap⟩
  · rintro ⟨hsmall, hD, hcap⟩
    exact ⟨hsmall.first_prime, hsmall.second_prime, hD, hsmall.increasing,
      hcap, hsmall.quotient_pair hn⟩

theorem mem_chenY8Tuples_iff_smallestTwo {n p₁ p₂ : ℕ} {N A C : ℝ}
    (hn : Squarefree n) :
    (p₁, p₂) ∈ chenY8Tuples n N A C ↔
      ChenSmallestTwo n p₁ p₂ ∧ A ≤ (p₁ : ℝ) ∧ (p₁ : ℝ) < C ∧
      C ≤ (p₂ : ℝ) ∧ (p₂ : ℝ) < Real.sqrt (N / (p₁ : ℝ)) := by
  rw [mem_chenY8Tuples_iff hn.ne_zero]
  constructor
  · rintro ⟨h₁, h₂, hA, h₁C, hC₂, hcap, hQ⟩
    have h₁₂ : p₁ < p₂ := by exact_mod_cast lt_of_lt_of_le h₁C hC₂
    exact ⟨chenSmallestTwo_of_quotient_pair h₁ h₂ h₁₂ hQ, hA, h₁C, hC₂, hcap⟩
  · rintro ⟨hsmall, hA, h₁C, hC₂, hcap⟩
    exact ⟨hsmall.first_prime, hsmall.second_prime, hA, h₁C, hC₂,
      hcap, hsmall.quotient_pair hn⟩

/-- The actual `Y7` tuple set is either empty or the singleton smallest pair. -/
theorem chenY7Tuples_eq_singleton_or_empty {n q₁ q₂ : ℕ} {N D : ℝ}
    (hn : Squarefree n) (hsmall : ChenSmallestTwo n q₁ q₂)
    (hcard : 3 ≤ n.primeFactors.card) (hnN : (n : ℝ) ≤ N) :
    chenY7Tuples n N D = if D ≤ (q₁ : ℝ) then {(q₁, q₂)} else ∅ := by
  classical
  have hcap := hsmall.strict_sqrt_cap hn.ne_zero hcard hnN
  ext ⟨p₁, p₂⟩
  rw [mem_chenY7Tuples_iff_smallestTwo hn]
  by_cases hD : D ≤ (q₁ : ℝ)
  · rw [if_pos hD, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, _, _⟩
      obtain ⟨rfl, rfl⟩ := hp.unique hsmall
      rfl
    · intro heq
      have h₁ := congrArg Prod.fst heq
      have h₂ := congrArg Prod.snd heq
      dsimp at h₁ h₂
      subst p₁ p₂
      exact ⟨hsmall, hD, hcap⟩
  · simp only [if_neg hD, Finset.notMem_empty, iff_false]
    rintro ⟨hp, hpD, _⟩
    obtain ⟨rfl, rfl⟩ := hp.unique hsmall
    exact hD hpD

/-- The `Y8` singleton reduction keeps both sides of its split endpoint. -/
theorem chenY8Tuples_eq_singleton_or_empty {n q₁ q₂ : ℕ} {N A C : ℝ}
    (hn : Squarefree n) (hsmall : ChenSmallestTwo n q₁ q₂)
    (hcard : 3 ≤ n.primeFactors.card) (hnN : (n : ℝ) ≤ N) :
    chenY8Tuples n N A C =
      if A ≤ (q₁ : ℝ) ∧ (q₁ : ℝ) < C ∧ C ≤ (q₂ : ℝ)
      then {(q₁, q₂)} else ∅ := by
  classical
  have hcap := hsmall.strict_sqrt_cap hn.ne_zero hcard hnN
  ext ⟨p₁, p₂⟩
  rw [mem_chenY8Tuples_iff_smallestTwo hn]
  by_cases hcut : A ≤ (q₁ : ℝ) ∧ (q₁ : ℝ) < C ∧ C ≤ (q₂ : ℝ)
  · rw [if_pos hcut, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, _, _, _, _⟩
      obtain ⟨rfl, rfl⟩ := hp.unique hsmall
      rfl
    · intro heq
      have h₁ := congrArg Prod.fst heq
      have h₂ := congrArg Prod.snd heq
      dsimp at h₁ h₂
      subst p₁ p₂
      exact ⟨hsmall, hcut.1, hcut.2.1, hcut.2.2, hcap⟩
  · simp only [if_neg hcut, Finset.notMem_empty, iff_false]
    rintro ⟨hp, hA, h₁C, hC₂, _⟩
    obtain ⟨rfl, rfl⟩ := hp.unique hsmall
    exact hcut ⟨hA, h₁C, hC₂⟩

/-- The first actual prime factor detects a zero strict-cutoff count. -/
theorem ChenSmallestTwo.below_card_eq_zero_iff {n q₁ q₂ : ℕ} {D : ℝ}
    (hsmall : ChenSmallestTwo n q₁ q₂) (hn : n ≠ 0) :
    (chenPrimesBelow n D).card = 0 ↔ D ≤ (q₁ : ℝ) := by
  classical
  constructor
  · intro hzero
    by_contra hD
    have hmem := (mem_chenPrimesBelow hn).mpr
      ⟨hsmall.first_prime, hsmall.first_dvd, lt_of_not_ge hD⟩
    have hempty := Finset.card_eq_zero.mp hzero
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  · intro hD
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hprime, hdvd, hpD⟩ := (mem_chenPrimesBelow hn).mp hp
    rcases hsmall.least_other p hprime hdvd with heq | hle
    · subst p
      exact (not_lt_of_ge hD) hpD
    · have hq₁p : (q₁ : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast le_trans (le_of_lt hsmall.increasing) hle
      exact (not_lt_of_ge (hD.trans hq₁p)) hpD

/-- Exactly one actual prime below the cut means the cut separates the
smallest two, with equality belonging to the upper side. -/
theorem ChenSmallestTwo.below_card_eq_one_iff {n q₁ q₂ : ℕ} {C : ℝ}
    (hsmall : ChenSmallestTwo n q₁ q₂) (hn : n ≠ 0) :
    (chenPrimesBelow n C).card = 1 ↔ (q₁ : ℝ) < C ∧ C ≤ (q₂ : ℝ) := by
  classical
  constructor
  · intro hone
    have hq₁C : (q₁ : ℝ) < C := by
      by_contra hnot
      have hzero := (hsmall.below_card_eq_zero_iff hn).mpr (le_of_not_gt hnot)
      omega
    refine ⟨hq₁C, ?_⟩
    by_contra hnot
    have hm₁ := (mem_chenPrimesBelow hn).mpr
      ⟨hsmall.first_prime, hsmall.first_dvd, hq₁C⟩
    have hm₂ := (mem_chenPrimesBelow hn).mpr
      ⟨hsmall.second_prime, hsmall.second_dvd, lt_of_not_ge hnot⟩
    obtain ⟨p, hset⟩ := Finset.card_eq_one.mp hone
    rw [hset, Finset.mem_singleton] at hm₁ hm₂
    have hinc := hsmall.increasing
    omega
  · rintro ⟨hq₁C, hC₂⟩
    have hset : chenPrimesBelow n C = {q₁} := by
      ext p
      rw [mem_chenPrimesBelow hn, Finset.mem_singleton]
      constructor
      · rintro ⟨hprime, hdvd, hpC⟩
        rcases hsmall.least_other p hprime hdvd with heq | hle
        · exact heq
        · have hlep : (q₂ : ℝ) ≤ (p : ℝ) := by exact_mod_cast hle
          exact ((not_lt_of_ge (hC₂.trans hlep)) hpC).elim
      · rintro rfl
        exact ⟨hsmall.first_prime, hsmall.first_dvd, hq₁C⟩
    rw [hset, Finset.card_singleton]

/-- Actual `Y7 = 1_{s=0}`, where `s` is the number of prime divisors below
`D`. The smallest pair and its strict cap are constructed in the proof. -/
theorem chenY7_eq_indicator_zero {n : ℕ} {N D : ℝ}
    (hn : Squarefree n) (hcard : 3 ≤ n.primeFactors.card) (hnN : (n : ℝ) ≤ N) :
    chenY7 n N D = if (chenPrimesBelow n D).card = 0 then 1 else 0 := by
  classical
  obtain ⟨q₁, q₂, hsmall⟩ := chen_exists_smallestTwo (by omega : 2 ≤ n.primeFactors.card)
  unfold chenY7
  rw [chenY7Tuples_eq_singleton_or_empty hn hsmall hcard hnN]
  simp only [hsmall.below_card_eq_zero_iff hn.ne_zero]
  by_cases hD : D ≤ (q₁ : ℝ) <;> simp [hD]

/-- Actual `Y8 = 1_{t=1}` on the rough squarefree source with at least three
prime factors. No desired count, smallest pair, or square-root cap is assumed. -/
theorem chenY8_eq_indicator_one {n : ℕ} {N A C : ℝ}
    (hn : Squarefree n) (hrough : ChenPrimeRough A n)
    (hcard : 3 ≤ n.primeFactors.card) (hnN : (n : ℝ) ≤ N) :
    chenY8 n N A C = if (chenPrimesBelow n C).card = 1 then 1 else 0 := by
  classical
  obtain ⟨q₁, q₂, hsmall⟩ := chen_exists_smallestTwo (by omega : 2 ≤ n.primeFactors.card)
  have hA := hrough q₁ hsmall.first_prime hsmall.first_dvd
  unfold chenY8
  rw [chenY8Tuples_eq_singleton_or_empty hn hsmall hcard hnN]
  simp only [hsmall.below_card_eq_one_iff hn.ne_zero]
  by_cases hcut : (q₁ : ℝ) < C ∧ C ≤ (q₂ : ℝ) <;> simp [hA, hcut]

end

end ImbalancedChen
