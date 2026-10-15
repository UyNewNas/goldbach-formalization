import ImbalancedChen.CurrentChenUpsilon9PrimeSource

/-!
# The actual eighth source has prime or unit quotients

The original second-prime cutoff is retained.  Its lower band gives
p2^3>=N, while a composite rough quotient would have q>=p2^2.  The
actual first prime is greater than one, contradicting the genuine strict
receiver bound p1*p2*q<N.  The generic quotient witness and prime fibre
dictionary already proved in the ninth source are reused unchanged.
The finite equality below preserves all original outer pair labels.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical

theorem currentChenUpsilon8_second_cube_ge {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    (N : ℝ) ≤ (t.2 : ℝ) ^ 3 := by
  obtain ⟨_, _, _, hsecond, _⟩ := Finset.mem_filter.mp ht
  have hcube : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (N : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N) (1 / 3 : ℝ) 3,
      show (1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  calc
    (N : ℝ) = ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := hcube.symm
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg N) _) hsecond 3

/-- Composite quotients are impossible in the literal eighth source.
No factorization, squarefreeness or replacement roughness is assumed. -/
theorem currentChenUpsilon8_quotient_prime_or_one {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) {q : ℕ}
    (hq : q ∈ chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)) :
    q = 1 ∨ Nat.Prime q := by
  obtain ⟨hc, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp hc
  have hp₁ := (mem_chenAdditivePrimeCarrier.mp hc₁).2.1
  have hp₂ := (mem_chenAdditivePrimeCarrier.mp hc₂).2.1
  obtain ⟨hqsource, hrough⟩ := Finset.mem_filter.mp hq
  obtain ⟨_P, _hP, _hmul, hlt, hqpos, _hquot⟩ :=
    currentChenUpsilon9_quotient_witness (mul_pos hp₁.pos hp₂.pos) hqsource
  by_cases hqone : q = 1
  · exact Or.inl hqone
  right
  by_contra hnotprime
  have hminprime := Nat.minFac_prime hqone
  have hroughmin := hrough (Nat.minFac q) hminprime (Nat.minFac_dvd q)
  have hminsq : ((Nat.minFac q : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) := by
    exact_mod_cast Nat.minFac_sq_le_self hqpos hnotprime
  have hqsecond : (t.2 : ℝ) ^ 2 ≤ (q : ℝ) :=
    ((sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr hroughmin).trans hminsq
  have hp₂pos : (0 : ℝ) < t.2 := by exact_mod_cast hp₂.pos
  have hfirst : (1 : ℝ) < t.1 := by exact_mod_cast hp₁.one_lt
  have hstrict : (t.2 : ℝ) ^ 3 < (t.1 : ℝ) * (t.2 : ℝ) ^ 3 := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hfirst (pow_pos hp₂pos 3)
  have hcontradiction : (N : ℝ) < (N : ℝ) := by
    calc
      (N : ℝ) ≤ (t.2 : ℝ) ^ 3 := currentChenUpsilon8_second_cube_ge ht
      _ < (t.1 : ℝ) * (t.2 : ℝ) ^ 3 := hstrict
      _ = ((t.1 : ℝ) * (t.2 : ℝ)) * (t.2 : ℝ) ^ 2 := by ring
      _ ≤ ((t.1 : ℝ) * (t.2 : ℝ)) * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hqsecond (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ < (N : ℝ) := by exact_mod_cast hlt
  exact (lt_irrefl _) hcontradiction

def currentChenUpsilon8PrimeTriples (N : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ) :=
  (chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
    ((N : ℝ) ^ (1 / 3 : ℝ))).sigma fun t =>
      (chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)).filter Nat.Prime

def currentChenUpsilon8UnitFibres (N : ℕ) : Finset (ℕ × ℕ) :=
  (chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
    ((N : ℝ) ^ (1 / 3 : ℝ))).filter fun t =>
      1 ∈ chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)

/-- Every actual prime label and the inclusive roughness q>=p2 remain in
the finite prime-triple dictionary. -/
theorem mem_currentChenUpsilon8PrimeTriples_iff {N p₁ p₂ q : ℕ} :
    (⟨(p₁, p₂), q⟩ : Σ _ : ℕ × ℕ, ℕ) ∈ currentChenUpsilon8PrimeTriples N ↔
      p₁ ∈ chenAdditivePrimeCarrier N ∧ p₂ ∈ chenAdditivePrimeCarrier N ∧
      (N : ℝ) ^ (417 / 5000 : ℝ) ≤ (p₁ : ℝ) ∧
      (p₁ : ℝ) < (N : ℝ) ^ (1 / 3 : ℝ) ∧
      (N : ℝ) ^ (1 / 3 : ℝ) ≤ (p₂ : ℝ) ∧
      (p₂ : ℝ) < Real.sqrt ((N : ℝ) / (p₁ : ℝ)) ∧
      Nat.Prime q ∧ p₁ * p₂ * q < N ∧
      N - p₁ * p₂ * q ∈ chenAdditivePrimeCarrier N ∧ (p₂ : ℝ) ≤ q := by
  simp only [currentChenUpsilon8PrimeTriples, Finset.mem_sigma,
    chenY8PrimeSelector, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, hA, h₁C, hC₂, hcap⟩, hq, hprime⟩
    have hb : 0 < p₁ * p₂ := mul_pos
      (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
    obtain ⟨hlt, hP, hcut⟩ := (currentChenUpsilon9_prime_mem_iff hb hprime _).mp hq
    exact ⟨h₁, h₂, hA, h₁C, hC₂, hcap, hprime, hlt, hP, hcut⟩
  · rintro ⟨h₁, h₂, hA, h₁C, hC₂, hcap, hprime, hlt, hP, hcut⟩
    have hb : 0 < p₁ * p₂ := mul_pos
      (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
    exact ⟨⟨⟨h₁, h₂⟩, hA, h₁C, hC₂, hcap⟩,
      (currentChenUpsilon9_prime_mem_iff hb hprime _).mpr ⟨hlt, hP, hcut⟩, hprime⟩

theorem currentChenUpsilon8_row_card_partition {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    let F := chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)
    F.card = (F.filter Nat.Prime).card + if 1 ∈ F then 1 else 0 := by
  intro F
  have hcompl : F.filter (fun q => ¬ Nat.Prime q) =
      if 1 ∈ F then {1} else ∅ := by
    ext q
    by_cases hunit : 1 ∈ F
    · simp only [hunit, if_true, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hq, hnot⟩
        exact (currentChenUpsilon8_quotient_prime_or_one ht hq).resolve_right hnot
      · rintro rfl
        exact ⟨hunit, Nat.not_prime_one⟩
    · simp only [hunit, if_false, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hq hnot
      have hqone := (currentChenUpsilon8_quotient_prime_or_one ht hq).resolve_right hnot
      exact hunit (hqone ▸ hq)
  have hpartition := Finset.card_filter_add_card_filter_not (s := F) Nat.Prime
  rw [hcompl] at hpartition
  by_cases hunit : 1 ∈ F <;> simpa only [hunit, if_true, if_false,
    Finset.card_singleton, Finset.card_empty] using hpartition.symm

/-- Exact finite equality for the original eighth count, without deleting
unit fibres, pair multiplicity, original target primes or prime endpoints. -/
theorem currentChenUpsilon8_eq_primeTriples_add_unitFibres (N : ℕ) :
    currentChenUpsilon8 N =
      ((currentChenUpsilon8PrimeTriples N).card : ℝ) +
        ((currentChenUpsilon8UnitFibres N).card : ℝ) := by
  rw [currentChenUpsilon8_eq_siftedQuotientPrimeSource]
  have hunitcount : ((currentChenUpsilon8UnitFibres N).card : ℝ) =
      ∑ t ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)),
        if 1 ∈ chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)
        then (1 : ℝ) else 0 := by
    simp only [currentChenUpsilon8UnitFibres, Finset.card_eq_sum_ones,
      Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hunitcount]
  simp only [currentChenUpsilon8PrimeTriples, Finset.card_sigma, Nat.cast_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact_mod_cast currentChenUpsilon8_row_card_partition ht

end

end ImbalancedChen
