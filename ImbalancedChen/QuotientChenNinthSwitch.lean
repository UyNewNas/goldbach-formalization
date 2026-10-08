import ImbalancedChen.QuotientChenInitialCounts
import ImbalancedChen.QuotientChenSwitchGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
# The actual ninth quotient switch in the repaired Chen weight

`Y9` is the cardinality of its literal prime-pair support, with quotient
cutoff `sqrt (N / (p₁*p₂))`. It is not a smallest-two indicator: more than
one pair can contribute. The results below only prove the lower bound
needed in the source branch `r = 0`, `s = 1`, `t ≤ 2`, `k ≥ 3`.

The source-count theorem constructs its factors from `n.primeFactors`.
Four actual distinct prime divisors contradict `H*D*C^2 > N`; squarefreeness
then identifies the receiver with the product of its three actual factors.
The lower size band and roughness supply the ninth quotient cutoff, and
the third factor supplies the strict upper endpoint for the second prime.
-/

namespace ImbalancedChen

noncomputable section

/-- The manuscript's literal ninth nonzero tuple support. All lower
endpoints are inclusive and both displayed upper endpoints are strict. -/
def chenY9Tuples (n : ℕ) (N H D : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (n.primeFactors ×ˢ n.primeFactors).filter fun t =>
    H ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < D ∧ D ≤ (t.2 : ℝ) ∧
    (t.2 : ℝ) < Real.sqrt (N / (t.1 : ℝ)) ∧
    ChenQuotient (t.1 * t.2) (Real.sqrt (N / ((t.1 : ℝ) * (t.2 : ℝ)))) n

def chenY9 (n : ℕ) (N H D : ℝ) : ℕ := (chenY9Tuples n N H D).card

/-- The finite carrier is exactly the actual quotient summand, rather than
an extra restriction on which prime pairs are counted. -/
theorem mem_chenY9Tuples_iff {n p₁ p₂ : ℕ} {N H D : ℝ} (hn : n ≠ 0) :
    (p₁, p₂) ∈ chenY9Tuples n N H D ↔
      Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ H ≤ (p₁ : ℝ) ∧ (p₁ : ℝ) < D ∧
      D ≤ (p₂ : ℝ) ∧ (p₂ : ℝ) < Real.sqrt (N / (p₁ : ℝ)) ∧
      ChenQuotient (p₁ * p₂) (Real.sqrt (N / ((p₁ : ℝ) * (p₂ : ℝ)))) n := by
  classical
  rw [chenY9Tuples, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hrest⟩
    exact ⟨(Nat.mem_primeFactors.mp h₁).1, (Nat.mem_primeFactors.mp h₂).1, hrest⟩
  · rintro ⟨h₁, h₂, hH, hD₁, hD₂, hcap, hQ⟩
    refine ⟨⟨?_, ?_⟩, hH, hD₁, hD₂, hcap, hQ⟩
    · exact Nat.mem_primeFactors.mpr ⟨h₁, (dvd_mul_right p₁ p₂).trans hQ.1, hn⟩
    · exact Nat.mem_primeFactors.mpr ⟨h₂, (dvd_mul_left p₂ p₁).trans hQ.1, hn⟩

/-- The lower receiver band is used through `N ≤ n*p₃`. With an actual
three-prime factorization this proves the literal ninth quotient cutoff. -/
theorem chen_ninth_quotient_of_three_primes {n p₁ p₂ p₃ : ℕ} {N : ℝ}
    (h₁ : Nat.Prime p₁) (h₂ : Nat.Prime p₂) (h₃ : Nat.Prime p₃)
    (heq : n = p₁ * p₂ * p₃) (hN : 0 ≤ N)
    (hlower : N ≤ (n : ℝ) * (p₃ : ℝ)) :
    ChenQuotient (p₁ * p₂) (Real.sqrt (N / ((p₁ : ℝ) * (p₂ : ℝ)))) n := by
  have hp₁ : 0 < (p₁ : ℝ) := by exact_mod_cast h₁.pos
  have hp₂ : 0 < (p₂ : ℝ) := by exact_mod_cast h₂.pos
  have hp₃ : 0 ≤ (p₃ : ℝ) := Nat.cast_nonneg _
  have hp₁₂ := mul_pos hp₁ hp₂
  have hquot : n / (p₁ * p₂) = p₃ := by
    rw [heq]
    exact Nat.mul_div_cancel_left p₃ (mul_pos h₁.pos h₂.pos)
  have heqR : (n : ℝ) = (p₁ : ℝ) * (p₂ : ℝ) * (p₃ : ℝ) := by
    exact_mod_cast heq
  have hsq : N / ((p₁ : ℝ) * (p₂ : ℝ)) ≤ (p₃ : ℝ) ^ 2 := by
    apply (div_le_iff₀ hp₁₂).mpr
    rw [heqR] at hlower
    nlinarith only [hlower]
  have hcut : Real.sqrt (N / ((p₁ : ℝ) * (p₂ : ℝ))) ≤ (p₃ : ℝ) := by
    have hsqrt := Real.sq_sqrt (div_nonneg hN hp₁₂.le)
    have hsqrt_nonneg := Real.sqrt_nonneg (N / ((p₁ : ℝ) * (p₂ : ℝ)))
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact dvd_mul_right (p₁ * p₂) p₃
  · rw [hquot]
    intro q hq hqd
    have heqp : q = p₃ := (Nat.prime_dvd_prime_iff_eq hq h₃).mp hqd
    simpa only [heqp] using hcut

/-- An explicit three-prime witness contributes one actual tuple. This is
only a lower bound; other prime pairs may contribute as well. -/
theorem chenY9_ge_one_of_three_primes {n p₁ p₂ p₃ : ℕ} {N H D : ℝ}
    (h₁ : Nat.Prime p₁) (h₂ : Nat.Prime p₂) (h₃ : Nat.Prime p₃)
    (h₁₂ : p₁ < p₂) (h₂₃ : p₂ < p₃) (heq : n = p₁ * p₂ * p₃)
    (hN : 0 ≤ N) (hnN : (n : ℝ) ≤ N) (hlower : N ≤ (n : ℝ) * (p₃ : ℝ))
    (hH : H ≤ (p₁ : ℝ)) (hD₁ : (p₁ : ℝ) < D) (hD₂ : D ≤ (p₂ : ℝ)) :
    1 ≤ chenY9 n N H D := by
  have hn : n ≠ 0 := by
    rw [heq]
    exact mul_ne_zero (mul_ne_zero h₁.ne_zero h₂.ne_zero) h₃.ne_zero
  have hd₁ : p₁ ∣ n := by
    rw [heq]
    exact dvd_mul_of_dvd_left (dvd_mul_right p₁ p₂) p₃
  have hd₂ : p₂ ∣ n := by
    rw [heq]
    exact dvd_mul_of_dvd_left (dvd_mul_left p₂ p₁) p₃
  have hd₃ : p₃ ∣ n := by
    rw [heq]
    exact dvd_mul_left p₃ (p₁ * p₂)
  have hmem : (p₁, p₂) ∈ chenY9Tuples n N H D :=
    (mem_chenY9Tuples_iff hn).mpr ⟨h₁, h₂, hH, hD₁, hD₂,
      chen_switch_strict_sqrt_cap hn hnN h₁ h₂ h₃ h₁₂ h₂₃ hd₁ hd₂ hd₃,
      chen_ninth_quotient_of_three_primes h₁ h₂ h₃ heq hN hlower⟩
  exact Finset.card_pos.mpr ⟨(p₁, p₂), hmem⟩

/-- With at most two factors strictly below `C`, every factor after the
smallest two is at least `C`. Equality stays on the upper side. -/
theorem ChenSmallestTwo.le_third_of_below_card_le_two {n p₁ p₂ p₃ : ℕ} {C : ℝ}
    (hsmall : ChenSmallestTwo n p₁ p₂) (hn : n ≠ 0)
    (ht : (chenPrimesBelow n C).card ≤ 2)
    (h₃ : Nat.Prime p₃) (hd₃ : p₃ ∣ n) (h₂₃ : p₂ < p₃) :
    C ≤ (p₃ : ℝ) := by
  classical
  by_contra hnot
  have h₃C : (p₃ : ℝ) < C := lt_of_not_ge hnot
  have h₂C : (p₂ : ℝ) < C := lt_trans (by exact_mod_cast h₂₃) h₃C
  have h₁C : (p₁ : ℝ) < C := lt_trans (by exact_mod_cast hsmall.increasing) h₂C
  have hsub : {p₁, p₂, p₃} ⊆ chenPrimesBelow n C := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact (mem_chenPrimesBelow hn).mpr ⟨hsmall.first_prime, hsmall.first_dvd, h₁C⟩
    · exact (mem_chenPrimesBelow hn).mpr ⟨hsmall.second_prime, hsmall.second_dvd, h₂C⟩
    · exact (mem_chenPrimesBelow hn).mpr ⟨h₃, hd₃, h₃C⟩
  have hcard : ({p₁, p₂, p₃} : Finset ℕ).card = 3 := by
    simp [ne_of_lt hsmall.increasing, ne_of_lt h₂₃,
      ne_of_lt (lt_trans hsmall.increasing h₂₃)]
  have hle := Finset.card_le_card hsub
  omega

/-- Four actual prime factors supply two ordered factors beyond the smallest
pair. No desired factorization or tuple-count identity is assumed. -/
theorem ChenSmallestTwo.exists_third_fourth {n p₁ p₂ : ℕ}
    (hsmall : ChenSmallestTwo n p₁ p₂) (hcard : 4 ≤ n.primeFactors.card) :
    ∃ p₃ p₄ : ℕ, Nat.Prime p₃ ∧ Nat.Prime p₄ ∧ p₃ ∣ n ∧ p₄ ∣ n ∧
      p₂ < p₃ ∧ p₃ < p₄ := by
  classical
  obtain ⟨q₃, h₃, hd₃, h₂₃⟩ := hsmall.exists_third (by omega)
  have hex : ∃ q ∈ n.primeFactors, q ≠ p₁ ∧ q ≠ p₂ ∧ q ≠ q₃ := by
    by_contra hnone
    have hsub : n.primeFactors ⊆ {p₁, p₂, q₃} := by
      intro q hq
      by_cases heq₁ : q = p₁
      · simp [heq₁]
      by_cases heq₂ : q = p₂
      · simp [heq₂]
      have heq₃ : q = q₃ := by
        by_contra hne₃
        exact hnone ⟨q, hq, heq₁, heq₂, hne₃⟩
      simp [heq₃]
    have hle : n.primeFactors.card ≤ 3 :=
      (Finset.card_le_card hsub).trans Finset.card_le_three
    omega
  obtain ⟨q₄, hmem₄, hne₁, hne₂, hne₃⟩ := hex
  have h₄ := (Nat.mem_primeFactors.mp hmem₄).1
  have hd₄ := (Nat.mem_primeFactors.mp hmem₄).2.1
  have h₂₄ : p₂ < q₄ := by
    rcases hsmall.least_other q₄ h₄ hd₄ with heq | hle
    · exact (hne₁ heq).elim
    · omega
  by_cases h₃₄ : q₃ < q₄
  · exact ⟨q₃, q₄, h₃, h₄, hd₃, hd₄, h₂₃, h₃₄⟩
  · exact ⟨q₄, q₃, h₄, h₃, hd₄, hd₃, h₂₄, by omega⟩

/-- The actual branch counts exclude four factors using their genuine
product and the receiver upper bound. -/
theorem chen_primeFactors_card_eq_three_of_ninth_branch {n : ℕ} {N H D C : ℝ}
    (hn : n ≠ 0) (hnN : (n : ℝ) ≤ N)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C) (hlarge : N < H * D * C ^ 2)
    (hr : (chenPrimesBelow n H).card = 0)
    (hs : (chenPrimesBelow n D).card = 1)
    (ht : (chenPrimesBelow n C).card ≤ 2) (hk : 3 ≤ n.primeFactors.card) :
    n.primeFactors.card = 3 := by
  obtain ⟨p₁, p₂, hsmall⟩ := chen_exists_smallestTwo (by omega : 2 ≤ n.primeFactors.card)
  have hH₁ := (hsmall.below_card_eq_zero_iff hn).mp hr
  obtain ⟨_, hD₂⟩ := (hsmall.below_card_eq_one_iff hn).mp hs
  by_contra hne
  have hfour : 4 ≤ n.primeFactors.card := by omega
  obtain ⟨p₃, p₄, h₃, h₄, hd₃, hd₄, h₂₃, h₃₄⟩ := hsmall.exists_third_fourth hfour
  have hC₃ := hsmall.le_third_of_below_card_le_two hn ht h₃ hd₃ h₂₃
  have hC₄ := hsmall.le_third_of_below_card_le_two hn ht h₄ hd₄ (lt_trans h₂₃ h₃₄)
  have hd := chen_four_prime_product_dvd hsmall.first_prime hsmall.second_prime h₃ h₄
    hsmall.increasing h₂₃ h₃₄ hsmall.first_dvd hsmall.second_dvd hd₃ hd₄
  have hprod : (p₁ : ℝ) * (p₂ : ℝ) * (p₃ : ℝ) * (p₄ : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have h₁₂ : H * D ≤ (p₁ : ℝ) * (p₂ : ℝ) :=
    mul_le_mul hH₁ hD₂ hD (Nat.cast_nonneg _)
  have h₃₄ : C * C ≤ (p₃ : ℝ) * (p₄ : ℝ) :=
    mul_le_mul hC₃ hC₄ hC (Nat.cast_nonneg _)
  have hlow := mul_le_mul h₁₂ h₃₄ (mul_nonneg hC hC)
    (mul_nonneg (Nat.cast_nonneg p₁) (Nat.cast_nonneg p₂))
  nlinarith only [hlow, hprod, hnN, hlarge]

/-- Three actual distinct prime divisors exhaust a squarefree receiver
whose prime-factor carrier has size three. -/
theorem chen_eq_three_prime_product_of_card {n p₁ p₂ p₃ : ℕ}
    (hn : Squarefree n) (hcard : n.primeFactors.card = 3)
    (hsmall : ChenSmallestTwo n p₁ p₂)
    (h₃ : Nat.Prime p₃) (hd₃ : p₃ ∣ n) (h₂₃ : p₂ < p₃) :
    n = p₁ * p₂ * p₃ := by
  classical
  have hsub : {p₁, p₂, p₃} ⊆ n.primeFactors := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact Nat.mem_primeFactors.mpr ⟨hsmall.first_prime, hsmall.first_dvd, hn.ne_zero⟩
    · exact Nat.mem_primeFactors.mpr ⟨hsmall.second_prime, hsmall.second_dvd, hn.ne_zero⟩
    · exact Nat.mem_primeFactors.mpr ⟨h₃, hd₃, hn.ne_zero⟩
  have hthree : ({p₁, p₂, p₃} : Finset ℕ).card = 3 := by
    simp [ne_of_lt hsmall.increasing, ne_of_lt h₂₃,
      ne_of_lt (lt_trans hsmall.increasing h₂₃)]
  have hset : ({p₁, p₂, p₃} : Finset ℕ) = n.primeFactors :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hprod := Nat.prod_primeFactors_of_squarefree hn
  rw [← hset] at hprod
  simpa [ne_of_lt hsmall.increasing, ne_of_lt h₂₃,
    ne_of_lt (lt_trans hsmall.increasing h₂₃), mul_assoc] using hprod.symm

/-- The repaired ninth switch lower bound from actual source counts.
No factorization, selected tuple, or target count is supplied as a premise. -/
theorem chenY9_ge_one_of_ninth_branch {n : ℕ} {N A H D C : ℝ}
    (hn : Squarefree n) (hrough : ChenPrimeRough A n) (hN : 0 ≤ N)
    (hnN : (n : ℝ) ≤ N) (hlower : N ≤ (n : ℝ) * A)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C) (hlarge : N < H * D * C ^ 2)
    (hr : (chenPrimesBelow n H).card = 0)
    (hs : (chenPrimesBelow n D).card = 1)
    (ht : (chenPrimesBelow n C).card ≤ 2) (hk : 3 ≤ n.primeFactors.card) :
    1 ≤ chenY9 n N H D := by
  have hcard := chen_primeFactors_card_eq_three_of_ninth_branch hn.ne_zero hnN
    hH hD hC hlarge hr hs ht hk
  obtain ⟨p₁, p₂, hsmall⟩ := chen_exists_smallestTwo (by omega : 2 ≤ n.primeFactors.card)
  obtain ⟨p₃, h₃, hd₃, h₂₃⟩ := hsmall.exists_third hk
  have heq := chen_eq_three_prime_product_of_card hn hcard hsmall h₃ hd₃ h₂₃
  have hH₁ := (hsmall.below_card_eq_zero_iff hn.ne_zero).mp hr
  obtain ⟨hD₁, hD₂⟩ := (hsmall.below_card_eq_one_iff hn.ne_zero).mp hs
  have hlower₃ : N ≤ (n : ℝ) * (p₃ : ℝ) :=
    hlower.trans (mul_le_mul_of_nonneg_left (hrough p₃ h₃ hd₃) (Nat.cast_nonneg n))
  exact chenY9_ge_one_of_three_primes hsmall.first_prime hsmall.second_prime h₃
    hsmall.increasing h₂₃ heq hN hnN hlower₃ hH₁ hD₁ hD₂

/-- Exact manuscript exponents imply the four-factor exclusion, strictly. -/
theorem chen_ninth_fixed_cutoffs_product_gt {N : ℝ} (hN : 1 < N) :
    N < N ^ (50 / 309 : ℝ) * N ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)) *
      (N ^ (1 / 3 : ℝ)) ^ 2 := by
  have hNpos : 0 < N := lt_trans zero_lt_one hN
  rw [← Real.rpow_mul_natCast hNpos.le (1 / 3 : ℝ) 2,
    ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
  have he : (1 : ℝ) < (50 / 309 : ℝ) + ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)) +
      (1 / 3 : ℝ) * 2 := by norm_num
  simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hN he

/-- The actual lower size band yields precisely the product needed for the
ninth quotient cutoff; no stronger receiver-size hypothesis is inserted. -/
theorem chen_ninth_lower_product {n : ℕ} {N a : ℝ} (hN : 0 < N)
    (hband : N ^ (1 - a) ≤ (n : ℝ)) : N ≤ (n : ℝ) * N ^ a := by
  calc
    N = N ^ (1 - a) * N ^ a := by rw [← Real.rpow_add hN]; simp
    _ ≤ (n : ℝ) * N ^ a :=
      mul_le_mul_of_nonneg_right hband (Real.rpow_nonneg hN.le _)

/-- The literal repaired-source branch at the manuscript's exact constants.
Only squarefreeness, original size/roughness conditions, and actual prime-
factor counts appear in the assumptions. Coprimality is unnecessary here. -/
theorem chenY9_ge_one_fixed_source_branch {n : ℕ} {N : ℝ}
    (hN : 1 < N) (hn : Squarefree n)
    (hnN : (n : ℝ) ≤ N) (hband : N ^ (1 - (100 / 1149 : ℝ)) ≤ (n : ℝ))
    (hrough : ChenPrimeRough (N ^ (100 / 1149 : ℝ)) n)
    (hr : (chenPrimesBelow n (N ^ (50 / 309 : ℝ))).card = 0)
    (hs : (chenPrimesBelow n (N ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))).card = 1)
    (ht : (chenPrimesBelow n (N ^ (1 / 3 : ℝ))).card ≤ 2)
    (hk : 3 ≤ n.primeFactors.card) :
    1 ≤ chenY9 n N (N ^ (50 / 309 : ℝ))
      (N ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))) := by
  have hNpos : 0 < N := lt_trans zero_lt_one hN
  exact chenY9_ge_one_of_ninth_branch hn hrough hNpos.le hnN
    (chen_ninth_lower_product hNpos hband)
    (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)
    (Real.rpow_nonneg hNpos.le _) (chen_ninth_fixed_cutoffs_product_gt hN)
    hr hs ht hk

end

end ImbalancedChen
