import ImbalancedChen.QuotientChenWeightCases
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# A uniform positive bound for the actual Chen weight

The estimate here applies to every positive receiver at most `N`, without
squarefreeness or the lower size band. Nonrough receivers have nonpositive
weight. A receiver rough at `N^(100/1149)` has at most eleven distinct prime
factors, since their product divides the receiver. The two positive pair
supports each lie in the square of that actual prime-factor carrier.
-/

namespace ImbalancedChen

open scoped BigOperators

noncomputable section

/-- The distinct prime-factor product is at least the roughness cutoff to
the actual number of factors. Multiplicities do not need to be bounded. -/
theorem chen_pow_primeFactors_card_le {n : ℕ} {A : ℝ}
    (hn : n ≠ 0) (hA : 0 ≤ A) (hrough : ChenPrimeRough A n) :
    A ^ n.primeFactors.card ≤ (n : ℝ) := by
  classical
  have hprod : (∏ p ∈ n.primeFactors, p) ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
  calc
    A ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, A :=
      (Finset.prod_const A).symm
    _ ≤ ∏ p ∈ n.primeFactors, (p : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact hA
      · intro p hp
        obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
        exact hrough p hprime hdvd
    _ ≤ (n : ℝ) := by
      have hcast : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hprod
      simpa only [Nat.cast_prod] using hcast

/-- The fixed roughness cutoff bounds the number of distinct prime factors
by eleven on the whole positive range, including `N = n = 1`. -/
theorem chen_primeFactors_card_le_eleven_of_fixed_rough {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) (hn : n ≠ 0) (hnN : (n : ℝ) ≤ N)
    (hrough : ChenPrimeRough (N ^ (100 / 1149 : ℝ)) n) :
    n.primeFactors.card ≤ 11 := by
  classical
  by_cases hN₁ : N = 1
  · subst N
    have hnle : n ≤ 1 := by exact_mod_cast hnN
    have hn₁ : n = 1 := by omega
    subst n
    simp
  have hNgt : 1 < N := lt_of_le_of_ne hN (Ne.symm hN₁)
  have hNpos : 0 < N := lt_trans zero_lt_one hNgt
  have hpow : (N ^ (100 / 1149 : ℝ)) ^ n.primeFactors.card ≤ N :=
    (chen_pow_primeFactors_card_le hn (Real.rpow_nonneg hNpos.le _) hrough).trans hnN
  by_contra hk
  have hk₁₂ : 12 ≤ n.primeFactors.card := by omega
  have hk₁₂R : (12 : ℝ) ≤ (n.primeFactors.card : ℝ) := by exact_mod_cast hk₁₂
  have hexp : (1 : ℝ) < (100 / 1149 : ℝ) * (n.primeFactors.card : ℝ) := by
    nlinarith
  have hstrict : N < (N ^ (100 / 1149 : ℝ)) ^ n.primeFactors.card := by
    calc
      N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ < N ^ ((100 / 1149 : ℝ) * (n.primeFactors.card : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt hNgt hexp
      _ = (N ^ (100 / 1149 : ℝ)) ^ n.primeFactors.card :=
        Real.rpow_mul_natCast hNpos.le _ _
  exact (not_lt_of_ge hpow) hstrict

/-- A carrier-only upper bound for the literal weight. Its negative terms
are discarded, while both positive pair counts are bounded by `11 * 11`. -/
theorem chenElevenWeight_le_246_of_card_le_eleven {n : ℕ} {N A H D C : ℝ}
    (hk : n.primeFactors.card ≤ 11) :
    chenElevenWeight n N A H D C ≤ 246 := by
  classical
  have h₁ : chenY1 n A ≤ 1 := by
    unfold chenY1
    split_ifs <;> omega
  have h₂ : chenY2 n H ≤ 1 := by
    unfold chenY2
    split_ifs <;> omega
  have hpair : (chenInitialPairCarrier n).card ≤ 121 := by
    rw [chenInitialPairCarrier, Finset.card_product]
    calc
      n.primeFactors.card * n.primeFactors.card ≤ 11 * 11 := Nat.mul_le_mul hk hk
      _ = 121 := by norm_num
  have h₅ : chenY5 n A H ≤ 121 := by
    unfold chenY5 chenY5Tuples
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans hpair
  have h₆ : chenY6 n A H D ≤ 121 := by
    unfold chenY6 chenY6Tuples
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans hpair
  have h₁R : (chenY1 n A : ℝ) ≤ 1 := by exact_mod_cast h₁
  have h₂R : (chenY2 n H : ℝ) ≤ 1 := by exact_mod_cast h₂
  have h₅R : (chenY5 n A H : ℝ) ≤ 121 := by exact_mod_cast h₅
  have h₆R : (chenY6 n A H D : ℝ) ≤ 121 := by exact_mod_cast h₆
  have h₃ := Nat.cast_nonneg (α := ℝ) (chenY3 n A C)
  have h₄ := Nat.cast_nonneg (α := ℝ) (chenY4 n A D)
  have h₇ := Nat.cast_nonneg (α := ℝ) (chenY7 n N D)
  have h₈ := Nat.cast_nonneg (α := ℝ) (chenY8 n N A C)
  have h₉ := Nat.cast_nonneg (α := ℝ) (chenY9 n N H D)
  have h₁₀ := Nat.cast_nonneg (α := ℝ) (chenY10 n A H)
  have h₁₁ := Nat.cast_nonneg (α := ℝ) (chenY11Full n A H D)
  unfold chenElevenWeight
  linarith

/-- A uniform bound for the actual fixed eleven-term Chen weight, with no
squarefree hypothesis and no lower size-band hypothesis. -/
theorem chenFixedElevenWeight_le_246 {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) (hn : n ≠ 0) (hnN : (n : ℝ) ≤ N) :
    chenFixedElevenWeight n N ≤ 246 := by
  classical
  have hAH : N ^ (100 / 1149 : ℝ) ≤ N ^ (50 / 309 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  unfold chenFixedElevenWeight
  by_cases hrough : ChenPrimeRough (N ^ (100 / 1149 : ℝ)) n
  · exact chenElevenWeight_le_246_of_card_le_eleven
      (chen_primeFactors_card_le_eleven_of_fixed_rough hN hn hnN hrough)
  · exact (chenElevenWeight_nonpos_of_not_rough hn hAH hrough).trans (by norm_num)

end

end ImbalancedChen
