import ImbalancedChen.QuotientChenWeightCases

/-!
# The current manuscript's full Chen pointwise weight

This module uses the current exponents `417/5000`, `19/125`, and `59/250`,
and keeps the full fourth-prime range in `Y11`. In the ninth-switch branch,
the actual factor cutoffs imply the necessary quotient bound directly.
Consequently no lower size band for the receiver is needed.

These are literal finite quotient-count results. They do not assume a mean
value, a distribution estimate, a sieve constant, or a numerical certificate.
The paired deletion and analytic lower mean are separate obligations.
-/

namespace ImbalancedChen

open scoped ArithmeticFunction.Omega

noncomputable section

/-- In the ninth branch, the actual factor cutoffs already give `N < n*p₃`.
The old receiver-band hypothesis and its auxiliary roughness hypothesis are
unnecessary here. All three factors are constructed from the actual receiver. -/
theorem chenY9_ge_one_of_ninth_branch_without_band
    {n : ℕ} {N H D C : ℝ}
    (hn : Squarefree n) (hN : 0 ≤ N) (hnN : (n : ℝ) ≤ N)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hlarge : N < H * D * C ^ 2)
    (hr : (chenPrimesBelow n H).card = 0)
    (hs : (chenPrimesBelow n D).card = 1)
    (ht : (chenPrimesBelow n C).card ≤ 2)
    (hk : 3 ≤ n.primeFactors.card) :
    1 ≤ chenY9 n N H D := by
  have hcard := chen_primeFactors_card_eq_three_of_ninth_branch hn.ne_zero hnN
    hH hD hC hlarge hr hs ht hk
  obtain ⟨p₁, p₂, hsmall⟩ := chen_exists_smallestTwo
    (by omega : 2 ≤ n.primeFactors.card)
  obtain ⟨p₃, h₃, hd₃, h₂₃⟩ := hsmall.exists_third hk
  have heq := chen_eq_three_prime_product_of_card hn hcard hsmall h₃ hd₃ h₂₃
  have hH₁ := (hsmall.below_card_eq_zero_iff hn.ne_zero).mp hr
  obtain ⟨hD₁, hD₂⟩ := (hsmall.below_card_eq_one_iff hn.ne_zero).mp hs
  have hC₃ := hsmall.le_third_of_below_card_le_two hn.ne_zero ht h₃ hd₃ h₂₃
  have h₁₂ : H * D ≤ (p₁ : ℝ) * (p₂ : ℝ) :=
    mul_le_mul hH₁ hD₂ hD (Nat.cast_nonneg _)
  have h₃sq : C ^ 2 ≤ (p₃ : ℝ) ^ 2 := pow_le_pow_left₀ hC hC₃ 2
  have hprod := mul_le_mul h₁₂ h₃sq (sq_nonneg C)
    (mul_nonneg (Nat.cast_nonneg p₁) (Nat.cast_nonneg p₂))
  have heqR : (n : ℝ) = (p₁ : ℝ) * (p₂ : ℝ) * (p₃ : ℝ) := by
    exact_mod_cast heq
  have hlower₃ : N ≤ (n : ℝ) * (p₃ : ℝ) := by
    rw [heqR]
    nlinarith only [hlarge, hprod]
  exact chenY9_ge_one_of_three_primes hsmall.first_prime hsmall.second_prime h₃
    hsmall.increasing h₂₃ heq hN hnN hlower₃ hH₁ hD₁ hD₂

/-- The high-multiplicity full-weight bound needs only the upper receiver
bound and the cutoff geometry, with no artificial lower receiver band. -/
theorem chenElevenWeight_nonpos_of_three_factors_without_band
    {n : ℕ} {N A H D C : ℝ}
    (hn : Squarefree n) (hrough : ChenPrimeRough A n) (hN : 0 ≤ N)
    (hnN : (n : ℝ) ≤ N)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hHD : H ≤ D) (hDC : D ≤ C) (hcube : N ≤ C ^ 3)
    (hlarge : N < H * D * C ^ 2) (hk : 3 ≤ n.primeFactors.card) :
    chenElevenWeight n N A H D C ≤ 0 := by
  classical
  by_cases hr₂ : 2 ≤ (chenPrimesBelow n H).card
  · exact chenElevenWeight_nonpos_of_two_le_below hn hrough hHD hDC hr₂
  let r := (chenPrimesBelow n H).card
  let s := (chenPrimesBelow n D).card
  let t := (chenPrimesBelow n C).card
  have hrs : r ≤ s := chenPrimesBelow_card_mono hHD
  have hst : s ≤ t := chenPrimesBelow_card_mono hDC
  have ht : 1 ≤ t := chenPrimesBelow_card_pos_of_three hn.ne_zero hnN hC hcube hk
  have h₇id := chenY7_eq_indicator_zero (D := D) hn hk hnN
  have h₈id := chenY8_eq_indicator_one (C := C) hn hrough hk hnN
  change chenY7 n N D = if s = 0 then 1 else 0 at h₇id
  change chenY8 n N A C = if t = 1 then 1 else 0 at h₈id
  have hbalance : (2 : ℝ) - (t : ℝ) - (chenY8 n N A C : ℝ) ≤ 0 := by
    rw [h₈id]
    exact chen_two_sub_count_sub_indicator_nonpos t ht
  have h₇ := Nat.cast_nonneg (α := ℝ) (chenY7 n N D)
  have h₈ := Nat.cast_nonneg (α := ℝ) (chenY8 n N A C)
  have h₉ := Nat.cast_nonneg (α := ℝ) (chenY9 n N H D)
  have hW := chenElevenWeight_le_initial_switches (N := N) (C := C)
    hn.ne_zero hrough hHD
  change chenElevenWeight n N A H D C ≤
    3 + ((if r = 0 then 1 else 0 : ℕ) : ℝ) - (t : ℝ) - (s : ℝ) +
      (r.choose 2 : ℝ) + ((r * (s - r) : ℕ) : ℝ) -
      2 * (chenY7 n N D : ℝ) - (chenY8 n N A C : ℝ) -
      (chenY9 n N H D : ℝ) at hW
  have hr01 : r = 0 ∨ r = 1 := by dsimp [r]; omega
  rcases hr01 with hr | hr
  · simp [hr] at hW
    by_cases hs₀ : s = 0
    · have h₇one : chenY7 n N D = 1 := by simpa [hs₀] using h₇id
      rw [hs₀, h₇one] at hW
      norm_num only [Nat.cast_zero, Nat.cast_one] at hW
      linarith
    · by_cases hs₁ : s = 1
      · rw [hs₁] at hW
        norm_num only [Nat.cast_one] at hW
        by_cases ht₂ : t ≤ 2
        · have h₉one : 1 ≤ chenY9 n N H D :=
            chenY9_ge_one_of_ninth_branch_without_band hn hN hnN hH hD hC hlarge
              hr hs₁ ht₂ hk
          have h₉oneR : (1 : ℝ) ≤ (chenY9 n N H D : ℝ) := by exact_mod_cast h₉one
          linarith
        · have ht₃ : 3 ≤ t := by omega
          have ht₃R : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht₃
          linarith
      · have hs₂ : 2 ≤ s := by omega
        have hs₂R : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs₂
        have hstR : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
        linarith
  · have hs₁ : 1 ≤ s := by omega
    have hsub : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub hs₁]
      norm_num
    simp only [hr, Nat.one_ne_zero, if_false, Nat.choose_eq_zero_of_lt (by omega : 1 < 2),
      Nat.cast_zero, one_mul, hsub] at hW
    linarith

/-- The full eleven-term weight at the actual current manuscript parameters.
The inherited generic definition uses the full `chenY11Full` endpoint. -/
def currentChenElevenWeight (n : ℕ) (N : ℝ) : ℝ :=
  chenElevenWeight n N (N ^ (417 / 5000 : ℝ)) (N ^ (19 / 125 : ℝ))
    (N ^ (59 / 250 : ℝ)) (N ^ (1 / 3 : ℝ))

/-- The strict geometric margin at the current exponents. -/
theorem currentChen_cutoffs_product_gt {N : ℝ} (hN : 1 < N) :
    N < N ^ (19 / 125 : ℝ) * N ^ (59 / 250 : ℝ) *
      (N ^ (1 / 3 : ℝ)) ^ 2 := by
  have hNpos : 0 < N := lt_trans zero_lt_one hN
  rw [← Real.rpow_mul_natCast hNpos.le (1 / 3 : ℝ) 2,
    ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
  have he : (1 : ℝ) < (19 / 125 : ℝ) + (59 / 250 : ℝ) +
      (1 / 3 : ℝ) * 2 := by norm_num
  simpa only [Real.rpow_one, Nat.cast_ofNat] using
    Real.rpow_lt_rpow_of_exponent_lt hN he

/-- The current manuscript's pointwise full-weight inequality. Only
squarefreeness and `n ≤ N` are required of the receiver; there is no
asymptotic, roughness, distribution, or lower-size-band assumption.
The unit receiver and the endpoint `N = 1` are included. -/
theorem currentChenElevenWeight_le_four_indicator {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) (hn : Squarefree n) (hnN : (n : ℝ) ≤ N) :
    currentChenElevenWeight n N ≤ if Ω n ≤ 2 then 4 else 0 := by
  classical
  by_cases hN₁ : N = 1
  · subst N
    have hnle : n ≤ 1 := by exact_mod_cast hnN
    have hnzero := hn.ne_zero
    have hn₁ : n = 1 := by omega
    subst n
    simp [currentChenElevenWeight]
  have hNgt : 1 < N := lt_of_le_of_ne hN (Ne.symm hN₁)
  have hNpos : 0 < N := lt_trans zero_lt_one hNgt
  have hAH : N ^ (417 / 5000 : ℝ) ≤ N ^ (19 / 125 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have hHD : N ^ (19 / 125 : ℝ) ≤ N ^ (59 / 250 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have hDC : N ^ (59 / 250 : ℝ) ≤ N ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  unfold currentChenElevenWeight
  by_cases hΩ : Ω n ≤ 2
  · rw [if_pos hΩ]
    exact chenElevenWeight_le_four_of_omega_le_two hn hAH hHD hDC hΩ
  · rw [if_neg hΩ]
    by_cases hrough : ChenPrimeRough (N ^ (417 / 5000 : ℝ)) n
    · have hk : 3 ≤ n.primeFactors.card := by
        rw [chen_primeFactors_card_eq_omega hn]
        omega
      have hcube : (N ^ (1 / 3 : ℝ)) ^ 3 = N := by
        rw [← Real.rpow_mul_natCast hNpos.le (1 / 3 : ℝ) 3]
        norm_num
      exact chenElevenWeight_nonpos_of_three_factors_without_band
        hn hrough hNpos.le hnN
        (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)
        (Real.rpow_nonneg hNpos.le _) hHD hDC hcube.ge
        (currentChen_cutoffs_product_gt hNgt) hk
    · exact chenElevenWeight_nonpos_of_not_rough hn.ne_zero hAH hrough

end

end ImbalancedChen
