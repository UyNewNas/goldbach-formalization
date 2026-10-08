import ImbalancedChen.QuotientChenNinthSwitch
import ImbalancedChen.Multiplicity
import Mathlib.Data.Nat.Choose.Basic

/-!
# The actual repaired eleven-term Chen pointwise weight

Every term in this file is the cardinality of its literal quotient support.
The smallest pair used in the four-prime identities is constructed from the
actual number of factors below `H`; it is never assumed as a desired tuple.
Subtraction in the weight is real subtraction. Natural subtraction occurs
only inside proved cardinality identities, with its order hypotheses made
explicit before casting.

The final theorem uses the manuscript's exact fixed powers and its original
squarefree size band. Receiver one is evaluated separately, and the right
side counts prime factors with multiplicity, including the unit receiver.
-/

namespace ImbalancedChen

open scoped ArithmeticFunction.Omega

noncomputable section

/-- The literal eleven-term weight, with the full fourth-prime endpoint `D`.
All negative signs are in `ℝ`, not truncated natural subtraction. -/
def chenElevenWeight (n : ℕ) (N A H D C : ℝ) : ℝ :=
  3 * (chenY1 n A : ℝ) + (chenY2 n H : ℝ) - (chenY3 n A C : ℝ) -
    (chenY4 n A D : ℝ) + (chenY5 n A H : ℝ) + (chenY6 n A H D : ℝ) -
    2 * (chenY7 n N D : ℝ) - (chenY8 n N A C : ℝ) -
    (chenY9 n N H D : ℝ) - (chenY10 n A H : ℝ) - (chenY11Full n A H D : ℝ)

/-- The exact exponents of the repaired source weight. -/
def chenFixedElevenWeight (n : ℕ) (N : ℝ) : ℝ :=
  chenElevenWeight n N (N ^ (100 / 1149 : ℝ)) (N ^ (50 / 309 : ℝ))
    (N ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))) (N ^ (1 / 3 : ℝ))

/-- A literal positive pair summand forces roughness of the whole receiver. -/
theorem chenPrimeRough_of_initial_quotient_pair {n p₁ p₂ : ℕ} {A : ℝ}
    (h₁ : Nat.Prime p₁) (h₂ : Nat.Prime p₂)
    (hA₁ : A ≤ (p₁ : ℝ)) (hA₂ : A ≤ (p₂ : ℝ))
    (hQ : ChenQuotient (p₁ * p₂) A n) : ChenPrimeRough A n := by
  intro q hq hqn
  have hprod : (p₁ * p₂) * (n / (p₁ * p₂)) = n := Nat.mul_div_cancel' hQ.1
  have hqd : q ∣ (p₁ * p₂) * (n / (p₁ * p₂)) := by rwa [hprod]
  rcases hq.dvd_mul.mp hqd with hpref | hquot
  · rcases hq.dvd_mul.mp hpref with hd₁ | hd₂
    · have heq := (Nat.prime_dvd_prime_iff_eq hq h₁).mp hd₁
      simpa only [heq] using hA₁
    · have heq := (Nat.prime_dvd_prime_iff_eq hq h₂).mp hd₂
      simpa only [heq] using hA₂
  · exact hQ.2 q hq hquot

/-- Only the positive supports need to vanish on the nonrough branch.
No assertion about the ninth switching cutoff is needed for this bound. -/
theorem chenElevenWeight_nonpos_of_not_rough {n : ℕ} {N A H D C : ℝ}
    (hn : n ≠ 0) (hAH : A ≤ H) (hnot : ¬ ChenPrimeRough A n) :
    chenElevenWeight n N A H D C ≤ 0 := by
  classical
  have h₁ : chenY1 n A = 0 := by simp [chenY1, hnot]
  have hnotH : ¬ ChenPrimeRough H n := by
    intro hrough
    exact hnot (fun q hq hd => hAH.trans (hrough q hq hd))
  have h₂ : chenY2 n H = 0 := by simp [chenY2, hnotH]
  have h₅ : chenY5 n A H = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨p₁, p₂⟩ hp
    obtain ⟨hp₁, hp₂, hA₁, h₁₂, _, hQ⟩ := (mem_chenY5Tuples_iff hn).mp hp
    have hA₂ : A ≤ (p₂ : ℝ) := hA₁.trans (by exact_mod_cast h₁₂.le)
    exact hnot (chenPrimeRough_of_initial_quotient_pair hp₁ hp₂ hA₁ hA₂ hQ)
  have h₆ : chenY6 n A H D = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨p₁, p₂⟩ hp
    obtain ⟨hp₁, hp₂, hA₁, _, hH₂, _, hQ⟩ := (mem_chenY6Tuples_iff hn).mp hp
    exact hnot (chenPrimeRough_of_initial_quotient_pair hp₁ hp₂ hA₁ (hAH.trans hH₂) hQ)
  unfold chenElevenWeight
  rw [h₁, h₂, h₅, h₆]
  have h₃ := Nat.cast_nonneg (α := ℝ) (chenY3 n A C)
  have h₄ := Nat.cast_nonneg (α := ℝ) (chenY4 n A D)
  have h₇ := Nat.cast_nonneg (α := ℝ) (chenY7 n N D)
  have h₈ := Nat.cast_nonneg (α := ℝ) (chenY8 n N A C)
  have h₉ := Nat.cast_nonneg (α := ℝ) (chenY9 n N H D)
  have h₁₀ := Nat.cast_nonneg (α := ℝ) (chenY10 n A H)
  have h₁₁ := Nat.cast_nonneg (α := ℝ) (chenY11Full n A H D)
  norm_num only [Nat.cast_zero]
  linarith

/-- A genuine count of at least two primes below `H` supplies the smallest
pair and puts its second member below `H`. -/
theorem chen_exists_smallestTwo_below {n : ℕ} {H : ℝ} (hn : n ≠ 0)
    (hr : 2 ≤ (chenPrimesBelow n H).card) :
    ∃ q₁ q₂ : ℕ, ChenSmallestTwo n q₁ q₂ ∧ (q₂ : ℝ) < H := by
  classical
  have hle : (chenPrimesBelow n H).card ≤ n.primeFactors.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨q₁, q₂, hsmall⟩ := chen_exists_smallestTwo (hr.trans hle)
  refine ⟨q₁, q₂, hsmall, ?_⟩
  by_contra hnot
  have hH₂ : H ≤ (q₂ : ℝ) := le_of_not_gt hnot
  have hsub : chenPrimesBelow n H ⊆ {q₁} := by
    intro p hp
    obtain ⟨hprime, hdvd, hpH⟩ := (mem_chenPrimesBelow hn).mp hp
    rcases hsmall.least_other p hprime hdvd with heq | hle
    · simpa only [Finset.mem_singleton] using heq
    · have hleR : (q₂ : ℝ) ≤ (p : ℝ) := by exact_mod_cast hle
      exact ((not_lt_of_ge (hH₂.trans hleR)) hpH).elim
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hcard
  omega

/-- The exact two-step binomial difference, before any casts or subtraction. -/
theorem chen_choose_two_step (m : ℕ) :
    (m + 2).choose 2 = m.choose 2 + 2 * m + 1 := by
  have h₁ := Nat.choose_succ_succ m 1
  have h₂ := Nat.choose_succ_succ (m + 1) 1
  simp only [Nat.choose_one_right] at h₁ h₂
  omega

/-- The large-low-count branch follows from the actual first-six and
four-prime source identities. The remaining actual switches are nonnegative. -/
theorem chenElevenWeight_nonpos_of_two_le_below {n : ℕ} {N A H D C : ℝ}
    (hn : Squarefree n) (hrough : ChenPrimeRough A n)
    (hHD : H ≤ D) (hDC : D ≤ C) (hr : 2 ≤ (chenPrimesBelow n H).card) :
    chenElevenWeight n N A H D C ≤ 0 := by
  classical
  obtain ⟨q₁, q₂, hsmall, hq₂H⟩ := chen_exists_smallestTwo_below hn.ne_zero hr
  have hA := hrough q₁ hsmall.first_prime hsmall.first_dvd
  let r := (chenPrimesBelow n H).card
  let s := (chenPrimesBelow n D).card
  let t := (chenPrimesBelow n C).card
  have hrs : r ≤ s := chenPrimesBelow_card_mono hHD
  have hst : s ≤ t := chenPrimesBelow_card_mono hDC
  have hr₂ : 2 ≤ r := hr
  have hr₀ : r ≠ 0 := by omega
  have hrc : r = (r - 2) + 2 := by omega
  have hchoose := chen_choose_two_step (r - 2)
  rw [← hrc] at hchoose
  have hchooseR : (r.choose 2 : ℝ) = ((r - 2).choose 2 : ℝ) +
      2 * ((r - 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hchoose
  have hrsub : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by
    rw [Nat.cast_sub hr₂]
    norm_num
  have hssub : ((s - r : ℕ) : ℝ) = (s : ℝ) - (r : ℝ) := Nat.cast_sub hrs
  have hstR : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  have h₇ := Nat.cast_nonneg (α := ℝ) (chenY7 n N D)
  have h₈ := Nat.cast_nonneg (α := ℝ) (chenY8 n N A C)
  have h₉ := Nat.cast_nonneg (α := ℝ) (chenY9 n N H D)
  unfold chenElevenWeight
  rw [chenY1_eq_one hrough, chenY2_eq_indicator hn.ne_zero,
    chenY3_eq_card hn.ne_zero hrough, chenY4_eq_card hn.ne_zero hrough,
    chenY5_eq_choose hn.ne_zero hrough, chenY6_eq_mul_sub hn.ne_zero hrough hHD,
    chenY10_eq_choose_sub_two hn hsmall hA hq₂H,
    chenY11Full_eq_sub_two_mul_sub hn hsmall hA hq₂H hHD]
  change 3 * (1 : ℝ) + ((if r = 0 then 1 else 0 : ℕ) : ℝ) - (t : ℝ) -
    (s : ℝ) + (r.choose 2 : ℝ) + ((r * (s - r) : ℕ) : ℝ) -
    2 * (chenY7 n N D : ℝ) - (chenY8 n N A C : ℝ) -
    (chenY9 n N H D : ℝ) - ((r - 2).choose 2 : ℝ) -
    (((r - 2) * (s - r) : ℕ) : ℝ) ≤ 0
  rw [if_neg hr₀]
  simp only [Nat.cast_zero, Nat.cast_mul, hrsub, hssub] at *
  nlinarith

/-- A convenient upper bound retaining exactly the three pair switches.
Its count variables are the actual prime-factor sets, not supplied scalars. -/
theorem chenElevenWeight_le_initial_switches {n : ℕ} {N A H D C : ℝ}
    (hn : n ≠ 0) (hrough : ChenPrimeRough A n) (hHD : H ≤ D) :
    let r := (chenPrimesBelow n H).card
    let s := (chenPrimesBelow n D).card
    let t := (chenPrimesBelow n C).card
    chenElevenWeight n N A H D C ≤
      3 + ((if r = 0 then 1 else 0 : ℕ) : ℝ) - (t : ℝ) - (s : ℝ) +
        (r.choose 2 : ℝ) + ((r * (s - r) : ℕ) : ℝ) -
        2 * (chenY7 n N D : ℝ) - (chenY8 n N A C : ℝ) - (chenY9 n N H D : ℝ) := by
  dsimp only
  have h₁₀ := Nat.cast_nonneg (α := ℝ) (chenY10 n A H)
  have h₁₁ := Nat.cast_nonneg (α := ℝ) (chenY11Full n A H D)
  unfold chenElevenWeight
  rw [chenY1_eq_one hrough, chenY2_eq_indicator hn,
    chenY3_eq_card hn hrough, chenY4_eq_card hn hrough,
    chenY5_eq_choose hn hrough, chenY6_eq_mul_sub hn hrough hHD]
  norm_num only [Nat.cast_one]
  linarith

/-- The actual distinct-factor count agrees with multiplicity on squarefree
receivers. This is the bridge needed for the manuscript's `Ω` convention. -/
theorem chen_primeFactors_card_eq_omega {n : ℕ} (hn : Squarefree n) :
    n.primeFactors.card = Ω n := by
  change n.primeFactors.card = n.primeFactorsList.length
  rw [← Nat.toFinset_factors]
  exact List.toFinset_card_of_nodup hn.nodup_primeFactorsList

/-- The small-multiplicity branch includes receiver one and uses only actual
count bounds. No upper cap for a two-factor switching tuple is presumed. -/
theorem chenElevenWeight_le_four_of_omega_le_two {n : ℕ} {N A H D C : ℝ}
    (hn : Squarefree n) (hAH : A ≤ H) (hHD : H ≤ D) (hDC : D ≤ C)
    (hΩ : Ω n ≤ 2) : chenElevenWeight n N A H D C ≤ 4 := by
  classical
  by_cases hrough : ChenPrimeRough A n
  · by_cases hr₂ : 2 ≤ (chenPrimesBelow n H).card
    · exact (chenElevenWeight_nonpos_of_two_le_below hn hrough hHD hDC hr₂).trans (by norm_num)
    · let r := (chenPrimesBelow n H).card
      let s := (chenPrimesBelow n D).card
      let t := (chenPrimesBelow n C).card
      have hrs : r ≤ s := chenPrimesBelow_card_mono hHD
      have hst : s ≤ t := chenPrimesBelow_card_mono hDC
      have hs₂ : s ≤ 2 := by
        have hsub : s ≤ n.primeFactors.card := Finset.card_le_card (Finset.filter_subset _ _)
        rw [chen_primeFactors_card_eq_omega hn] at hsub
        omega
      have hr01 : r = 0 ∨ r = 1 := by dsimp [r]; omega
      have hW := chenElevenWeight_le_initial_switches (N := N) (C := C) hn.ne_zero hrough hHD
      change chenElevenWeight n N A H D C ≤ 3 + ((if r = 0 then 1 else 0 : ℕ) : ℝ) -
        (t : ℝ) - (s : ℝ) + (r.choose 2 : ℝ) + ((r * (s - r) : ℕ) : ℝ) -
        2 * (chenY7 n N D : ℝ) - (chenY8 n N A C : ℝ) - (chenY9 n N H D : ℝ) at hW
      have h₇ := Nat.cast_nonneg (α := ℝ) (chenY7 n N D)
      have h₈ := Nat.cast_nonneg (α := ℝ) (chenY8 n N A C)
      have h₉ := Nat.cast_nonneg (α := ℝ) (chenY9 n N H D)
      rcases hr01 with hr | hr
      · simp [hr] at hW
        have hs := Nat.cast_nonneg (α := ℝ) s
        have ht := Nat.cast_nonneg (α := ℝ) t
        linarith
      · have hs₁ : 1 ≤ s := by omega
        have hsub : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
          rw [Nat.cast_sub hs₁]
          norm_num
        simp only [hr, Nat.one_ne_zero, if_false, Nat.choose_eq_zero_of_lt (by omega : 1 < 2),
          Nat.cast_zero, one_mul, hsub] at hW
        have ht := Nat.cast_nonneg (α := ℝ) t
        linarith
  · exact (chenElevenWeight_nonpos_of_not_rough hn.ne_zero hAH hrough).trans (by norm_num)

/-- Three actual factors cannot all be at least a nonnegative cube-root
cutoff. The strictness comes from the distinct third prime. -/
theorem chenPrimesBelow_card_pos_of_three {n : ℕ} {N C : ℝ}
    (hn : n ≠ 0) (hnN : (n : ℝ) ≤ N) (hC : 0 ≤ C)
    (hcube : N ≤ C ^ 3) (hk : 3 ≤ n.primeFactors.card) :
    1 ≤ (chenPrimesBelow n C).card := by
  obtain ⟨p₁, p₂, hsmall⟩ := chen_exists_smallestTwo (by omega : 2 ≤ n.primeFactors.card)
  obtain ⟨p₃, h₃, hd₃, h₂₃⟩ := hsmall.exists_third hk
  by_contra hnot
  have htzero : (chenPrimesBelow n C).card = 0 := by omega
  have hC₁ := (hsmall.below_card_eq_zero_iff hn).mp htzero
  have hC₂ : C ≤ (p₂ : ℝ) := hC₁.trans (by exact_mod_cast hsmall.increasing.le)
  have hd := chen_switch_triple_product_dvd hsmall.first_prime hsmall.second_prime h₃
    hsmall.increasing h₂₃ hsmall.first_dvd hsmall.second_dvd hd₃
  have hprod : (p₁ : ℝ) * (p₂ : ℝ) * (p₃ : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have h₁₂ : C * C ≤ (p₁ : ℝ) * (p₂ : ℝ) :=
    mul_le_mul hC₁ hC₂ hC (Nat.cast_nonneg _)
  have hlow := mul_le_mul h₁₂ hC₂ hC
    (mul_nonneg (Nat.cast_nonneg p₁) (Nat.cast_nonneg p₂))
  have hp₁ : 0 < (p₁ : ℝ) := by exact_mod_cast hsmall.first_prime.pos
  have hp₂ : 0 < (p₂ : ℝ) := by exact_mod_cast hsmall.second_prime.pos
  have h₂₃R : (p₂ : ℝ) < (p₃ : ℝ) := by exact_mod_cast h₂₃
  have hstrict := mul_lt_mul_of_pos_left h₂₃R (mul_pos hp₁ hp₂)
  nlinarith only [hlow, hstrict, hprod, hnN, hcube]

/-- The remaining two-minus-count expression is always nonpositive. -/
theorem chen_two_sub_count_sub_indicator_nonpos (t : ℕ) (ht : 1 ≤ t) :
    (2 : ℝ) - (t : ℝ) - ((if t = 1 then 1 else 0 : ℕ) : ℝ) ≤ 0 := by
  by_cases ht₁ : t = 1
  · simp [ht₁]
  · have ht₂ : 2 ≤ t := by omega
    have ht₂R : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht₂
    simp only [if_neg ht₁, Nat.cast_zero, sub_zero]
    linarith

/-- All high-multiplicity branches for actual quotient tuples. The geometric
hypotheses are numeric cutoff bounds, not assumed tuple-count identities. -/
theorem chenElevenWeight_nonpos_of_three_factors {n : ℕ} {N A H D C : ℝ}
    (hn : Squarefree n) (hrough : ChenPrimeRough A n) (hN : 0 ≤ N)
    (hnN : (n : ℝ) ≤ N) (hlower : N ≤ (n : ℝ) * A)
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
  have hW := chenElevenWeight_le_initial_switches (N := N) (C := C) hn.ne_zero hrough hHD
  change chenElevenWeight n N A H D C ≤ 3 + ((if r = 0 then 1 else 0 : ℕ) : ℝ) -
    (t : ℝ) - (s : ℝ) + (r.choose 2 : ℝ) + ((r * (s - r) : ℕ) : ℝ) -
    2 * (chenY7 n N D : ℝ) - (chenY8 n N A C : ℝ) - (chenY9 n N H D : ℝ) at hW
  have hr01 : r = 0 ∨ r = 1 := by dsimp [r]; omega
  rcases hr01 with hr | hr
  · simp only [hr, if_pos rfl, Nat.choose_zero_succ, Nat.zero_mul,
      Nat.cast_one, Nat.cast_zero, add_zero] at hW
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
            chenY9_ge_one_of_ninth_branch hn hrough hN hnN hlower hH hD hC hlarge
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

/-- The unit receiver contributes exactly four, for arbitrary cutoffs.
All actual prime tuple carriers are empty, while both `Q_1` indicators are one. -/
@[simp] theorem chenElevenWeight_one (N A H D C : ℝ) :
    chenElevenWeight 1 N A H D C = 4 := by
  classical
  simp [chenElevenWeight, chenY1, chenY2, chenY3, chenY4, chenY5, chenY6,
    chenY7, chenY8, chenY9, chenY10, chenY11Full,
    chenSinglePrimeTuples, chenY5Tuples, chenY6Tuples, chenInitialPairCarrier,
    chenY7Tuples, chenY8Tuples, chenY9Tuples,
    chenY10Tuples, chenY11FullTuples, chenFourPrimeCarrier]

/-- The repaired eleven-term pointwise inequality on the exact source band.
The right side is `4 * 1_{Ω(n) ≤ 2}`. No desired count identity, selected
factorization, or scalar envelope is assumed. Coprimality with `N` is not
needed for this pointwise assertion. The `N = 1`, `n = 1` case is retained. -/
theorem chenFixedElevenWeight_le_four_indicator {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) (hn : Squarefree n) (hnN : (n : ℝ) ≤ N)
    (hband : N ^ (1 - (100 / 1149 : ℝ)) ≤ (n : ℝ)) :
    chenFixedElevenWeight n N ≤ if Ω n ≤ 2 then 4 else 0 := by
  classical
  by_cases hN₁ : N = 1
  · subst N
    have hnle : n ≤ 1 := by exact_mod_cast hnN
    have hnzero := hn.ne_zero
    have hn₁ : n = 1 := by omega
    subst n
    simp [chenFixedElevenWeight]
  have hNgt : 1 < N := lt_of_le_of_ne hN (Ne.symm hN₁)
  have hNpos : 0 < N := lt_trans zero_lt_one hNgt
  have hAH : N ^ (100 / 1149 : ℝ) ≤ N ^ (50 / 309 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have hHD : N ^ (50 / 309 : ℝ) ≤ N ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have hDC : N ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)) ≤ N ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  unfold chenFixedElevenWeight
  by_cases hΩ : Ω n ≤ 2
  · rw [if_pos hΩ]
    exact chenElevenWeight_le_four_of_omega_le_two hn hAH hHD hDC hΩ
  · rw [if_neg hΩ]
    by_cases hrough : ChenPrimeRough (N ^ (100 / 1149 : ℝ)) n
    · have hk : 3 ≤ n.primeFactors.card := by
        rw [chen_primeFactors_card_eq_omega hn]
        omega
      have hcube : (N ^ (1 / 3 : ℝ)) ^ 3 = N := by
        rw [← Real.rpow_mul_natCast hNpos.le (1 / 3 : ℝ) 3]
        norm_num
      exact chenElevenWeight_nonpos_of_three_factors hn hrough hNpos.le hnN
        (chen_ninth_lower_product hNpos hband)
        (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)
        (Real.rpow_nonneg hNpos.le _) hHD hDC hcube.ge
        (chen_ninth_fixed_cutoffs_product_gt hNgt) hk
    · exact chenElevenWeight_nonpos_of_not_rough hn.ne_zero hAH hrough

end

end ImbalancedChen
