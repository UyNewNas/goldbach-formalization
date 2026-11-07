import ImbalancedChen.CurrentChenPairedDeletion
import ImbalancedChen.QuotientChenSummedBridge
import ImbalancedChen.PowerErrorBudget

/-!
# The current paired Chen weight on the actual additive-prime carrier

This module uses the current cutoff `a = 417/5000`. Only nonsquarefree
rough receivers are exceptional; there is no lower receiver-size band.
The bound needed to discard them is one-sided. The selected eleventh term
is absorbed by the full negative eleventh term, so the two positive pair
carriers give the uniform bound 246 even without squarefreeness.

The final finite inequality counts additive primes, removes receiver one,
and retains the explicit error `246 N / (N^a - 1) + 4`. No assertion about
the mean value of the weight is a hypothesis or a conclusion here.
-/

namespace ImbalancedChen

open scoped BigOperators ArithmeticFunction.Omega
open Filter

noncomputable section

theorem chen_primeFactors_card_le_eleven_of_current_rough {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) (hn : n ≠ 0) (hnN : (n : ℝ) ≤ N)
    (hrough : ChenPrimeRough (N ^ (417 / 5000 : ℝ)) n) :
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
  have hpow : (N ^ (417 / 5000 : ℝ)) ^ n.primeFactors.card ≤ N :=
    (chen_pow_primeFactors_card_le hn (Real.rpow_nonneg hNpos.le _) hrough).trans hnN
  by_contra hk
  have hk₁₂ : 12 ≤ n.primeFactors.card := by omega
  have hk₁₂R : (12 : ℝ) ≤ (n.primeFactors.card : ℝ) := by exact_mod_cast hk₁₂
  have hexp : (1 : ℝ) < (417 / 5000 : ℝ) * (n.primeFactors.card : ℝ) := by
    nlinarith
  have hstrict : N < (N ^ (417 / 5000 : ℝ)) ^ n.primeFactors.card := by
    calc
      N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ < N ^ ((417 / 5000 : ℝ) * (n.primeFactors.card : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt hNgt hexp
      _ = (N ^ (417 / 5000 : ℝ)) ^ n.primeFactors.card :=
        Real.rpow_mul_natCast hNpos.le _ _
  exact (not_lt_of_ge hpow) hstrict

/-- The selected eleventh term never exceeds the full subtracted term. -/
theorem chenPairedElevenWeight_le_positive_terms (n : ℕ) (N A H D C : ℝ)
    (E : ℕ × ℕ → Prop) :
    chenPairedElevenWeight n N A H D C E ≤
      3 * (chenY1 n A : ℝ) + (chenY2 n H : ℝ) +
        (chenY5 n A H : ℝ) + (chenY6 n A H D : ℝ) := by
  have hsel : (chenY11Selected n A H D E : ℝ) ≤ (chenY11Full n A H D : ℝ) := by
    exact_mod_cast chenY11Selected_le_full n A H D E
  have h₃ := Nat.cast_nonneg (α := ℝ) (chenY3 n A C)
  have h₄ := Nat.cast_nonneg (α := ℝ) (chenY4 n A D)
  have h₇ := Nat.cast_nonneg (α := ℝ) (chenY7 n N D)
  have h₈ := Nat.cast_nonneg (α := ℝ) (chenY8 n N A C)
  have h₉ := Nat.cast_nonneg (α := ℝ) (chenY9 n N H D)
  have h₁₀ := Nat.cast_nonneg (α := ℝ) (chenY10 n A H)
  have h₆E := Nat.cast_nonneg (α := ℝ) (chenY6Selected n A H D E)
  unfold chenPairedElevenWeight chenElevenWeight
  linarith

theorem chenPairedElevenWeight_le_246_of_card_le_eleven
    {n : ℕ} {N A H D C : ℝ} (E : ℕ × ℕ → Prop)
    (hk : n.primeFactors.card ≤ 11) :
    chenPairedElevenWeight n N A H D C E ≤ 246 := by
  classical
  have h₁ : chenY1 n A ≤ 1 := by unfold chenY1; split_ifs <;> omega
  have h₂ : chenY2 n H ≤ 1 := by unfold chenY2; split_ifs <;> omega
  have hpair : (chenInitialPairCarrier n).card ≤ 121 := by
    rw [chenInitialPairCarrier, Finset.card_product]
    exact (Nat.mul_le_mul hk hk).trans (by norm_num)
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
  have h := chenPairedElevenWeight_le_positive_terms n N A H D C E
  linarith

/-- Nonrough receivers have nonpositive paired weight, even if squareful. -/
theorem chenPairedElevenWeight_nonpos_of_not_rough
    {n : ℕ} {N A H D C : ℝ} (E : ℕ × ℕ → Prop)
    (hn : n ≠ 0) (hAH : A ≤ H) (hnot : ¬ ChenPrimeRough A n) :
    chenPairedElevenWeight n N A H D C E ≤ 0 := by
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
  simpa only [h₁, h₂, h₅, h₆, Nat.cast_zero, mul_zero, add_zero] using
    chenPairedElevenWeight_le_positive_terms n N A H D C E

theorem currentChenPairedWeight_le_246 {n : ℕ} {N : ℝ} (E : ℕ × ℕ → Prop)
    (hN : 1 ≤ N) (hn : n ≠ 0) (hnN : (n : ℝ) ≤ N) :
    currentChenPairedWeight n N E ≤ 246 := by
  unfold currentChenPairedWeight
  by_cases hrough : ChenPrimeRough (N ^ (417 / 5000 : ℝ)) n
  · exact chenPairedElevenWeight_le_246_of_card_le_eleven E
      (chen_primeFactors_card_le_eleven_of_current_rough hN hn hnN hrough)
  · exact (chenPairedElevenWeight_nonpos_of_not_rough E hn
      (Real.rpow_le_rpow_of_exponent_le hN (by norm_num)) hrough).trans (by norm_num)

/-- The actual exceptional additive primes. There is no small-size exception. -/
def currentChenSquarefulPrimes (N : ℕ) : Finset ℕ := by
  classical
  exact (chenAdditivePrimeCarrier N).filter fun P =>
    ChenPrimeRough ((N : ℝ) ^ (417 / 5000 : ℝ)) (N - P) ∧ ¬ Squarefree (N - P)

@[simp] theorem mem_currentChenSquarefulPrimes {N P : ℕ} :
    P ∈ currentChenSquarefulPrimes N ↔ P ∈ chenAdditivePrimeCarrier N ∧
      ChenPrimeRough ((N : ℝ) ^ (417 / 5000 : ℝ)) (N - P) ∧ ¬ Squarefree (N - P) := by
  classical
  simp only [currentChenSquarefulPrimes, Finset.mem_filter]

theorem currentChenSquarefulPrimes_card_le (N : ℕ) :
    (currentChenSquarefulPrimes N).card ≤
      (roughSquareExceptions N ((N : ℝ) ^ (417 / 5000 : ℝ))).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun P : ℕ => N - P)
  · intro P hP
    obtain ⟨hPc, hrough, hnsf⟩ := mem_currentChenSquarefulPrimes.mp hP
    have hPN := (mem_chenAdditivePrimeCarrier.mp hPc).1
    exact chen_mem_roughSquareExceptions_of_not_squarefree
      (by omega : 0 < N - P) (Nat.sub_le N P) hrough hnsf
  · intro P hP Q hQ hPQ
    have hPN := (mem_chenAdditivePrimeCarrier.mp
      (mem_currentChenSquarefulPrimes.mp hP).1).1
    have hQN := (mem_chenAdditivePrimeCarrier.mp
      (mem_currentChenSquarefulPrimes.mp hQ).1).1
    change N - P = N - Q at hPQ
    omega

theorem currentChenSquarefulPrimes_card_cast_le (N : ℕ)
    (hA : 1 < (N : ℝ) ^ (417 / 5000 : ℝ)) :
    ((currentChenSquarefulPrimes N).card : ℝ) ≤
      (N : ℝ) / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1) := by
  have hcard : ((currentChenSquarefulPrimes N).card : ℝ) ≤
      ((roughSquareExceptions N ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ) := by
    exact_mod_cast currentChenSquarefulPrimes_card_le N
  exact hcard.trans (roughSquareExceptions_card_le N hA)

def currentChenPairedPrimeSum (N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N, currentChenPairedWeight (N - P) (N : ℝ) E

theorem currentChenPairedWeight_le_indicator_add_exception {N P : ℕ}
    (E : ℕ × ℕ → Prop) (hN : 1 ≤ (N : ℝ)) (hP : P ∈ chenAdditivePrimeCarrier N) :
    currentChenPairedWeight (N - P) (N : ℝ) E ≤
      (if Ω (N - P) ≤ 2 then (4 : ℝ) else 0) +
        (if P ∈ currentChenSquarefulPrimes N then (246 : ℝ) else 0) := by
  classical
  have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
  have hn : N - P ≠ 0 := by omega
  have hnN : ((N - P : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N P
  have hindicator : 0 ≤ (if Ω (N - P) ≤ 2 then (4 : ℝ) else 0) := by
    split_ifs <;> norm_num
  by_cases hbad : P ∈ currentChenSquarefulPrimes N
  · rw [if_pos hbad]
    have hbound := currentChenPairedWeight_le_246 E hN hn hnN
    linarith
  · rw [if_neg hbad, add_zero]
    by_cases hrough : ChenPrimeRough ((N : ℝ) ^ (417 / 5000 : ℝ)) (N - P)
    · have hsf : Squarefree (N - P) := by
        by_contra hnsf
        exact hbad (mem_currentChenSquarefulPrimes.mpr ⟨hP, hrough, hnsf⟩)
      exact currentChenPairedWeight_le_four_indicator hN hsf hnN E
    · exact (chenPairedElevenWeight_nonpos_of_not_rough E hn
        (Real.rpow_le_rpow_of_exponent_le hN (by norm_num)) hrough).trans hindicator

theorem currentChenPairedPrimeSum_le_count_add_exceptions (N : ℕ)
    (E : ℕ × ℕ → Prop) (hN : 1 ≤ (N : ℝ)) :
    currentChenPairedPrimeSum N E ≤ 4 * (D12Omega N : ℝ) +
      246 * ((currentChenSquarefulPrimes N).card : ℝ) := by
  classical
  let S := chenAdditivePrimeCarrier N
  let X := currentChenSquarefulPrimes N
  have hsub : S.filter (fun P => Ω (N - P) ≤ 2) ⊆ omegaChenPrimes N := by
    intro P hP
    obtain ⟨hPS, hΩ⟩ := Finset.mem_filter.mp hP
    obtain ⟨hPN, hp, _⟩ := mem_chenAdditivePrimeCarrier.mp hPS
    exact mem_omegaChenPrimes.mpr ⟨hPN, hp, hΩ⟩
  have hcount : (((S.filter (fun P => Ω (N - P) ≤ 2)).card) : ℝ) ≤ (D12Omega N : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hfilterX : S.filter (fun P => P ∈ X) = X := by
    ext P
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hPX
      exact ⟨(mem_currentChenSquarefulPrimes.mp hPX).1, hPX⟩
  calc
    currentChenPairedPrimeSum N E ≤ ∑ P ∈ S,
        ((if Ω (N - P) ≤ 2 then (4 : ℝ) else 0) +
          (if P ∈ X then (246 : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro P hP
      exact currentChenPairedWeight_le_indicator_add_exception E hN hP
    _ = (((S.filter (fun P => Ω (N - P) ≤ 2)).card) : ℝ) * 4 +
        (X.card : ℝ) * 246 := by
      rw [Finset.sum_add_distrib, chen_sum_indicator_card, chen_sum_indicator_card, hfilterX]
    _ ≤ 4 * (D12Omega N : ℝ) + 246 * (X.card : ℝ) := by linarith

/-- The current manuscript's finite weight-to-count bridge, with receiver one
removed and no obsolete lower size band. -/
theorem currentChenPairedPrimeSum_le_four_D12_add_error (N : ℕ)
    (E : ℕ × ℕ → Prop) (hN : 1 ≤ (N : ℝ))
    (hA : 1 < (N : ℝ) ^ (417 / 5000 : ℝ)) :
    currentChenPairedPrimeSum N E ≤ 4 * (D12 N : ℝ) +
      246 * ((N : ℝ) / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1)) + 4 := by
  have hsum := currentChenPairedPrimeSum_le_count_add_exceptions N E hN
  have herr := currentChenSquarefulPrimes_card_cast_le N hA
  have hunit : (D12Omega N : ℝ) ≤ (D12 N : ℝ) + 1 := by
    exact_mod_cast D12Omega_le_D12_add_one N
  linarith

/-- A fixed-power budget sufficient for the asymptotic passage. It uses
only a one-sided bound on the discarded weight. -/
theorem currentChenPairedPrimeSum_sub_power_error_le_four_D12 (N : ℕ)
    (E : ℕ × ℕ → Prop) (hN : 1 ≤ (N : ℝ))
    (hA : 2 ≤ (N : ℝ) ^ (417 / 5000 : ℝ)) :
    currentChenPairedPrimeSum N E -
      (492 * (N : ℝ) ^ (1 - (417 / 5000 : ℝ)) + 4) ≤ 4 * (D12 N : ℝ) := by
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN
  have hdiv : (N : ℝ) / (N : ℝ) ^ (417 / 5000 : ℝ) =
      (N : ℝ) ^ (1 - (417 / 5000 : ℝ)) := by
    rw [Real.rpow_sub hNpos, Real.rpow_one]
  have hrecip : 1 / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1) ≤
      2 / (N : ℝ) ^ (417 / 5000 : ℝ) := by
    apply (div_le_div_iff₀ (by linarith : 0 < (N : ℝ) ^ (417 / 5000 : ℝ) - 1)
      (by linarith : 0 < (N : ℝ) ^ (417 / 5000 : ℝ))).mpr
    linarith
  have herr : (N : ℝ) / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1) ≤
      2 * (N : ℝ) ^ (1 - (417 / 5000 : ℝ)) := by
    calc
      (N : ℝ) / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1) =
          (N : ℝ) * (1 / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1)) := by ring
      _ ≤ (N : ℝ) * (2 / (N : ℝ) ^ (417 / 5000 : ℝ)) :=
        mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg N)
      _ = 2 * ((N : ℝ) / (N : ℝ) ^ (417 / 5000 : ℝ)) := by ring
      _ = 2 * (N : ℝ) ^ (1 - (417 / 5000 : ℝ)) := by rw [hdiv]
  have hsum := currentChenPairedPrimeSum_le_four_D12_add_error N E hN (by linarith)
  linarith

/-- Both finite size gates eventually hold at the current exponent. -/
theorem eventually_currentChen_weight_size_conditions :
    ∀ᶠ N : ℕ in atTop, 1 ≤ (N : ℝ) ∧ 2 ≤ (N : ℝ) ^ (417 / 5000 : ℝ) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (417 / 5000 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 417 / 5000)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hpow.eventually (eventually_ge_atTop (2 : ℝ))] with N hN hA
  exact ⟨by exact_mod_cast hN, hA⟩

/-- The one-sided squareful and unit budget is negligible in the literal
singular normalization, independently of the selected pair region. -/
theorem eventually_currentChen_weight_error_le_singularNormalization
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      492 * (N : ℝ) ^ (1 - (417 / 5000 : ℝ)) + 4 ≤
        epsilon * singularNormalization N := by
  have hquarter : 0 < epsilon / 4 := by linarith
  have hbudget := eventually_powerLog_add_one_le_singularNormalization
    123 (1 - (417 / 5000 : ℝ)) 0 (by norm_num) (epsilon / 4) hquarter
  filter_upwards [hbudget] with N hN
  simp only [pow_zero, mul_one] at hN
  nlinarith only [hN]

/-- The current weight-to-count inequality with its proved negligible
loss. The quantifier is uniform over the pair selection, so the actual
logarithmic rectangle predicate may depend on `N`. This proves no lower
mean estimate for that weight. -/
theorem eventually_currentChenPairedPrimeSum_sub_normalized_error_le_four_D12
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop,
      currentChenPairedPrimeSum N E - epsilon * singularNormalization N ≤
        4 * (D12 N : ℝ) := by
  filter_upwards [eventually_currentChen_weight_size_conditions,
    eventually_currentChen_weight_error_le_singularNormalization epsilon hepsilon]
    with N hsize herror
  intro E
  have hfinite := currentChenPairedPrimeSum_sub_power_error_le_four_D12
    N E hsize.1 hsize.2
  linarith only [hfinite, herror]

end

end ImbalancedChen
