import ImbalancedChen.Part3PrimeAPDistribution
import ImbalancedChen.ChenQuotientBVFinite
import ImbalancedChen.PowerErrorBudget

/-!
# The current lower rows and the genuine ordinary BV supplier

This file uses the frozen exponents `a=417/5000`, `h=19/125`, `d=59/250`.
The historical `chenUpsilon36` wrappers use different exponents and are not
silently reused as current instances.  Their general selector and pooling
theorems are reused instead.

One threshold precedes every choice of the four row families.  The required
cap is on the complete physical modulus, including the selected prime(s).
This file proves no cap for the future compiled high-level policy.  It pays
actual ordinary-prime AP errors and complete quotient remainders for every
row family satisfying this cap.  The four-row remainder supplier uses the
actual `singularNormalization`; identifying the rows of the full current
lower policy and supplying their physical caps remains a separate input.

The added normalized remainder supplier is a proof candidate pending
kernel/CI validation; source-level API checks alone do not establish it.
-/

namespace ImbalancedChen

noncomputable section

open Filter
open scoped BigOperators
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

/-- Exactly the four current prime bands, with four independently varying
inner supports.  `ChenQuotientRows` retains actual divisor membership and
the full product cap, rather than merely a bound on the inner divisor. -/
def Part3CurrentLowerRows (N Q : ℕ) (S3 S4 : ℕ → Finset ℕ)
    (S5 S6 : (ℕ × ℕ) → Finset ℕ) : Prop :=
  ChenQuotientRows N ((N : ℝ) ^ (417 / 5000 : ℝ)) Q
    (chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) id S3 ∧
  ChenQuotientRows N ((N : ℝ) ^ (417 / 5000 : ℝ)) Q
    (chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ))) id S4 ∧
  ChenQuotientRows N ((N : ℝ) ^ (417 / 5000 : ℝ)) Q
    (chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ))) (fun t => t.1 * t.2) S5 ∧
  ChenQuotientRows N ((N : ℝ) ^ (417 / 5000 : ℝ)) Q
    (chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)))
    (fun t => t.1 * t.2) S6

/-- The four literal product-modulus errors at the common genuine `li`
centre.  Squares in receivers and all labelled row multiplicities persist. -/
def part3CurrentLowerAPError (N : ℕ) (S3 S4 : ℕ → Finset ℕ)
    (S5 S6 : (ℕ × ℕ) → Finset ℕ) : ℝ :=
  (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)), ∑ e ∈ S3 p,
    |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (p * e)|) +
  (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ)), ∑ e ∈ S4 p,
    |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (p * e)|) +
  (∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)), ∑ e ∈ S5 t,
    |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) ((t.1 * t.2) * e)|) +
  (∑ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)), ∑ e ∈ S6 t,
    |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) ((t.1 * t.2) * e)|)

/-- One factor four, for the four displayed terms.  No selector-cardinality,
divisor-multiplicity or residue-cardinality factor is introduced. -/
theorem part3CurrentLowerAPError_le_four_pool (N Q : ℕ)
    (S3 S4 : ℕ → Finset ℕ) (S5 S6 : (ℕ × ℕ) → Finset ℕ)
    (hrows : Part3CurrentLowerRows N Q S3 S4 S5 S6) :
    part3CurrentLowerAPError N S3 S4 S5 S6 ≤
      4 * (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) := by
  obtain ⟨h3, h4, h5, h6⟩ := hrows
  have b3 := chenSinglePrimeSelector_pooled_AP_bound N _ _
    (trueLogarithmicIntegral N) Q S3
    (fun p hp e he => (Finset.mem_filter.mp (h3 p hp he)).1)
    (fun p hp e he => (Finset.mem_filter.mp (h3 p hp he)).2)
  have b4 := chenSinglePrimeSelector_pooled_AP_bound N _ _
    (trueLogarithmicIntegral N) Q S4
    (fun p hp e he => (Finset.mem_filter.mp (h4 p hp he)).1)
    (fun p hp e he => (Finset.mem_filter.mp (h4 p hp he)).2)
  have b5 := chenY5PrimeSelector_pooled_AP_bound N _ _
    (trueLogarithmicIntegral N) Q S5
    (fun t ht e he => (Finset.mem_filter.mp (h5 t ht he)).1)
    (fun t ht e he => (Finset.mem_filter.mp (h5 t ht he)).2)
  have b6 := chenY6PrimeSelector_pooled_AP_bound N _ _ _
    (trueLogarithmicIntegral N) Q S6
    (fun t ht e he => (Finset.mem_filter.mp (h6 t ht he)).1)
    (fun t ht e he => (Finset.mem_filter.mp (h6 t ht he)).2)
  unfold part3CurrentLowerAPError
  linarith only [b3, b4, b5, b6]

/-- Unconditional actual-prime distribution for the current four bands,
uniform over all row families obeying the displayed below-half *physical*
modulus cap.  The only premises are finite legal support conditions. -/
theorem part3_currentLowerAPError_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S3 S4 : ℕ → Finset ℕ, ∀ S5 S6 : (ℕ × ℕ) → Finset ℕ,
          Part3CurrentLowerRows N Q S3 S4 S5 S6 →
          part3CurrentLowerAPError N S3 S4 S5 S6 ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, hB, C, hC, hBV⟩ := part3_chenQuotientPrimeAPError_pool_log_saving A hA
  refine ⟨B, hB, 4 * C, by positivity, ?_⟩
  filter_upwards [hBV] with N hN
  intro Q hQ S3 S4 S5 S6 hrows
  calc
    _ ≤ 4 * (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) :=
      part3CurrentLowerAPError_le_four_pool N Q S3 S4 S5 S6 hrows
    _ ≤ 4 * (C * (N : ℝ) / Real.log (N : ℝ) ^ A) :=
      mul_le_mul_of_nonneg_left (hN Q hQ) (by norm_num)
    _ = (4 * C) * (N : ℝ) / Real.log (N : ℝ) ^ A := by ring

/-- The real quotient-sieve remainder gets the same analytic input.  Both
the secondary base-modulus error (the explicit logarithmic factor) and the
complete prime-centre correction remain visible.  The row labels, real
cutoff and inner supports may all vary after the common BV threshold. -/
theorem part3_quotientRemainder_log_saving_add_centre
    {α : Type*} (accuracy : ℝ) (haccuracy : 0 < accuracy) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ A : ℝ, ∀ T : Finset α, ∀ b : α → ℕ, ∀ S : α → Finset ℕ,
          ∀ hN : Even N,
          ∀ hbpos : ∀ t ∈ T, 0 < b t,
          ∀ hbN : ∀ t ∈ T, Nat.Coprime (b t) N,
          ∀ hb : ∀ t ∈ T, Nat.Coprime (b t) (sieveProduct N (Nat.ceil A)),
          Set.InjOn b (T : Set α) → ChenQuotientRows N A Q T b S →
          (∑ t ∈ T.attach, ∑ e ∈ S t.val,
            |(chenQuotientBoundingSieve N (b t.val) A hN (hb t.val t.property)).rem e|) ≤
            (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) *
              (C * (N : ℝ) / Real.log (N : ℝ) ^ accuracy) +
                chenSelectedCentreCost N T b S := by
  obtain ⟨B, hB, C, hC, hBV⟩ :=
    part3_chenQuotientPrimeAPError_pool_log_saving accuracy haccuracy
  refine ⟨B, hB, C, hC, ?_⟩
  filter_upwards [hBV] with N hN
  intro Q hQ A T b S heven hbpos hbN hb hinj hrows
  refine (sum_abs_chenQuotient_rem_le_primitive_log_add_cost
    T b S N A (trueLogarithmicIntegral N) Q heven hbpos hbN hb hinj
    (fun t ht e he => (Finset.mem_filter.mp (hrows t ht he)).1)
    (fun t ht e he => (Finset.mem_filter.mp (hrows t ht he)).2)).trans ?_
  refine add_le_add ?_ le_rfl
  exact mul_le_mul_of_nonneg_left (hN Q hQ) (by
    have hlog : 0 ≤ Real.log (max 1 (Q : ℝ)) := Real.log_nonneg (le_max_left _ _)
    positivity)

/-- The four genuine quotient-sieve remainder sums, with the current
prime bands and unit absolute outer coefficients.  Each attached label
supplies its actual coprimality proof to `chenQuotientBoundingSieve`. -/
def part3CurrentLowerRemainderSum (N : ℕ) (hN : Even N)
    (S3 S4 : ℕ → Finset ℕ) (S5 S6 : (ℕ × ℕ) → Finset ℕ) : ℝ :=
  (∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))).attach, ∑ e ∈ S3 p.val,
    |(chenQuotientBoundingSieve N p.val ((N : ℝ) ^ (417 / 5000 : ℝ)) hN
      (chenSinglePrimeSelector_sieve_data p.property).2.2).rem e|) +
  (∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ))).attach, ∑ e ∈ S4 p.val,
    |(chenQuotientBoundingSieve N p.val ((N : ℝ) ^ (417 / 5000 : ℝ)) hN
      (chenSinglePrimeSelector_sieve_data p.property).2.2).rem e|) +
  (∑ t ∈ (chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ))).attach, ∑ e ∈ S5 t.val,
    |(chenQuotientBoundingSieve N (t.val.1 * t.val.2)
      ((N : ℝ) ^ (417 / 5000 : ℝ)) hN
      (chenY5PrimeSelector_sieve_data t.property).2.2).rem e|) +
  (∑ t ∈ (chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))).attach,
      ∑ e ∈ S6 t.val,
    |(chenQuotientBoundingSieve N (t.val.1 * t.val.2)
      ((N : ℝ) ^ (417 / 5000 : ℝ)) hN
      (chenY6PrimeSelector_sieve_data t.property).2.2).rem e|)

/-- Every labelled centre correction in the four current rows. -/
def part3CurrentLowerCentreCost (N : ℕ) (S3 S4 : ℕ → Finset ℕ)
    (S5 S6 : (ℕ × ℕ) → Finset ℕ) : ℝ :=
  chenSelectedCentreCost N
      (chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ))) id S3 +
    chenSelectedCentreCost N
      (chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (59 / 250 : ℝ))) id S4 +
    chenSelectedCentreCost N
      (chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ))) (fun t => t.1 * t.2) S5 +
    chenSelectedCentreCost N
      (chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)))
      (fun t => t.1 * t.2) S6

/-- Both ordinary-AP errors of each quotient remainder share one
primitive pool.  The current selectors are instantiated directly. -/
theorem part3CurrentLowerRemainderSum_le_primitive_log_add_cost
    (N Q : ℕ) (hN : Even N) (M : ℝ)
    (S3 S4 : ℕ → Finset ℕ) (S5 S6 : (ℕ × ℕ) → Finset ℕ)
    (hrows : Part3CurrentLowerRows N Q S3 S4 S5 S6) :
    part3CurrentLowerRemainderSum N hN S3 S4 S5 S6 ≤
      4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) *
        (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N M k|) +
            part3CurrentLowerCentreCost N S3 S4 S5 S6 := by
  obtain ⟨hr3, hr4, hr5, hr6⟩ := hrows
  have h3 := sum_abs_chenQuotient_rem_le_primitive_log_add_cost
    (chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) id S3 N ((N : ℝ) ^ (417 / 5000 : ℝ)) M Q hN
    (fun p hp => lt_trans Nat.zero_lt_one (chenSinglePrimeSelector_sieve_data hp).1)
    (fun p hp => (chenSinglePrimeSelector_sieve_data hp).2.1)
    (fun p hp => (chenSinglePrimeSelector_sieve_data hp).2.2)
    (fun _ _ _ _ h => h)
    (fun p hp e he => (Finset.mem_filter.mp (hr3 p hp he)).1)
    (fun p hp e he => (Finset.mem_filter.mp (hr3 p hp he)).2)
  have h4 := sum_abs_chenQuotient_rem_le_primitive_log_add_cost
    (chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ))) id S4 N ((N : ℝ) ^ (417 / 5000 : ℝ)) M Q hN
    (fun p hp => lt_trans Nat.zero_lt_one (chenSinglePrimeSelector_sieve_data hp).1)
    (fun p hp => (chenSinglePrimeSelector_sieve_data hp).2.1)
    (fun p hp => (chenSinglePrimeSelector_sieve_data hp).2.2)
    (fun _ _ _ _ h => h)
    (fun p hp e he => (Finset.mem_filter.mp (hr4 p hp he)).1)
    (fun p hp e he => (Finset.mem_filter.mp (hr4 p hp he)).2)
  have h5 := sum_abs_chenQuotient_rem_le_primitive_log_add_cost
    (chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)))
    (fun t => t.1 * t.2) S5 N ((N : ℝ) ^ (417 / 5000 : ℝ)) M Q hN
    (fun t ht => lt_trans Nat.zero_lt_one (chenY5PrimeSelector_sieve_data ht).1)
    (fun t ht => (chenY5PrimeSelector_sieve_data ht).2.1)
    (fun t ht => (chenY5PrimeSelector_sieve_data ht).2.2)
    (chenY5PrimeSelector_multiplier_injOn N _ _)
    (fun t ht e he => (Finset.mem_filter.mp (hr5 t ht he)).1)
    (fun t ht e he => (Finset.mem_filter.mp (hr5 t ht he)).2)
  have h6 := sum_abs_chenQuotient_rem_le_primitive_log_add_cost
    (chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)))
    (fun t => t.1 * t.2) S6 N ((N : ℝ) ^ (417 / 5000 : ℝ)) M Q hN
    (fun t ht => lt_trans Nat.zero_lt_one (chenY6PrimeSelector_sieve_data ht).1)
    (fun t ht => (chenY6PrimeSelector_sieve_data ht).2.1)
    (fun t ht => (chenY6PrimeSelector_sieve_data ht).2.2)
    (chenY6PrimeSelector_multiplier_injOn N _ _ _)
    (fun t ht e he => (Finset.mem_filter.mp (hr6 t ht he)).1)
    (fun t ht e he => (Finset.mem_filter.mp (hr6 t ht he)).2)
  unfold part3CurrentLowerRemainderSum part3CurrentLowerCentreCost
  linarith only [h3, h4, h5, h6]

/-- The complete current centre cost is sublinear under the full row
cap.  Only selected rows are constrained, including when other rows are
nonempty or have very large support. -/
theorem part3CurrentLowerCentreCost_le_sqrt_log_cube {N Q : ℕ}
    (hN : Even N) (hN4 : 4 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ))
    (hQ : (Q : ℝ) ≤ Real.sqrt (N : ℝ))
    (S3 S4 : ℕ → Finset ℕ) (S5 S6 : (ℕ × ℕ) → Finset ℕ)
    (hrows : Part3CurrentLowerRows N Q S3 S4 S5 S6) :
    part3CurrentLowerCentreCost N S3 S4 S5 S6 ≤
      (8 / (Real.log 2) ^ 3) * (N : ℝ) ^ (1 / 2 : ℝ) *
        (Real.log (N : ℝ)) ^ 3 := by
  obtain ⟨hr3, hr4, hr5, hr6⟩ := hrows
  have hpos : 0 < N := by omega
  have hNP := chen_not_prime_of_even_four_le hN hN4
  let L : ℝ := Real.log (N : ℝ) / Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have hL : 1 ≤ L := (le_div_iff₀ htwo).mpr (by simpa using htwo1.trans hlog)
  have hpow : L ^ 2 ≤ L ^ 3 := by
    have h := mul_nonneg (sub_nonneg.mpr hL) (sq_nonneg L)
    nlinarith
  have h3 := chenSinglePrimeSelector_centreCost_le_log_sq hpos hNP
    ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) S3
    (hr3.subset_Icc (fun p hp => lt_trans Nat.zero_lt_one
      (chenSinglePrimeSelector_sieve_data hp).1))
  have h4 := chenSinglePrimeSelector_centreCost_le_log_sq hpos hNP
    ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)) S4
    (hr4.subset_Icc (fun p hp => lt_trans Nat.zero_lt_one
      (chenSinglePrimeSelector_sieve_data hp).1))
  have h5 := chenY5PrimeSelector_centreCost_le_log_cube hpos hNP
    ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (19 / 125 : ℝ)) S5
    (hr5.subset_Icc (fun t ht => lt_trans Nat.zero_lt_one
      (chenY5PrimeSelector_sieve_data ht).1))
  have h6 := chenY6PrimeSelector_centreCost_le_log_cube hpos hNP
    ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (19 / 125 : ℝ))
    ((N : ℝ) ^ (59 / 250 : ℝ)) S6
    (hr6.subset_Icc (fun t ht => lt_trans Nat.zero_lt_one
      (chenY6PrimeSelector_sieve_data ht).1))
  have hmul := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2 * (Q : ℝ))
  have hcost : part3CurrentLowerCentreCost N S3 S4 S5 S6 ≤ 8 * (Q : ℝ) * L ^ 3 := by
    change _ ≤ 2 * (Q : ℝ) * L ^ 2 at h3 h4
    change _ ≤ 2 * (Q : ℝ) * L ^ 3 at h5 h6
    unfold part3CurrentLowerCentreCost
    linarith only [h3, h4, h5, h6, hmul]
  calc
    _ ≤ 8 * (Q : ℝ) * L ^ 3 := hcost
    _ ≤ 8 * Real.sqrt (N : ℝ) * L ^ 3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ (by norm_num))
        (pow_nonneg (zero_le_one.trans hL) 3)
    _ = _ := by dsimp only [L]; rw [Real.sqrt_eq_rpow, div_pow]; ring

/-- A nonnegative logarithmic loss keeps the BV cutoff below the
square-root level once the logarithm is at least one. -/
private theorem part3_panModulusCutoff_le_sqrt (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hlog : 1 ≤ Real.log (N : ℝ)) :
    (panModulusCutoff N B : ℝ) ≤ Real.sqrt (N : ℝ) := by
  have hden : 1 ≤ Real.log (N : ℝ) ^ B := Real.one_le_rpow hlog hB
  unfold panModulusCutoff
  calc
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B :=
      Nat.floor_le (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        (zero_le_one.trans hden))
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
      div_le_self (Real.rpow_nonneg (Nat.cast_nonneg N) _) hden
    _ = Real.sqrt (N : ℝ) := (Real.sqrt_eq_rpow _).symm

/-- One fixed BV logarithmic loss pays the complete genuine quotient
remainders in the four current bands.  `B` is chosen before `epsilon`;
the eventual threshold precedes `Q`, the evenness witness, and every row
family.  The remaining policy task is to supply these literal full
product caps, rather than just caps on the inner divisors. -/
theorem part3_currentLowerRemainder_negligible :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ hN : Even N,
        ∀ S3 S4 : ℕ → Finset ℕ, ∀ S5 S6 : (ℕ × ℕ) → Finset ℕ,
          Part3CurrentLowerRows N Q S3 S4 S5 S6 →
          part3CurrentLowerRemainderSum N hN S3 S4 S5 S6 ≤
            epsilon * singularNormalization N := by
  obtain ⟨B, hB, C, hC, hBV⟩ :=
    part3_chenQuotientPrimeAPError_pool_log_saving 4 (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro epsilon hepsilon
  have hlarge : ∀ᶠ N : ℕ in atTop,
      72 * C / (epsilon * twinPrimeConstant) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hBV, hlarge, eventually_one_le_nat_log,
    eventually_ge_atTop (4 : ℕ),
    eventually_powerLog_le_singularNormalization
      (8 / (Real.log 2) ^ 3) (1 / 2) 3 (by norm_num)
      (epsilon / 2) (half_pos hepsilon)] with N hBVN hlargeN hlog hN4 hcentreN
  intro Q hQ hN S3 S4 S5 S6 hrows
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hQsqrt : (Q : ℝ) ≤ Real.sqrt (N : ℝ) :=
    (show (Q : ℝ) ≤ (panModulusCutoff N B : ℝ) by exact_mod_cast hQ).trans
      (part3_panModulusCutoff_le_sqrt N B hB hlog)
  have hsqrtN : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_self_of_one_le hN1 (by norm_num)
  have hlogQ : Real.log (max 1 (Q : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (zero_lt_one.trans_le (le_max_left _ _))
      (max_le hN1 (hQsqrt.trans hsqrtN))
  have hfactor : 4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) ≤
      36 * Real.log (N : ℝ) := by linarith only [hlogQ, hlog]
  have hfactor0 : 0 ≤ 4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) := by
    have h := Real.log_nonneg (le_max_left (1 : ℝ) (Q : ℝ))
    positivity
  have hpool : (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
      |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) ≤
        C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast (Real.log (N : ℝ)) (4 : ℕ)]
    exact hBVN Q hQ
  have hterm : 4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) *
      (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) ≤
          36 * C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℕ) := by
    calc
      _ ≤ 4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) *
          (C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℕ)) :=
        mul_le_mul_of_nonneg_left hpool hfactor0
      _ ≤ (36 * Real.log (N : ℝ)) *
          (C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℕ)) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = _ := by field_simp [ne_of_gt hlogpos]
  have hlogprod : 72 * C ≤ Real.log (N : ℝ) * (epsilon * twinPrimeConstant) :=
    (div_le_iff₀ (mul_pos hepsilon twinPrimeConstant_pos)).mp hlargeN
  have hcoefficient : 36 * C / Real.log (N : ℝ) ≤
      (epsilon / 2) * twinPrimeConstant :=
    (div_le_iff₀ hlogpos).mpr (by nlinarith only [hlogprod])
  have hAP : 36 * C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℕ) ≤
      (epsilon / 2) * singularNormalization N := by
    calc
      _ = (36 * C / Real.log (N : ℝ)) *
          ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) := by
        field_simp [ne_of_gt hlogpos]
      _ ≤ ((epsilon / 2) * twinPrimeConstant) *
          ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hcoefficient (by positivity)
      _ = (epsilon / 2) *
          (twinPrimeConstant * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) := by ring
      _ ≤ (epsilon / 2) * singularNormalization N :=
        mul_le_mul_of_nonneg_left (singularNormalization_lower N) (half_pos hepsilon).le
  have hcentre : part3CurrentLowerCentreCost N S3 S4 S5 S6 ≤
      (epsilon / 2) * singularNormalization N :=
    (part3CurrentLowerCentreCost_le_sqrt_log_cube hN hN4 hlog hQsqrt
      S3 S4 S5 S6 hrows).trans hcentreN
  calc
    _ ≤ 4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) *
        (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) +
            part3CurrentLowerCentreCost N S3 S4 S5 S6 :=
      part3CurrentLowerRemainderSum_le_primitive_log_add_cost N Q hN
        (trueLogarithmicIntegral N) S3 S4 S5 S6 hrows
    _ ≤ (epsilon / 2) * singularNormalization N +
        (epsilon / 2) * singularNormalization N :=
      add_le_add (hterm.trans hAP) hcentre
    _ = epsilon * singularNormalization N := by ring

end

end ImbalancedChen
