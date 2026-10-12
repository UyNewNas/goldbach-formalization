import ImbalancedChen.Part3PrimeAPDistribution
import ImbalancedChen.ChenQuotientBVFinite

/-!
# The current lower rows and the genuine ordinary BV supplier

This file uses the frozen exponents `a=417/5000`, `h=19/125`, `d=59/250`.
The historical `chenUpsilon36` wrappers use different exponents and are not
silently reused as current instances.  Their general selector and pooling
theorems are reused instead.

One threshold precedes every choice of the four row families.  The required
cap is on the complete physical modulus, including the selected prime(s).
This file proves no cap for the future compiled high-level policy.  It pays
actual ordinary-prime AP errors for every row family satisfying this cap;
it does not identify those rows with the full current lower policy.
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
  apply add_le_add_right
  exact mul_le_mul_of_nonneg_left (hN Q hQ) (by
    have hlog : 0 ≤ Real.log (max 1 (Q : ℝ)) := Real.log_nonneg (le_max_left _ _)
    positivity)

end

end ImbalancedChen
