import ImbalancedChen.CurrentChenMeanLedger
import ImbalancedChen.ChenQuotientLevelGeometry

/-!
# Buffered product restriction for the actual current sixth Chen term

The retained pairs are a subset of the literal current sixth selector,
outside the same paired-deletion mask. Their product is at most
`N^(1/2 - 2*(417/5000) - eta)`. The omitted contribution is nonnegative,
so restricting this positive row gives a valid lower-bound direction.
The negative eleventh row is neither changed nor discarded.

For each fixed `eta > 0` and fixed real logarithmic loss `B`, the proved
uniform quotient-level geometry gives one threshold before all retained
pairs and masks. At the actual natural level
`D = floor(sqrt N / (log N)^B) / (p1*p2) + 1`, we prove the stronger bound
`N^(eta/2) < D / (N^(417/5000))^2`, and hence the strict gate `s > 2`.
Thus a strict product-exponent inequality is not being substituted for
the physical logarithmic-loss calculation.

This module does not evaluate the retained-region integral, remove eta,
prove a causal mean, or reuse the uncorrected full-region coefficient.
Its new declarations are source candidates pending P0 verification.
-/

namespace ImbalancedChen

noncomputable section

open Filter
open scoped BigOperators
open Classical

/-- The literal current sixth pair carrier, with the unchanged deletion
mask and the additional fixed product buffer. Pair labels are preserved. -/
def currentChenUpsilon6RetainedSelector (N : ℕ) (E : ℕ × ℕ → Prop)
    (eta : ℝ) : Finset (ℕ × ℕ) :=
  ((chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
    ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))).filter
      (fun t => ¬ E t)).filter
        (fun t => ((t.1 * t.2 : ℕ) : ℝ) ≤
          (N : ℝ) ^ ((1 / 2 : ℝ) - 2 * (417 / 5000 : ℝ) - eta))

/-- Actual sifted quotient counts on the retained pair labels. -/
def currentChenUpsilon6Retained (N : ℕ) (E : ℕ × ℕ → Prop) (eta : ℝ) : ℝ :=
  ∑ t ∈ currentChenUpsilon6RetainedSelector N E eta,
    ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
      ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)

theorem currentChenUpsilon6Retained_nonneg (N : ℕ) (E : ℕ × ℕ → Prop)
    (eta : ℝ) : 0 ≤ currentChenUpsilon6Retained N E eta := by
  exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- Exact retained/discarded partition of the same actual positive row.
The complement here is only the new product restriction, not the mask E. -/
theorem currentChenUpsilon6Retained_add_discarded (N : ℕ)
    (E : ℕ × ℕ → Prop) (eta : ℝ) :
    currentChenUpsilon6Retained N E eta +
      (∑ t ∈ ((chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))).filter
            (fun t => ¬ E t)).filter
              (fun t => ¬ ((t.1 * t.2 : ℕ) : ℝ) ≤
                (N : ℝ) ^ ((1 / 2 : ℝ) - 2 * (417 / 5000 : ℝ) - eta)),
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
          ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)) =
      currentChenUpsilon6 N E := by
  rw [currentChenUpsilon6_eq_siftedQuotientPrimeSource]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- Dropping the complementary positive counts is legitimate. No upper
estimate for a negative ledger row follows from this restriction. -/
theorem currentChenUpsilon6Retained_le (N : ℕ) (E : ℕ × ℕ → Prop)
    (eta : ℝ) : currentChenUpsilon6Retained N E eta ≤ currentChenUpsilon6 N E := by
  rw [currentChenUpsilon6_eq_siftedQuotientPrimeSource]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => Nat.cast_nonneg _)

/-- The positive fixed buffer implies Wu's strict product restriction.
The original individual upper bound on the second prime is not used as
a substitute for the product bound. -/
theorem currentChenUpsilon6Retained_product_lt {N : ℕ}
    (hN : (1 : ℝ) < N) {E : ℕ × ℕ → Prop} {eta : ℝ} (heta : 0 < eta)
    {t : ℕ × ℕ} (ht : t ∈ currentChenUpsilon6RetainedSelector N E eta) :
    ((t.1 * t.2 : ℕ) : ℝ) <
      (N : ℝ) ^ ((1 / 2 : ℝ) - 2 * (417 / 5000 : ℝ)) := by
  exact (Finset.mem_filter.mp ht).2.trans_lt
    (Real.rpow_lt_rpow_of_exponent_lt hN (by linarith))

/-- At each fixed buffer, the true rounded level pays the logarithmic
loss uniformly in every positive multiplier in the retained power range.
This uses the already proved arbitrary-beta geometry, not the old bands. -/
theorem eventually_currentChenUpsilon6_buffered_level (B eta : ℝ)
    (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ, 0 < b →
      (b : ℝ) ≤ (N : ℝ) ^ ((1 / 2 : ℝ) - 2 * (417 / 5000 : ℝ) - eta) →
      b ≤ chenInitialLevelCap B N ∧
      (N : ℝ) ^ (eta / 2) <
        (chenQuotientRosserD B N b : ℝ) / ((N : ℝ) ^ (417 / 5000 : ℝ)) ^ 2 ∧
      2 < chenQuotientRosserT B (417 / 5000 : ℝ) N b := by
  let beta : ℝ := (1 / 2 : ℝ) - 2 * (417 / 5000 : ℝ) - eta
  have hbeta : beta < 1 / 2 := by dsimp [beta]; linarith
  have ha : (0 : ℝ) < 417 / 5000 := by norm_num
  have hgap : 2 + (2500 / 417 : ℝ) * eta <
      ((1 / 2 : ℝ) - beta) / (417 / 5000 : ℝ) := by
    dsimp [beta]
    norm_num
    linarith
  filter_upwards [eventually_powerBound_le_chenInitialLevelCap B beta hbeta,
    eventually_chenQuotientRosserT_gt B beta (417 / 5000 : ℝ)
      (2 + (2500 / 417 : ℝ) * eta) hbeta ha hgap,
    eventually_ge_atTop (2 : ℕ)] with N hcap hgate hN
  intro b hb hbpower
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hz : 1 < (N : ℝ) ^ (417 / 5000 : ℝ) := Real.one_lt_rpow hN1 ha
  have hs := hgate b hb hbpower
  have hlog :
      (2 + (2500 / 417 : ℝ) * eta) *
          Real.log ((N : ℝ) ^ (417 / 5000 : ℝ)) <
        Real.log (chenQuotientRosserD B N b : ℝ) :=
    (lt_div_iff₀ (Real.log_pos hz)).mp hs
  have hlogPower :
      Real.log ((N : ℝ) ^ (2 * (417 / 5000 : ℝ) + eta / 2)) <
        Real.log (chenQuotientRosserD B N b : ℝ) := by
    rw [Real.log_rpow hNpos] at hlog ⊢
    nlinarith only [hlog]
  have hDpos : (0 : ℝ) < chenQuotientRosserD B N b := by
    unfold chenQuotientRosserD chenQuotientRowLevel
    positivity
  have hpower : (N : ℝ) ^ (2 * (417 / 5000 : ℝ) + eta / 2) <
      (chenQuotientRosserD B N b : ℝ) :=
    (Real.log_lt_log_iff (Real.rpow_pos_of_pos hNpos _) hDpos).mp hlogPower
  have hsq : ((N : ℝ) ^ (417 / 5000 : ℝ)) ^ 2 =
      (N : ℝ) ^ (2 * (417 / 5000 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  have hprod : (N : ℝ) ^ (eta / 2) * ((N : ℝ) ^ (417 / 5000 : ℝ)) ^ 2 =
      (N : ℝ) ^ (2 * (417 / 5000 : ℝ) + eta / 2) := by
    rw [hsq, ← Real.rpow_add hNpos]
    congr 1
    ring
  refine ⟨hcap b hbpower, ?_, ?_⟩
  · apply (lt_div_iff₀ (sq_pos_of_pos (zero_lt_one.trans hz))).mpr
    rw [hprod]
    exact hpower
  · have hpad : 0 < (2500 / 417 : ℝ) * eta := mul_pos (by norm_num) heta
    linarith

/-- One common threshold is chosen after B and eta, but before the pair
mask and every actual retained pair. The ratio is strictly above one and
the actual linear-sieve parameter is strictly above two. -/
theorem eventually_currentChenUpsilon6Retained_physical_gates (B eta : ℝ)
    (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop,
      ∀ t ∈ currentChenUpsilon6RetainedSelector N E eta,
        t.1 * t.2 ≤ chenInitialLevelCap B N ∧
        1 < (chenQuotientRosserD B N (t.1 * t.2) : ℝ) /
          ((N : ℝ) ^ (417 / 5000 : ℝ)) ^ 2 ∧
        2 < chenQuotientRosserT B (417 / 5000 : ℝ) N (t.1 * t.2) := by
  filter_upwards [eventually_currentChenUpsilon6_buffered_level B eta heta,
    eventually_ge_atTop (2 : ℕ)] with N hgate hN
  intro E t ht
  obtain ⟨htmask, hproduct⟩ := Finset.mem_filter.mp ht
  have htselector := (Finset.mem_filter.mp htmask).1
  have htcarrier := (Finset.mem_filter.mp htselector).1
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp htcarrier
  have hb : 0 < t.1 * t.2 := mul_pos
    (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos
    (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos
  obtain ⟨hcap, hratio, hs⟩ := hgate (t.1 * t.2) hb hproduct
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact ⟨hcap, (Real.one_lt_rpow hN1 (half_pos heta)).trans hratio, hs⟩

end

end ImbalancedChen
