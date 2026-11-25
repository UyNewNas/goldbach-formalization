import ImbalancedChen.ChenQuotientLevelGeometry

/-!
# Actual current pair selectors and their ordinary residual parameters

These instances use the current a=417/5000, h=19/125 and d=59/250,
not the older parameter tuple instantiated in ChenQuotientLevelGeometry.
The existing genuine selector gates supply positivity and coprimality;
the existing integer-row profile theorem pays rounding uniformly.

The whole fifth selector has residual parameter uniformly between 7/3
and 4 eventually. The whole sixth selector only has a bound between
4/3 and 16/5: it is not assigned a positive lower-sieve gain throughout.
A positive sixth-row gate is supplied only on the explicitly restricted
physical-product subdomain, with the original mask E retained. No integral,
saved gain, main mean, or complete Upsilon count is identified with that
smaller subdomain.

Held source candidate. This new module has not yet been compiled,
kernel-replayed, or axiom-audited.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open Classical

/-- Logarithmic model of the actual ordinary row parameter at the current
initial cutoff. The multiplier remains the literal labelled pair product. -/
def currentChenPairLogProfile (N b : ℕ) : ℝ :=
  ((1 / 2 : ℝ) - Real.log (b : ℝ) / Real.log (N : ℝ)) / (417 / 5000)

/-- Both endpoints are consequences of actual fifth-selector membership.
The lower bound uses both selected primes; the upper bound uses their
strict order and the strict second-prime endpoint. -/
theorem currentChenUpsilon5_multiplier_power_bounds {N : ℕ} {t : ℕ × ℕ}
    (hN : (1 : ℝ) ≤ N)
    (ht : t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ))) :
    (N : ℝ) ^ (417 / 2500 : ℝ) ≤ (t.1 * t.2 : ℕ) ∧
      ((t.1 * t.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (38 / 125 : ℝ) := by
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  obtain ⟨_, hA, horder, hH⟩ := Finset.mem_filter.mp ht
  have horderR : (t.1 : ℝ) ≤ t.2 := by exact_mod_cast horder.le
  have hA₂ := hA.trans horderR
  have hH₁ := horderR.trans hH.le
  have hlo : (N : ℝ) ^ (417 / 5000 : ℝ) *
      (N : ℝ) ^ (417 / 5000 : ℝ) ≤ ((t.1 * t.2 : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hA hA₂ (Real.rpow_nonneg hNp.le _) (Nat.cast_nonneg _)
  have hhi : ((t.1 * t.2 : ℕ) : ℝ) ≤
      (N : ℝ) ^ (19 / 125 : ℝ) * (N : ℝ) ^ (19 / 125 : ℝ) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hH₁ hH.le (Nat.cast_nonneg _) (Real.rpow_nonneg hNp.le _)
  rw [← Real.rpow_add hNp] at hlo hhi
  constructor
  · convert hlo using 1; norm_num
  · convert hhi using 1; norm_num

/-- The full sixth rectangle is kept, including its inclusive second-prime
lower endpoint. Its largest product exponent is 97/250, above the
lower-positive boundary 833/2500. -/
theorem currentChenUpsilon6_multiplier_power_bounds {N : ℕ} {t : ℕ × ℕ}
    (hN : (1 : ℝ) ≤ N)
    (ht : t ∈ chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))) :
    (N : ℝ) ^ (1177 / 5000 : ℝ) ≤ (t.1 * t.2 : ℕ) ∧
      ((t.1 * t.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (97 / 250 : ℝ) := by
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  obtain ⟨_, hA, hH₁, hH₂, hD⟩ := Finset.mem_filter.mp ht
  have hlo : (N : ℝ) ^ (417 / 5000 : ℝ) *
      (N : ℝ) ^ (19 / 125 : ℝ) ≤ ((t.1 * t.2 : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hA hH₂ (Real.rpow_nonneg hNp.le _) (Nat.cast_nonneg _)
  have hhi : ((t.1 * t.2 : ℕ) : ℝ) ≤
      (N : ℝ) ^ (19 / 125 : ℝ) * (N : ℝ) ^ (59 / 250 : ℝ) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hH₁.le hD.le (Nat.cast_nonneg _) (Real.rpow_nonneg hNp.le _)
  rw [← Real.rpow_add hNp] at hlo hhi
  constructor
  · convert hlo using 1; norm_num
  · convert hhi using 1; norm_num

private theorem currentChenPairLogProfile_mem_of_power_bounds
    {N b : ℕ} {lo hi : ℝ} (hN : 2 ≤ N) (hb : 0 < b)
    (hlo : (N : ℝ) ^ lo ≤ b) (hhi : (b : ℝ) ≤ (N : ℝ) ^ hi) :
    currentChenPairLogProfile N b ∈
      Set.Icc ((1 / 2 - hi) / (417 / 5000)) ((1 / 2 - lo) / (417 / 5000)) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlogp := Real.log_pos hN1
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  have hloglo := Real.log_le_log (Real.rpow_pos_of_pos hNp lo) hlo
  have hloghi := Real.log_le_log hbp hhi
  rw [Real.log_rpow hNp] at hloglo hloghi
  have hquotlo : lo ≤ Real.log (b : ℝ) / Real.log (N : ℝ) :=
    (le_div_iff₀ hlogp).mpr (by nlinarith only [hloglo])
  have hquothi : Real.log (b : ℝ) / Real.log (N : ℝ) ≤ hi :=
    (div_le_iff₀ hlogp).mpr (by nlinarith only [hloghi])
  constructor <;> unfold currentChenPairLogProfile
  · exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
  · exact div_le_div_of_nonneg_right (by linarith) (by norm_num)

/-- The fifth model parameter lies strictly inside the first lower-sieve
interval with an explicit fixed gap at both ends. -/
theorem currentChenUpsilon5_profile_mem {N : ℕ} {t : ℕ × ℕ} (hN : 2 ≤ N)
    (ht : t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ))) :
    currentChenPairLogProfile N (t.1 * t.2) ∈
      Set.Icc (980 / 417 : ℝ) (1666 / 417) := by
  obtain ⟨hlo, hhi⟩ := currentChenUpsilon5_multiplier_power_bounds
    (by exact_mod_cast (show 1 ≤ N by omega)) ht
  have hb : 0 < t.1 * t.2 :=
    Nat.zero_lt_one.trans (chenY5PrimeSelector_sieve_data ht).1
  convert currentChenPairLogProfile_mem_of_power_bounds hN hb hlo hhi using 1; norm_num

/-- The whole sixth model range crosses the s=2 boundary. This statement
does not assert a positive ordinary lower-sieve factor throughout it. -/
theorem currentChenUpsilon6_profile_mem {N : ℕ} {t : ℕ × ℕ} (hN : 2 ≤ N)
    (ht : t ∈ chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))) :
    currentChenPairLogProfile N (t.1 * t.2) ∈
      Set.Icc (560 / 417 : ℝ) (441 / 139) := by
  obtain ⟨hlo, hhi⟩ := currentChenUpsilon6_multiplier_power_bounds
    (by exact_mod_cast (show 1 ≤ N by omega)) ht
  have hb : 0 < t.1 * t.2 :=
    Nat.zero_lt_one.trans (chenY6PrimeSelector_sieve_data ht).1
  convert currentChenPairLogProfile_mem_of_power_bounds hN hb hlo hhi using 1; norm_num

/-- Rounding and the actual logarithmic level loss are uniformly paid
before selecting any fifth-row label. -/
theorem eventually_currentChenUpsilon5_row_profile (B epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈
      chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (19 / 125 : ℝ)),
      |chenQuotientRosserT B (417 / 5000) N (t.1 * t.2) -
        currentChenPairLogProfile N (t.1 * t.2)| < epsilon := by
  filter_upwards [eventually_chenQuotientRosserT_profile B (38 / 125) (417 / 5000)
    (by norm_num) (by norm_num) epsilon hepsilon, eventually_ge_atTop (1 : ℕ)]
    with N hprofile hN
  intro t ht
  exact hprofile (t.1 * t.2)
    (Nat.zero_lt_one.trans (chenY5PrimeSelector_sieve_data ht).1)
    (currentChenUpsilon5_multiplier_power_bounds (by exact_mod_cast hN) ht).2

/-- The full sixth selector, with no product-domain removal, has the same
uniform physical-level profile control. -/
theorem eventually_currentChenUpsilon6_row_profile (B epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈
      chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)),
      |chenQuotientRosserT B (417 / 5000) N (t.1 * t.2) -
        currentChenPairLogProfile N (t.1 * t.2)| < epsilon := by
  filter_upwards [eventually_chenQuotientRosserT_profile B (97 / 250) (417 / 5000)
    (by norm_num) (by norm_num) epsilon hepsilon, eventually_ge_atTop (1 : ℕ)]
    with N hprofile hN
  intro t ht
  exact hprofile (t.1 * t.2)
    (Nat.zero_lt_one.trans (chenY6PrimeSelector_sieve_data ht).1)
    (currentChenUpsilon6_multiplier_power_bounds (by exact_mod_cast hN) ht).2

/-- Actual integer fifth-row parameters eventually stay in one fixed
compact subinterval of 2<s<=4, uniformly in every selected pair. -/
theorem eventually_currentChenUpsilon5_row_first_interval (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈
      chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (19 / 125 : ℝ)),
      chenQuotientRosserT B (417 / 5000) N (t.1 * t.2) ∈ Set.Ioo (7 / 3 : ℝ) 4 := by
  filter_upwards [eventually_currentChenUpsilon5_row_profile B (1 / 1000) (by norm_num),
    eventually_ge_atTop (2 : ℕ)] with N hprofile hN
  intro t ht
  obtain ⟨hlo, hhi⟩ := currentChenUpsilon5_profile_mem hN ht
  obtain ⟨herrorlo, herrorhi⟩ := abs_lt.mp (hprofile t ht)
  constructor <;> linarith

/-- Actual full-rectangle sixth-row parameters are controlled without
falsely asserting s>2 on the entire original selector. -/
theorem eventually_currentChenUpsilon6_row_interval (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈
      chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)),
      chenQuotientRosserT B (417 / 5000) N (t.1 * t.2) ∈
        Set.Ioo (4 / 3 : ℝ) (16 / 5) := by
  filter_upwards [eventually_currentChenUpsilon6_row_profile B (1 / 1000) (by norm_num),
    eventually_ge_atTop (2 : ℕ)] with N hprofile hN
  intro t ht
  obtain ⟨hlo, hhi⟩ := currentChenUpsilon6_profile_mem hN ht
  obtain ⟨herrorlo, herrorhi⟩ := abs_lt.mp (hprofile t ht)
  constructor <;> linarith

/-- A genuine sixth-row positive gate requires a fixed gap below the
physical product boundary N^(1/2-2a). The original mask E is retained;
the conclusion is only for the displayed additional product subdomain.
No full-selector gain is assigned to this subdomain. -/
theorem eventually_currentChenUpsilon6_positive_product_subdomain
    (B eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop, ∀ t ∈
      (chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))).filter
        (fun t => E t ∧ ((t.1 * t.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (833 / 2500 - eta)),
      2 < chenQuotientRosserT B (417 / 5000) N (t.1 * t.2) := by
  have hbeta : (833 / 2500 : ℝ) - eta < 1 / 2 := by linarith
  have hgap : (2 : ℝ) < (1 / 2 - (833 / 2500 - eta)) / (417 / 5000) := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 417 / 5000)).mpr
    linarith
  filter_upwards [eventually_chenQuotientRosserT_gt B (833 / 2500 - eta)
    (417 / 5000) 2 hbeta (by norm_num) hgap] with N hpositive
  intro E t ht
  obtain ⟨hselector, _hE, hproduct⟩ := Finset.mem_filter.mp ht
  exact hpositive (t.1 * t.2)
    (Nat.zero_lt_one.trans (chenY6PrimeSelector_sieve_data hselector).1) hproduct

end

end ImbalancedChen
