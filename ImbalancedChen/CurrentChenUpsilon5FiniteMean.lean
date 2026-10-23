import ImbalancedChen.CurrentChenPairRosser
import ImbalancedChen.CurrentChenMeanLedger
import ImbalancedChen.Part3CurrentLowerDistribution

/-!
# Actual fifth-row counts with a fully paid ordinary remainder

The pointwise actual Rosser inequality, its full physical row support, the
ordinary BV prime-AP supplier, and the complete centre cost are instantiated
and paid. The final actual-count conclusion has no analytic premise.
Its main term keeps the same actual row-dependent Rosser coefficient;
identifying its limiting integral is a separate component.

Executed verification status is recorded in
`docs/PROOF_CONTINUATION_2026-10-15.md`.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

/-- The literal same-coefficient density main term, at every genuine
rounded row level, before any limiting prime-pair replacement. -/
def currentChenUpsilon5OrdinaryDensitySum (B : ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)),
    trueLogarithmicIntegral N / (Nat.totient (t.1 * t.2) : ℝ) *
      actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
        ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N (t.1 * t.2) : ℝ)

/-- A concrete row family, not an unspecified future sieve policy. -/
def currentChenUpsilon5OrdinaryRows (N Q : ℕ) : (ℕ × ℕ) → Finset ℕ :=
  fun t => currentChenQuotientRosserActive N (t.1 * t.2)
    (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ))) Q ((N : ℝ) ^ (417 / 5000 : ℝ))

/-- These exact rows satisfy the genuine Part 3 physical-cap interface.
The other three bands are empty rather than being silently estimated. -/
theorem currentChenUpsilon5OrdinaryRows_admissible (N Q : ℕ) :
    Part3CurrentLowerRows N Q (fun _ => ∅) (fun _ => ∅)
      (currentChenUpsilon5OrdinaryRows N Q) (fun _ => ∅) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht d hd
    simp at hd
  · intro t ht d hd
    simp at hd
  · intro t ht d hd
    exact Finset.mem_filter.mpr
      ⟨currentChenQuotientRosserActive_divisor (Nat.le_ceil _) hd,
        currentChenQuotientRosserActive_physical_cap
          (Nat.zero_lt_one.trans (chenY5PrimeSelector_sieve_data ht).1) hd⟩
  · intro t ht d hd
    simp at hd

/-- The actual logarithmic row parameter supplies the level gates directly.
No density normalization or fixed surrogate level is used. -/
theorem eventually_currentChenUpsilon5_ordinary_row_level (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈
      chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)),
      1 < (chenQuotientRosserD B N (t.1 * t.2) : ℝ) ∧
        (N : ℝ) ^ (417 / 5000 : ℝ) ≤
          (chenQuotientRosserD B N (t.1 * t.2) : ℝ) := by
  filter_upwards [eventually_currentChenUpsilon5_row_first_interval B,
    eventually_ge_atTop (2 : ℕ)] with N hrows hN
  intro t ht
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hs := (hrows t ht).1
  have hz := Real.one_lt_rpow hN1 (by norm_num : (0 : ℝ) < 417 / 5000)
  have hDp : (0 : ℝ) < chenQuotientRosserD B N (t.1 * t.2) := by
    unfold chenQuotientRosserD chenQuotientRowLevel
    positivity
  have hratio : (1 : ℝ) <
      Real.log (chenQuotientRosserD B N (t.1 * t.2) : ℝ) /
        Real.log ((N : ℝ) ^ (417 / 5000 : ℝ)) := by
    change (1 : ℝ) < chenQuotientRosserT B (417 / 5000) N (t.1 * t.2)
    linarith only [hs]
  have hlog := (lt_div_iff₀ (Real.log_pos hz)).mp hratio
  have hlt : (N : ℝ) ^ (417 / 5000 : ℝ) <
      (chenQuotientRosserD B N (t.1 * t.2) : ℝ) :=
    (Real.log_lt_log_iff (zero_lt_one.trans hz) hDp).mp (by simpa only [one_mul] using hlog)
  exact ⟨hz.trans hlt, hlt.le⟩

/-- Summing the actual quotient Rosser inequality and bounding its signed
errors by their literal nonzero-row L1 costs gives a finite true U5 bound. -/
theorem currentChenUpsilon5_ge_ordinary_density_sub_costs
    (B : ℝ) (N : ℕ)
    (hlevels : ∀ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)),
      1 < (chenQuotientRosserD B N (t.1 * t.2) : ℝ) ∧
        (N : ℝ) ^ (417 / 5000 : ℝ) ≤
          (chenQuotientRosserD B N (t.1 * t.2) : ℝ)) :
    currentChenUpsilon5OrdinaryDensitySum B N -
        part3CurrentLowerAPError N (fun _ => ∅) (fun _ => ∅)
          (currentChenUpsilon5OrdinaryRows N (chenInitialLevelCap B N)) (fun _ => ∅) -
        part3CurrentLowerCentreCost N (fun _ => ∅) (fun _ => ∅)
          (currentChenUpsilon5OrdinaryRows N (chenInitialLevelCap B N)) (fun _ => ∅) ≤
      currentChenUpsilon5 N := by
  let z : ℝ := (N : ℝ) ^ (417 / 5000 : ℝ)
  let cap : ℕ := Nat.ceil z
  let Q : ℕ := chenInitialLevelCap B N
  let T := chenY5PrimeSelector N z ((N : ℝ) ^ (19 / 125 : ℝ))
  have hrow (t : ℕ × ℕ) (ht : t ∈ T) :
      trueLogarithmicIntegral N / (Nat.totient (t.1 * t.2) : ℝ) *
          actualSmallRosserMinusDensity N cap z (chenQuotientRowLevel Q (t.1 * t.2) : ℝ) -
        (∑ d ∈ currentChenQuotientRosserActive N (t.1 * t.2) cap Q z,
          |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) ((t.1 * t.2) * d)|) -
        (∑ d ∈ currentChenQuotientRosserActive N (t.1 * t.2) cap Q z,
          chenQuotientCentreCost N (t.1 * t.2) d) ≤
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) z).card : ℝ) := by
    have h := currentChen_quotient_actualRosser_density_lower N (t.1 * t.2) cap z
      (chenQuotientRowLevel Q (t.1 * t.2)) (Nat.le_ceil z)
      (chenY5PrimeSelector_sieve_data ht).2.2 (hlevels t ht).1 (hlevels t ht).2
    rw [currentChen_quotientRosser_sum_eq_active,
      currentChen_quotientRosser_sum_eq_active] at h
    have hAP : -(∑ d ∈ currentChenQuotientRosserActive N (t.1 * t.2) cap Q z,
        |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) ((t.1 * t.2) * d)|) ≤
      ∑ d ∈ currentChenQuotientRosserActive N (t.1 * t.2) cap Q z,
        actualSmallRosserMinus N cap z (chenQuotientRowLevel Q (t.1 * t.2) : ℝ) d *
          chenQuotientPrimeAPError N (trueLogarithmicIntegral N) ((t.1 * t.2) * d) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro d hd
      have habs := mul_le_mul_of_nonneg_right
        (actualSmallRosserMinus_abs_le_one N cap z
          (chenQuotientRowLevel Q (t.1 * t.2)) d)
        (abs_nonneg (chenQuotientPrimeAPError N (trueLogarithmicIntegral N)
          ((t.1 * t.2) * d)))
      rw [← abs_mul, one_mul] at habs
      exact (neg_le_neg habs).trans (neg_abs_le _)
    have hcentre :
        (∑ d ∈ currentChenQuotientRosserActive N (t.1 * t.2) cap Q z,
          actualSmallRosserMinus N cap z (chenQuotientRowLevel Q (t.1 * t.2) : ℝ) d *
            chenCentrePrimeAPCount N N ((t.1 * t.2) * d)) ≤
          ∑ d ∈ currentChenQuotientRosserActive N (t.1 * t.2) cap Q z,
            chenQuotientCentreCost N (t.1 * t.2) d := by
      apply Finset.sum_le_sum
      intro d hd
      have hb := (le_abs_self
        (actualSmallRosserMinus N cap z (chenQuotientRowLevel Q (t.1 * t.2)) d)).trans
          (actualSmallRosserMinus_abs_le_one N cap z
            (chenQuotientRowLevel Q (t.1 * t.2)) d)
      have hm := mul_le_mul_of_nonneg_right hb
        (chenCentrePrimeAPCount_nonneg N N ((t.1 * t.2) * d))
      have hc : chenCentrePrimeAPCount N N ((t.1 * t.2) * d) ≤
          chenQuotientCentreCost N (t.1 * t.2) d := by
        unfold chenQuotientCentreCost
        exact le_add_of_nonneg_left
          (div_nonneg (chenCentrePrimeAPCount_nonneg N N (t.1 * t.2))
            (Nat.cast_nonneg _))
      simp only [one_mul] at hm
      exact hm.trans hc
    linarith only [h, hAP, hcentre]
  have hsum := Finset.sum_le_sum hrow
  rw [currentChenUpsilon5_eq_siftedQuotientPrimeSource]
  simpa only [currentChenUpsilon5OrdinaryDensitySum, part3CurrentLowerAPError,
    part3CurrentLowerCentreCost, chenSelectedCentreCost,
    currentChenUpsilon5OrdinaryRows, Finset.sum_empty, Finset.sum_const_zero, add_zero, zero_add,
    Finset.sum_sub_distrib, chenQuotientRosserD, T, Q, cap, z] using hsum

/-- One fixed ordinary-BV logarithmic loss pays the full fifth-row AP and
centre errors. Its exact rounded same-coefficient density main sum is a
proved lower bound, with no analytic supplier left as a hypothesis. -/
theorem eventually_currentChenUpsilon5_ge_ordinary_density_sum :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N →
        currentChenUpsilon5OrdinaryDensitySum B N -
            epsilon * singularNormalization N ≤ currentChenUpsilon5 N := by
  obtain ⟨B, hB, C, _hC, hBV⟩ := part3_currentLowerAPError_log_saving 3 (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro epsilon hepsilon
  have hlarge : ∀ᶠ N : ℕ in atTop,
      2 * C / (epsilon * twinPrimeConstant) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hBV, eventually_currentChenUpsilon5_ordinary_row_level B,
    eventually_one_le_nat_log, eventually_ge_atTop (4 : ℕ), hlarge,
    eventually_powerLog_le_singularNormalization (8 / (Real.log 2) ^ 3) (1 / 2) 3
      (by norm_num) (epsilon / 2) (half_pos hepsilon)]
    with N hBVN hlevels hlog hN4 hlargeN hcentrebudget
  intro hEven
  let Q : ℕ := chenInitialLevelCap B N
  let S : (ℕ × ℕ) → Finset ℕ := currentChenUpsilon5OrdinaryRows N Q
  have hQ : Q ≤ panModulusCutoff N B := by
    dsimp [Q, chenInitialLevelCap, panModulusCutoff]
    rw [Real.sqrt_eq_rpow]
  have hrows := currentChenUpsilon5OrdinaryRows_admissible N Q
  have hrawAP := hBVN Q hQ (fun _ => ∅) (fun _ => ∅) S (fun _ => ∅) hrows
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hlogprod : 2 * C ≤ Real.log (N : ℝ) * (epsilon * twinPrimeConstant) :=
    (div_le_iff₀ (mul_pos hepsilon twinPrimeConstant_pos)).mp hlargeN
  have hcoefficient : C / Real.log (N : ℝ) ≤
      (epsilon / 2) * twinPrimeConstant :=
    (div_le_iff₀ hlogpos).mpr (by nlinarith only [hlogprod])
  have hAPbudget : C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℕ) ≤
      (epsilon / 2) * singularNormalization N := by
    calc
      _ = (C / Real.log (N : ℝ)) *
          ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) := by
        field_simp [ne_of_gt hlogpos]
      _ ≤ ((epsilon / 2) * twinPrimeConstant) *
          ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hcoefficient (by positivity)
      _ = (epsilon / 2) *
          (twinPrimeConstant * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) := by ring
      _ ≤ (epsilon / 2) * singularNormalization N :=
        mul_le_mul_of_nonneg_left (singularNormalization_lower N) (half_pos hepsilon).le
  have hAP : part3CurrentLowerAPError N (fun _ => ∅) (fun _ => ∅) S (fun _ => ∅) ≤
      (epsilon / 2) * singularNormalization N := by
    rw [Real.rpow_ofNat] at hrawAP
    exact hrawAP.trans hAPbudget
  have hQsqrt : (Q : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hden : 1 ≤ Real.log (N : ℝ) ^ B := Real.one_le_rpow hlog hB
    dsimp [Q, chenInitialLevelCap]
    calc
      _ ≤ Real.sqrt (N : ℝ) / Real.log (N : ℝ) ^ B :=
        Nat.floor_le (div_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans hden))
      _ ≤ Real.sqrt (N : ℝ) := div_le_self (Real.sqrt_nonneg _) hden
  have hcentre : part3CurrentLowerCentreCost N (fun _ => ∅) (fun _ => ∅)
      S (fun _ => ∅) ≤ (epsilon / 2) * singularNormalization N :=
    (part3CurrentLowerCentreCost_le_sqrt_log_cube hEven hN4 hlog hQsqrt
      (fun _ => ∅) (fun _ => ∅) S (fun _ => ∅) hrows).trans hcentrebudget
  have hfinite := currentChenUpsilon5_ge_ordinary_density_sub_costs B N hlevels
  change currentChenUpsilon5OrdinaryDensitySum B N -
      part3CurrentLowerAPError N (fun _ => ∅) (fun _ => ∅) S (fun _ => ∅) -
      part3CurrentLowerCentreCost N (fun _ => ∅) (fun _ => ∅) S (fun _ => ∅) ≤ _ at hfinite
  linarith only [hfinite, hAP, hcentre]

end

end ImbalancedChen
