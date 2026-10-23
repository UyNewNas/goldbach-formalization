import ImbalancedChen.CurrentChenPairRosser
import ImbalancedChen.CurrentChenUpsilon6OrdinarySource
import ImbalancedChen.Part3CurrentLowerDistribution

/-!
# Actual sixth-row counts with the ordinary remainder paid

Every subset of the actual sixth pair selector is supported by one proved
ordinary BV bound and the full centre budget. The row coefficient retains
its exact natural level, reciprocal-totient density and physical modulus.
The finite estimate does not need a positive product buffer; that buffer
is needed later for a nonzero analytic lower factor, where s must exceed 2.
No distribution, pointwise sieve or analytic lower estimate is assumed.
Executed verification status is recorded in the continuation progress report.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

/-- The same literal coefficient on any actual sixth-row subselector. -/
def currentChenUpsilon6OrdinaryDensitySum (B : ℝ) (N : ℕ)
    (T : Finset (ℕ × ℕ)) : ℝ :=
  ∑ t ∈ T,
    trueLogarithmicIntegral N / (Nat.totient (t.1 * t.2) : ℝ) *
      actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
        ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N (t.1 * t.2) : ℝ)

/-- A discarded pair contributes an empty row; retained pairs keep all
and only the nonzero actual Rosser coefficients. -/
def currentChenUpsilon6OrdinaryRows (N Q : ℕ) (T : Finset (ℕ × ℕ)) :
    (ℕ × ℕ) → Finset ℕ :=
  fun t => if t ∈ T then currentChenQuotientRosserActive N (t.1 * t.2)
    (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ))) Q ((N : ℝ) ^ (417 / 5000 : ℝ)) else ∅

theorem currentChenUpsilon6OrdinaryRows_admissible (N Q : ℕ)
    (T : Finset (ℕ × ℕ)) :
    Part3CurrentLowerRows N Q (fun _ => ∅) (fun _ => ∅)
      (fun _ => ∅) (currentChenUpsilon6OrdinaryRows N Q T) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht d hd
    simp at hd
  · intro t ht d hd
    simp at hd
  · intro t ht d hd
    simp at hd
  · intro t ht d hd
    by_cases hT : t ∈ T
    · simp only [currentChenUpsilon6OrdinaryRows, if_pos hT] at hd
      exact Finset.mem_filter.mpr
        ⟨currentChenQuotientRosserActive_divisor (Nat.le_ceil _) hd,
          currentChenQuotientRosserActive_physical_cap
            (Nat.zero_lt_one.trans (chenY6PrimeSelector_sieve_data ht).1) hd⟩
    · simp only [currentChenUpsilon6OrdinaryRows, if_neg hT, Finset.notMem_empty] at hd

/-- Masking by a genuine subselector is an exact finite summation identity. -/
theorem currentChenUpsilon6OrdinaryRows_sum (N Q : ℕ) (T : Finset (ℕ × ℕ))
    (hT : T ⊆ chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)))
    (F : (ℕ × ℕ) → ℕ → ℝ) :
    (∑ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)),
      ∑ d ∈ currentChenUpsilon6OrdinaryRows N Q T t, F t d) =
      ∑ t ∈ T, ∑ d ∈ currentChenQuotientRosserActive N (t.1 * t.2)
        (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ))) Q ((N : ℝ) ^ (417 / 5000 : ℝ)),
        F t d := by
  have hsub : (∑ t ∈ T, ∑ d ∈ currentChenUpsilon6OrdinaryRows N Q T t, F t d) =
      ∑ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)),
        ∑ d ∈ currentChenUpsilon6OrdinaryRows N Q T t, F t d := by
    apply Finset.sum_subset hT
    intro t ht hnot
    simp only [currentChenUpsilon6OrdinaryRows, if_neg hnot, Finset.sum_empty]
  rw [← hsub]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [currentChenUpsilon6OrdinaryRows, if_pos ht]

theorem currentChenUpsilon6OrdinaryRows_APError_eq (N Q : ℕ)
    (T : Finset (ℕ × ℕ))
    (hT : T ⊆ chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))) :
    part3CurrentLowerAPError N (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)
      (currentChenUpsilon6OrdinaryRows N Q T) =
      ∑ t ∈ T, ∑ d ∈ currentChenQuotientRosserActive N (t.1 * t.2)
        (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ))) Q ((N : ℝ) ^ (417 / 5000 : ℝ)),
        |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) ((t.1 * t.2) * d)| := by
  simpa only [part3CurrentLowerAPError, Finset.sum_empty, Finset.sum_const_zero,
    zero_add] using currentChenUpsilon6OrdinaryRows_sum N Q T hT
      (fun t d => |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) ((t.1 * t.2) * d)|)

theorem currentChenUpsilon6OrdinaryRows_CentreCost_eq (N Q : ℕ)
    (T : Finset (ℕ × ℕ))
    (hT : T ⊆ chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))) :
    part3CurrentLowerCentreCost N (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)
      (currentChenUpsilon6OrdinaryRows N Q T) =
      ∑ t ∈ T, ∑ d ∈ currentChenQuotientRosserActive N (t.1 * t.2)
        (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ))) Q ((N : ℝ) ^ (417 / 5000 : ℝ)),
        chenQuotientCentreCost N (t.1 * t.2) d := by
  simpa only [part3CurrentLowerCentreCost, chenSelectedCentreCost, Finset.sum_empty,
    Finset.sum_const_zero, zero_add] using currentChenUpsilon6OrdinaryRows_sum N Q T hT
      (fun t d => chenQuotientCentreCost N (t.1 * t.2) d)

/-- The actual sixth row already has s>1, which is sufficient for the finite
Rosser inequality. No uncorrected positive analytic factor is asserted. -/
theorem eventually_currentChenUpsilon6_ordinary_row_level (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈
      chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)),
      1 < (chenQuotientRosserD B N (t.1 * t.2) : ℝ) ∧
        (N : ℝ) ^ (417 / 5000 : ℝ) ≤
          (chenQuotientRosserD B N (t.1 * t.2) : ℝ) := by
  filter_upwards [eventually_currentChenUpsilon6_row_interval B,
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

/-- The actual same-coefficient finite count inequality on a genuine subset. -/
theorem currentChenUpsilon6_ge_ordinary_density_sub_costs
    (B : ℝ) (N : ℕ) (T : Finset (ℕ × ℕ))
    (hT : T ⊆ chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)))
    (hlevels : ∀ t ∈ T,
      1 < (chenQuotientRosserD B N (t.1 * t.2) : ℝ) ∧
        (N : ℝ) ^ (417 / 5000 : ℝ) ≤
          (chenQuotientRosserD B N (t.1 * t.2) : ℝ)) :
    currentChenUpsilon6OrdinaryDensitySum B N T -
        part3CurrentLowerAPError N (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)
          (currentChenUpsilon6OrdinaryRows N (chenInitialLevelCap B N) T) -
        part3CurrentLowerCentreCost N (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)
          (currentChenUpsilon6OrdinaryRows N (chenInitialLevelCap B N) T) ≤
      ∑ t ∈ T, ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
        ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ) := by
  let z : ℝ := (N : ℝ) ^ (417 / 5000 : ℝ)
  let cap : ℕ := Nat.ceil z
  let Q : ℕ := chenInitialLevelCap B N
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
      (chenY6PrimeSelector_sieve_data (hT ht)).2.2 (hlevels t ht).1 (hlevels t ht).2
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
  rw [currentChenUpsilon6OrdinaryRows_APError_eq N Q T hT,
    currentChenUpsilon6OrdinaryRows_CentreCost_eq N Q T hT]
  simpa only [currentChenUpsilon6OrdinaryDensitySum, Finset.sum_sub_distrib,
    chenQuotientRosserD, Q, cap, z] using hsum

/-- The ordinary BV constant and common threshold precede every choice of
actual sixth-row subset. All physical row and complete centre costs are paid. -/
theorem eventually_currentChenUpsilon6_subselector_ge_ordinary_density_sum :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N → ∀ T : Finset (ℕ × ℕ),
        T ⊆ chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)) →
        currentChenUpsilon6OrdinaryDensitySum B N T - epsilon * singularNormalization N ≤
          ∑ t ∈ T, ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
            ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ) := by
  obtain ⟨B, hB, C, _hC, hBV⟩ := part3_currentLowerAPError_log_saving 3 (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro epsilon hepsilon
  have hlarge : ∀ᶠ N : ℕ in atTop,
      2 * C / (epsilon * twinPrimeConstant) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hBV, eventually_currentChenUpsilon6_ordinary_row_level B,
    eventually_one_le_nat_log, eventually_ge_atTop (4 : ℕ), hlarge,
    eventually_powerLog_le_singularNormalization (8 / (Real.log 2) ^ 3) (1 / 2) 3
      (by norm_num) (epsilon / 2) (half_pos hepsilon)]
    with N hBVN hlevels hlog hN4 hlargeN hcentrebudget
  intro hEven T hT
  let Q : ℕ := chenInitialLevelCap B N
  let S : (ℕ × ℕ) → Finset ℕ := currentChenUpsilon6OrdinaryRows N Q T
  have hQ : Q ≤ panModulusCutoff N B := by
    dsimp [Q, chenInitialLevelCap, panModulusCutoff]
    rw [Real.sqrt_eq_rpow]
  have hrows := currentChenUpsilon6OrdinaryRows_admissible N Q T
  have hrawAP := hBVN Q hQ (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) S hrows
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
  have hAP : part3CurrentLowerAPError N (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) S ≤
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
      (fun _ => ∅) S ≤ (epsilon / 2) * singularNormalization N :=
    (part3CurrentLowerCentreCost_le_sqrt_log_cube hEven hN4 hlog hQsqrt
      (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) S hrows).trans hcentrebudget
  have hfinite := currentChenUpsilon6_ge_ordinary_density_sub_costs B N T hT
    (fun t ht => hlevels t (hT ht))
  change currentChenUpsilon6OrdinaryDensitySum B N T -
      part3CurrentLowerAPError N (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) S -
      part3CurrentLowerCentreCost N (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) S ≤ _ at hfinite
  linarith only [hfinite, hAP, hcentre]

/-- In particular, every fixed strict buffered selector has a real-count
lower bound from the same ordinary BV supplier, before any integral limit. -/
theorem eventually_currentChenUpsilon6Ordinary_ge_density_sum :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ eta epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N →
        currentChenUpsilon6OrdinaryDensitySum B N
            (currentChenUpsilon6OrdinarySelector N eta) -
          epsilon * singularNormalization N ≤ currentChenUpsilon6OrdinaryCount N eta := by
  obtain ⟨B, hB, hpaid⟩ :=
    eventually_currentChenUpsilon6_subselector_ge_ordinary_density_sum
  refine ⟨B, hB, ?_⟩
  intro eta epsilon hepsilon
  filter_upwards [hpaid epsilon hepsilon] with N hN
  intro hEven
  exact hN hEven (currentChenUpsilon6OrdinarySelector N eta)
    (currentChenUpsilon6OrdinarySelector_subset_original N eta)

end

end ImbalancedChen