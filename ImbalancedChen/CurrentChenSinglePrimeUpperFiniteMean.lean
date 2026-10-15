import ImbalancedChen.CurrentChenQuotientUpperRosser
import ImbalancedChen.CurrentChenMeanLedger
import ImbalancedChen.Part3CurrentLowerDistribution

/-!
# Actual third and fourth counts with the ordinary upper remainder paid

The upper Rosser coefficient is evaluated on each actual one-prime row.
An arbitrary subset of the actual third band is estimated uniformly after
one common threshold. The true fourth band is then included by its actual
upper exponent, while retaining its own exact count and density sum.

Every signed AP term and the full centre cost are paid by proved ordinary
suppliers. The four-row interface is independent of the sign of the sieve:
its historical `Lower` name does not turn these upper count bounds into
lower bounds. There is no BV, pointwise sieve or analytic-density premise.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

/-- The same literal upper coefficient, with its actual quotient level. -/
def currentChenSinglePrimeUpperDensitySum (B : ℝ) (N : ℕ) (T : Finset ℕ) : ℝ :=
  ∑ p ∈ T,
    trueLogarithmicIntegral N / (Nat.totient p : ℝ) *
      actualSmallRosserPlusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
        ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N p : ℝ)

/-- An unselected row is empty; a selected row keeps all nonzero upper
coefficients of the original strict sieve product. -/
def currentChenSinglePrimeUpperRows (N Q : ℕ) (T : Finset ℕ) : ℕ → Finset ℕ :=
  fun p => if p ∈ T then currentChenQuotientUpperRosserActive N p
    (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ))) Q ((N : ℝ) ^ (417 / 5000 : ℝ)) else ∅

theorem currentChenSinglePrimeUpperRows_admissible (N Q : ℕ) (T : Finset ℕ) :
    Part3CurrentLowerRows N Q (currentChenSinglePrimeUpperRows N Q T)
      (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp d hd
    by_cases hT : p ∈ T
    · simp only [currentChenSinglePrimeUpperRows, if_pos hT] at hd
      exact Finset.mem_filter.mpr
        ⟨currentChenQuotientUpperRosserActive_divisor (Nat.le_ceil _) hd,
          currentChenQuotientUpperRosserActive_physical_cap
            (Nat.zero_lt_one.trans (chenSinglePrimeSelector_sieve_data hp).1) hd⟩
    · simp only [currentChenSinglePrimeUpperRows, if_neg hT, Finset.notMem_empty] at hd
  · intro p hp d hd
    simp at hd
  · intro t ht d hd
    simp at hd
  · intro t ht d hd
    simp at hd

/-- An exact sum over a genuine subselector, including its multiplicity. -/
theorem currentChenSinglePrimeUpperRows_sum (N Q : ℕ) (T : Finset ℕ)
    (hT : T ⊆ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) (F : ℕ → ℕ → ℝ) :
    (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)),
      ∑ d ∈ currentChenSinglePrimeUpperRows N Q T p, F p d) =
      ∑ p ∈ T, ∑ d ∈ currentChenQuotientUpperRosserActive N p
        (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ))) Q ((N : ℝ) ^ (417 / 5000 : ℝ)),
        F p d := by
  have hsub : (∑ p ∈ T, ∑ d ∈ currentChenSinglePrimeUpperRows N Q T p, F p d) =
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)),
        ∑ d ∈ currentChenSinglePrimeUpperRows N Q T p, F p d := by
    apply Finset.sum_subset hT
    intro p hp hnot
    simp only [currentChenSinglePrimeUpperRows, if_neg hnot, Finset.sum_empty]
  rw [← hsub]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [currentChenSinglePrimeUpperRows, if_pos hp]

theorem currentChenSinglePrimeUpperRows_APError_eq (N Q : ℕ) (T : Finset ℕ)
    (hT : T ⊆ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    part3CurrentLowerAPError N (currentChenSinglePrimeUpperRows N Q T)
      (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) =
      ∑ p ∈ T, ∑ d ∈ currentChenQuotientUpperRosserActive N p
        (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ))) Q ((N : ℝ) ^ (417 / 5000 : ℝ)),
        |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (p * d)| := by
  simpa only [part3CurrentLowerAPError, Finset.sum_empty, Finset.sum_const_zero,
    add_zero] using currentChenSinglePrimeUpperRows_sum N Q T hT
      (fun p d => |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (p * d)|)

theorem currentChenSinglePrimeUpperRows_CentreCost_eq (N Q : ℕ) (T : Finset ℕ)
    (hT : T ⊆ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    part3CurrentLowerCentreCost N (currentChenSinglePrimeUpperRows N Q T)
      (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) =
      ∑ p ∈ T, ∑ d ∈ currentChenQuotientUpperRosserActive N p
        (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ))) Q ((N : ℝ) ^ (417 / 5000 : ℝ)),
        chenQuotientCentreCost N p d := by
  simpa only [part3CurrentLowerCentreCost, chenSelectedCentreCost, id_eq,
    Finset.sum_empty, Finset.sum_const_zero, add_zero] using
      currentChenSinglePrimeUpperRows_sum N Q T hT
        (fun p d => chenQuotientCentreCost N p d)

/-- The entire actual third band has s>1 eventually, before selecting p. -/
theorem eventually_currentChenSinglePrime_upper_row_level (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈
      chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)),
      1 < (chenQuotientRosserD B N p : ℝ) ∧
        (N : ℝ) ^ (417 / 5000 : ℝ) ≤ (chenQuotientRosserD B N p : ℝ) := by
  filter_upwards [eventually_chenQuotientRosserT_gt B (1 / 3) (417 / 5000) 1
    (by norm_num) (by norm_num) (by norm_num), eventually_ge_atTop (2 : ℕ)]
    with N hrows hN
  intro p hp
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hs := hrows p (Nat.zero_lt_one.trans (chenSinglePrimeSelector_sieve_data hp).1)
    (Finset.mem_filter.mp hp).2.2.le
  have hz := Real.one_lt_rpow hN1 (by norm_num : (0 : ℝ) < 417 / 5000)
  have hDp : (0 : ℝ) < chenQuotientRosserD B N p := by
    unfold chenQuotientRosserD chenQuotientRowLevel
    positivity
  have hratio : (1 : ℝ) < Real.log (chenQuotientRosserD B N p : ℝ) /
      Real.log ((N : ℝ) ^ (417 / 5000 : ℝ)) := hs
  have hlog := (lt_div_iff₀ (Real.log_pos hz)).mp hratio
  have hlt : (N : ℝ) ^ (417 / 5000 : ℝ) < (chenQuotientRosserD B N p : ℝ) :=
    (Real.log_lt_log_iff (zero_lt_one.trans hz) hDp).mp
      (by simpa only [one_mul] using hlog)
  exact ⟨hz.trans hlt, hlt.le⟩

/-- A finite actual upper count estimate, with every absolute cost shown. -/
theorem currentChenSinglePrime_le_upper_density_add_costs
    (B : ℝ) (N : ℕ) (T : Finset ℕ)
    (hT : T ⊆ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)))
    (hlevels : ∀ p ∈ T,
      1 < (chenQuotientRosserD B N p : ℝ) ∧
        (N : ℝ) ^ (417 / 5000 : ℝ) ≤ (chenQuotientRosserD B N p : ℝ)) :
    (∑ p ∈ T, ((chenSiftedQuotientPrimeSource N p
        ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)) ≤
      currentChenSinglePrimeUpperDensitySum B N T +
        part3CurrentLowerAPError N
          (currentChenSinglePrimeUpperRows N (chenInitialLevelCap B N) T)
          (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) +
        part3CurrentLowerCentreCost N
          (currentChenSinglePrimeUpperRows N (chenInitialLevelCap B N) T)
          (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) := by
  let z : ℝ := (N : ℝ) ^ (417 / 5000 : ℝ)
  let cap : ℕ := Nat.ceil z
  let Q : ℕ := chenInitialLevelCap B N
  have hrow (p : ℕ) (hp : p ∈ T) :
      ((chenSiftedQuotientPrimeSource N p z).card : ℝ) ≤
        trueLogarithmicIntegral N / (Nat.totient p : ℝ) *
            actualSmallRosserPlusDensity N cap z (chenQuotientRowLevel Q p : ℝ) +
          (∑ d ∈ currentChenQuotientUpperRosserActive N p cap Q z,
            |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (p * d)|) +
          ∑ d ∈ currentChenQuotientUpperRosserActive N p cap Q z,
            chenQuotientCentreCost N p d := by
    have h := currentChen_quotient_actualRosser_density_upper N p cap z
      (chenQuotientRowLevel Q p) (Nat.le_ceil z)
      (chenSinglePrimeSelector_sieve_data (hT hp)).2.2
      (hlevels p hp).1 (hlevels p hp).2
    rw [currentChen_quotientUpperRosser_sum_eq_active,
      currentChen_quotientUpperRosser_sum_eq_active] at h
    have hAP :
        (∑ d ∈ currentChenQuotientUpperRosserActive N p cap Q z,
          actualSmallRosserPlus N cap z (chenQuotientRowLevel Q p : ℝ) d *
            chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (p * d)) ≤
          ∑ d ∈ currentChenQuotientUpperRosserActive N p cap Q z,
            |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (p * d)| := by
      apply Finset.sum_le_sum
      intro d hd
      have habs := mul_le_mul_of_nonneg_right
        (actualSmallRosserPlus_abs_le_one N cap z (chenQuotientRowLevel Q p) d)
        (abs_nonneg (chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (p * d)))
      rw [← abs_mul, one_mul] at habs
      exact (le_abs_self _).trans habs
    have hcentre :
        -(∑ d ∈ currentChenQuotientUpperRosserActive N p cap Q z,
          actualSmallRosserPlus N cap z (chenQuotientRowLevel Q p : ℝ) d *
            chenCentrePrimeAPCount N N (p * d)) ≤
          ∑ d ∈ currentChenQuotientUpperRosserActive N p cap Q z,
            chenQuotientCentreCost N p d := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro d hd
      have hc0 := chenCentrePrimeAPCount_nonneg N N (p * d)
      have hb := (neg_le_abs
        (actualSmallRosserPlus N cap z (chenQuotientRowLevel Q p) d)).trans
          (actualSmallRosserPlus_abs_le_one N cap z (chenQuotientRowLevel Q p) d)
      have hm := mul_le_mul_of_nonneg_right hb hc0
      simp only [neg_mul, one_mul] at hm
      have hc : chenCentrePrimeAPCount N N (p * d) ≤ chenQuotientCentreCost N p d := by
        unfold chenQuotientCentreCost
        exact le_add_of_nonneg_left
          (div_nonneg (chenCentrePrimeAPCount_nonneg N N p) (Nat.cast_nonneg _))
      exact hm.trans hc
    linarith only [h, hAP, hcentre]
  have hsum := Finset.sum_le_sum hrow
  rw [currentChenSinglePrimeUpperRows_APError_eq N Q T hT,
    currentChenSinglePrimeUpperRows_CentreCost_eq N Q T hT]
  simpa only [currentChenSinglePrimeUpperDensitySum, Finset.sum_add_distrib,
    chenQuotientRosserD, Q, cap, z] using hsum

/-- One genuine ordinary BV constant precedes epsilon. Its common N
threshold precedes every actual subselector T, and all centre costs are paid. -/
theorem eventually_currentChenSinglePrime_subselector_le_upper_density_sum :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N → ∀ T : Finset ℕ,
        T ⊆ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)) →
        (∑ p ∈ T, ((chenSiftedQuotientPrimeSource N p
          ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)) ≤
          currentChenSinglePrimeUpperDensitySum B N T +
            epsilon * singularNormalization N := by
  obtain ⟨B, hB, C, _hC, hBV⟩ := part3_currentLowerAPError_log_saving 3 (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro epsilon hepsilon
  have hlarge : ∀ᶠ N : ℕ in atTop,
      2 * C / (epsilon * twinPrimeConstant) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hBV, eventually_currentChenSinglePrime_upper_row_level B,
    eventually_one_le_nat_log, eventually_ge_atTop (4 : ℕ), hlarge,
    eventually_powerLog_le_singularNormalization (8 / (Real.log 2) ^ 3) (1 / 2) 3
      (by norm_num) (epsilon / 2) (half_pos hepsilon)]
    with N hBVN hlevels hlog hN4 hlargeN hcentrebudget
  intro hEven T hT
  let Q : ℕ := chenInitialLevelCap B N
  let S : ℕ → Finset ℕ := currentChenSinglePrimeUpperRows N Q T
  have hQ : Q ≤ panModulusCutoff N B := by
    dsimp [Q, chenInitialLevelCap, panModulusCutoff]
    rw [Real.sqrt_eq_rpow]
  have hrows := currentChenSinglePrimeUpperRows_admissible N Q T
  have hrawAP := hBVN Q hQ S (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) hrows
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hlogprod : 2 * C ≤ Real.log (N : ℝ) * (epsilon * twinPrimeConstant) :=
    (div_le_iff₀ (mul_pos hepsilon twinPrimeConstant_pos)).mp hlargeN
  have hcoefficient : C / Real.log (N : ℝ) ≤ (epsilon / 2) * twinPrimeConstant :=
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
  have hAP : part3CurrentLowerAPError N S (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) ≤
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
  have hcentre : part3CurrentLowerCentreCost N S (fun _ => ∅) (fun _ => ∅)
      (fun _ => ∅) ≤ (epsilon / 2) * singularNormalization N :=
    (part3CurrentLowerCentreCost_le_sqrt_log_cube hEven hN4 hlog hQsqrt
      S (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) hrows).trans hcentrebudget
  have hfinite := currentChenSinglePrime_le_upper_density_add_costs B N T hT
    (fun p hp => hlevels p (hT hp))
  change _ ≤ currentChenSinglePrimeUpperDensitySum B N T +
      part3CurrentLowerAPError N S (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) +
      part3CurrentLowerCentreCost N S (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) at hfinite
  linarith only [hfinite, hAP, hcentre]

/-- The fourth band is a genuine subset of the third band for N>=1.
Its own strict upper endpoint is preserved throughout the specialization. -/
theorem currentChenUpsilon4_selector_subset_Upsilon3 {N : ℕ} (hN : 1 ≤ N) :
    chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (59 / 250 : ℝ)) ⊆
      chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  intro p hp
  obtain ⟨hc, hlo, hhi⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hc, hlo,
    hhi.trans_le (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN : (1 : ℝ) ≤ N) (by norm_num))⟩

/-- The actual third-row density sum, before identifying its limiting integral. -/
def currentChenUpsilon3OrdinaryUpperDensitySum (B : ℝ) (N : ℕ) : ℝ :=
  currentChenSinglePrimeUpperDensitySum B N
    (chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)))

/-- The actual fourth-row density sum with its distinct original band. -/
def currentChenUpsilon4OrdinaryUpperDensitySum (B : ℝ) (N : ℕ) : ℝ :=
  currentChenSinglePrimeUpperDensitySum B N
    (chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)))

/-- Both negatively signed ledger entries receive true upper count bounds
from the same ordinary BV constant and the same threshold. -/
theorem eventually_currentChenUpsilon3_Upsilon4_le_ordinary_upper_density_sum :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N →
        currentChenUpsilon3 N ≤ currentChenUpsilon3OrdinaryUpperDensitySum B N +
            epsilon * singularNormalization N ∧
          currentChenUpsilon4 N ≤ currentChenUpsilon4OrdinaryUpperDensitySum B N +
            epsilon * singularNormalization N := by
  obtain ⟨B, hB, hpaid⟩ :=
    eventually_currentChenSinglePrime_subselector_le_upper_density_sum
  refine ⟨B, hB, ?_⟩
  intro epsilon hepsilon
  filter_upwards [hpaid epsilon hepsilon, eventually_ge_atTop (1 : ℕ)] with N hpaidN hN
  intro hEven
  constructor
  · rw [currentChenUpsilon3_eq_siftedQuotientPrimeSource]
    exact hpaidN hEven _ (fun _ hp => hp)
  · rw [currentChenUpsilon4_eq_siftedQuotientPrimeSource]
    exact hpaidN hEven _ (currentChenUpsilon4_selector_subset_Upsilon3 hN)

end

end ImbalancedChen
