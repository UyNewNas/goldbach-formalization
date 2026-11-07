import ImbalancedChen.CurrentChenSinglePrimeHarmonicMean
import ImbalancedChen.CurrentChenSinglePrimeUpperFiniteMean
import ImbalancedChen.CurrentChenTrueLiNormalization

/-!
# Actual ordinary upper means for the third and fourth Chen terms

The canonical factor, actual single-prime harmonic measure, exact rounded
Rosser coefficient, primitive AP supplier and full centre budget are all
proved suppliers. The true logarithmic integral is normalized using its
proved leading-one estimate. No density or harmonic limit is a premise.
These are ordinary upper means, not adopted causal manuscript constants.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

/-- The normalized same-coefficient sum has the actual canonical harmonic
integral as an upper mean, uniformly over every actual row in the band. -/
theorem eventually_currentChenSinglePrime_normalized_upper_density_sum
    (B U : ℝ) (hU : (417 / 5000 : ℝ) < U) (hUhi : U ≤ 1 / 3)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ U),
        (1 / (Nat.totient p : ℝ)) *
          (actualSmallRosserPlusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
            ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N p : ℝ) *
              Real.log (N : ℝ) / singularSeries N)) ≤
        currentChenSinglePrimeOrdinaryUpperIntegral U + epsilon := by
  obtain ⟨M, hM, hmass⟩ :=
    currentChenSinglePrime_reciprocalTotient_eventually_bounded U hU hUhi
  let T := fun N : ℕ => chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ U)
  let w := fun (_N : ℕ) (p : ℕ) => 1 / (Nat.totient p : ℝ)
  let f := fun N p => actualSmallRosserPlusDensity N
    (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ))) ((N : ℝ) ^ (417 / 5000 : ℝ))
    (chenQuotientRosserD B N p : ℝ) * Real.log (N : ℝ) / singularSeries N
  let g := fun N p => currentChenSinglePrimeOrdinaryUpperFactor
    (chenQuotientRosserT B (417 / 5000) N p)
  let delta : ℝ := epsilon / (2 * (M + 1))
  have hden : 0 < 2 * (M + 1) := by linarith
  have hdeltap : 0 < delta := div_pos hepsilon hden
  have hcost : delta * M ≤ epsilon / 2 := by
    have h := mul_le_mul_of_nonneg_left (show M ≤ M + 1 by linarith) hdeltap.le
    have hid : delta * (M + 1) = epsilon / 2 := by
      dsimp [delta]
      field_simp [show M + 1 ≠ 0 by linarith]
    linarith only [h, hid]
  have hnear : ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ T N, w N p * g N p) < currentChenSinglePrimeOrdinaryUpperIntegral U + epsilon / 2 :=
    (tendsto_currentChenSinglePrime_ordinary_moving_harmonic B U hU hUhi).eventually
      (Iio_mem_nhds (by linarith : currentChenSinglePrimeOrdinaryUpperIntegral U <
        currentChenSinglePrimeOrdinaryUpperIntegral U + epsilon / 2))
  filter_upwards [hmass, hnear,
    eventually_currentChen_singleUpperRosserDensity_upper B delta hdeltap,
    eventually_currentChenSinglePrime_row_interval B, eventually_ge_atTop (1 : ℕ)]
    with N hmassN hnearN hdensity hinterval hN
  intro hEven
  have hsubset := currentChenSinglePrime_selector_subset_Upsilon3 hN U hUhi
  have hsum : (∑ p ∈ T N, w N p * f N p) ≤
      (∑ p ∈ T N, w N p * g N p) + delta * (∑ p ∈ T N, w N p) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have h := mul_le_mul_of_nonneg_left
      (hdensity hEven p (hinterval p (hsubset hp)))
      (show 0 ≤ w N p by dsimp [w]; positivity)
    change w N p * f N p ≤ w N p * (g N p + delta) at h
    nlinarith only [h]
  have hmasscost := (mul_le_mul_of_nonneg_left hmassN hdeltap.le).trans hcost
  change (∑ p ∈ T N, w N p * f N p) ≤ currentChenSinglePrimeOrdinaryUpperIntegral U + epsilon
  linarith only [hsum, hmasscost, hnearN]

/-- The actual count has an ordinary upper mean. A negative raw density
sum is treated using nonnegativity of true li; it is never multiplied by
an upper li bound with the wrong sign. -/
theorem eventually_currentChenSinglePrime_le_ordinary_upper_mean
    (U : ℝ) (hU : (417 / 5000 : ℝ) < U) (hUhi : U ≤ 1 / 3)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ U),
        ((chenSiftedQuotientPrimeSource N p ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)) ≤
          (currentChenSinglePrimeOrdinaryUpperIntegral U + epsilon) * singularNormalization N := by
  obtain ⟨B, _hB, hpaid⟩ :=
    eventually_currentChenSinglePrime_subselector_le_upper_density_sum
  let I : ℝ := currentChenSinglePrimeOrdinaryUpperIntegral U
  have hI : 0 ≤ I := currentChenSinglePrimeOrdinaryUpperIntegral_nonneg U hU hUhi
  let delta : ℝ := min (1 / 2) (epsilon / (2 * (I + 3)))
  have hden : 0 < 2 * (I + 3) := by linarith
  have hdeltap : 0 < delta := lt_min (by norm_num) (div_pos hepsilon hden)
  have hdelta1 : delta ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hcost : delta * (I + 3) ≤ epsilon / 2 := by
    have h := (le_div_iff₀ hden).mp
      (show delta ≤ epsilon / (2 * (I + 3)) from min_le_right _ _)
    nlinarith only [h]
  have hdeltae : delta ≤ epsilon := by nlinarith only [hcost, hI, hdeltap, hepsilon]
  have htotal : (1 + delta) * (I + delta) + delta ≤ I + epsilon := by
    have hdeltasq := mul_le_mul_of_nonneg_left hdelta1 hdeltap.le
    nlinarith only [hcost, hdeltasq, hepsilon]
  filter_upwards [eventually_currentChenSinglePrime_normalized_upper_density_sum
      B U hU hUhi delta hdeltap, hpaid delta hdeltap,
    eventually_currentChen_trueLi_le delta hdeltap, eventually_ge_atTop (2 : ℕ)]
    with N hnear hfinite hli hN
  intro hEven
  let T := chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ U)
  have hsubset := currentChenSinglePrime_selector_subset_Upsilon3 (N := N) (by omega) U hUhi
  have hfiniteN := hfinite hEven T hsubset
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlogp := Real.log_pos hN1
  have hSSp := singularSeries_pos N
  have hH : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg hSSp.le hNp.le) (sq_nonneg _)
  let V : ℝ := ∑ p ∈ T,
    actualSmallRosserPlusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
      ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N p : ℝ) / (Nat.totient p : ℝ)
  have hvnorm : V * Real.log (N : ℝ) / singularSeries N ≤ I + delta := by
    have h := hnear hEven
    have heq : (∑ p ∈ T, (1 / (Nat.totient p : ℝ)) *
        (actualSmallRosserPlusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
          ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N p : ℝ) *
            Real.log (N : ℝ) / singularSeries N)) =
        V * Real.log (N : ℝ) / singularSeries N := by
      dsimp [V]
      rw [Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    rwa [heq] at h
  have hsum_eq : currentChenSinglePrimeUpperDensitySum B N T = trueLogarithmicIntegral N * V := by
    unfold currentChenSinglePrimeUpperDensitySum V
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hsum_eq] at hfiniteN
  by_cases hV : 0 ≤ V
  · have hmain : trueLogarithmicIntegral N * V ≤
        ((1 + delta) * (I + delta)) * singularNormalization N := by
      calc
        _ ≤ ((1 + delta) * (N : ℝ) / Real.log (N : ℝ)) * V :=
          mul_le_mul_of_nonneg_right hli hV
        _ = (1 + delta) * (V * Real.log (N : ℝ) / singularSeries N) *
            singularNormalization N := by
          unfold singularNormalization
          field_simp [hSSp.ne', hlogp.ne']
        _ ≤ ((1 + delta) * (I + delta)) * singularNormalization N :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hvnorm (by positivity)) hH
    have hbudget := mul_le_mul_of_nonneg_right htotal hH
    change (∑ p ∈ T, ((chenSiftedQuotientPrimeSource N p
      ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)) ≤ (I + epsilon) * singularNormalization N
    nlinarith only [hfiniteN, hmain, hbudget]
  · have hli0 : 0 ≤ trueLogarithmicIntegral N := by
      exact MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg
        (2 / Real.log 2) (by positivity) (by exact_mod_cast hN)
    have hmain : trueLogarithmicIntegral N * V ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hli0 (le_of_not_ge hV)
    have hbudget := mul_le_mul_of_nonneg_right
      (show delta ≤ I + epsilon by linarith only [hdeltae, hI]) hH
    change (∑ p ∈ T, ((chenSiftedQuotientPrimeSource N p
      ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)) ≤ (I + epsilon) * singularNormalization N
    linarith only [hfiniteN, hmain, hbudget]

/-- The two actual negatively signed ledger terms have the corresponding
ordinary canonical upper means, with their distinct strict prime bands. -/
theorem eventually_currentChenUpsilon3_Upsilon4_le_ordinary_upper_mean
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon3 N ≤
          (currentChenSinglePrimeOrdinaryUpperIntegral (1 / 3) + epsilon) * singularNormalization N ∧
        currentChenUpsilon4 N ≤
          (currentChenSinglePrimeOrdinaryUpperIntegral (59 / 250) + epsilon) * singularNormalization N := by
  filter_upwards [eventually_currentChenSinglePrime_le_ordinary_upper_mean
      (1 / 3) (by norm_num) le_rfl epsilon hepsilon,
    eventually_currentChenSinglePrime_le_ordinary_upper_mean
      (59 / 250) (by norm_num) (by norm_num) epsilon hepsilon] with N h3 h4
  intro hEven
  constructor
  · rw [currentChenUpsilon3_eq_siftedQuotientPrimeSource]
    exact h3 hEven
  · rw [currentChenUpsilon4_eq_siftedQuotientPrimeSource]
    exact h4 hEven

end

end ImbalancedChen