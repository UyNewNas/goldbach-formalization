import ImbalancedChen.ActualSmallRosserDensity
import ImbalancedChen.ChenInitialCorrectionBudget
import ImbalancedChen.Part3PrimeAPDistribution

/-!
# Actual lower Rosser weights on the Chen prime receiver source

These finite identities join the same small-prime Rosser coefficient used
by the proved density limit to the genuine initial Chen source. The AP
error is centred at the genuine logarithmic integral, and the centre-prime
count is retained separately with its signed coefficient. No estimate for
either signed sum is supplied by a premise.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open MathlibNt.SieveTheory.BombieriVinogradov

/-- The enumeration cap disappears once it covers the real cutoff. -/
theorem currentChen_actualSmallPrimeProduct_eq_sieveProduct
    (N cap : ℕ) (z : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallPrimeProduct N cap z = sieveProduct N (Nat.ceil z) := by
  have hs : actualSmallPrimeFinset N cap z = sievePrimes N (Nat.ceil z) := by
    ext p
    rw [mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap hzcap,
      mem_sievePrimes_chen_real_cap]
    tauto
  simp only [actualSmallPrimeProduct, sieveProduct, hs, id_eq]

/-- Exact Fubini on the genuine receiver set, without changing the
underlying source to a prime-product image or losing tuple multiplicity. -/
theorem currentChen_sum_supportedDivisorSum (N : ℕ) (S : Finset ℕ)
    (beta : ℕ → ℝ) :
    (∑ n ∈ chenPrimeReceiverSource N, supportedDivisorSum S beta n) =
      ∑ d ∈ S, beta d * (chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d) := by
  classical
  simp only [supportedDivisorSum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  calc
    (∑ n ∈ chenPrimeReceiverSource N, if d ∣ n then beta d else 0) =
        (((chenPrimeReceiverSource N).filter (fun n => d ∣ n)).card : ℝ) * beta d := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by
      rw [chenPrimeReceiverSource_divisibility_fibre_card,
        chenAdditivePrimeCarrier_AP_count]
      ring

/-- The pointwise lower sieve gives a true lower bound for the actual
sifted cardinality at this same real cutoff. -/
theorem currentChen_initial_actualRosser_lower
    (N cap : ℕ) (z L : ℝ) (hzcap : z ≤ (cap : ℝ))
    (hL : 1 < L) (hzL : z ≤ L) :
    (∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserMinus N cap z L d *
        (chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d)) ≤
      ((chenSiftedPrimeSource N z).card : ℝ) := by
  classical
  rw [← currentChen_sum_supportedDivisorSum]
  calc
    _ ≤ ∑ n ∈ chenPrimeReceiverSource N,
        if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n _
      have h := (actualSmallRosser_sandwich_nat N cap z L hL hzL n).1
      rw [currentChen_actualSmallPrimeProduct_eq_sieveProduct N cap z hzcap] at h
      simpa only [Nat.coprime_comm] using h
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [chenSiftedPrimeSource, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Exact decomposition into the proved density's actual coefficient,
the genuine prime-AP error, and the full signed centre-prime correction. -/
theorem currentChen_initial_actualRosser_main_and_errors (N cap : ℕ) (z L : ℝ) :
    (∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserMinus N cap z L d *
        (chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d)) =
      trueLogarithmicIntegral N * actualSmallRosserMinusDensity N cap z L +
        (∑ d ∈ actualSmallRosserSupport N cap z,
          actualSmallRosserMinus N cap z L d * part3PrimeAPError N N d) -
        ∑ d ∈ actualSmallRosserSupport N cap z,
          actualSmallRosserMinus N cap z L d * chenCentrePrimeAPCount N N d := by
  classical
  simp only [actualSmallRosserMinusDensity, reciprocalTotientDensity,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold part3PrimeAPError
  ring

/-- The real initial source receives the same density used in the
all-depth Rosser limit, with every actual signed error still visible. -/
theorem currentChen_initial_actualRosser_density_lower
    (N cap : ℕ) (z L : ℝ) (hzcap : z ≤ (cap : ℝ))
    (hL : 1 < L) (hzL : z ≤ L) :
    trueLogarithmicIntegral N * actualSmallRosserMinusDensity N cap z L +
        (∑ d ∈ actualSmallRosserSupport N cap z,
          actualSmallRosserMinus N cap z L d * part3PrimeAPError N N d) -
        (∑ d ∈ actualSmallRosserSupport N cap z,
          actualSmallRosserMinus N cap z L d * chenCentrePrimeAPCount N N d) ≤
      ((chenSiftedPrimeSource N z).card : ℝ) := by
  rw [← currentChen_initial_actualRosser_main_and_errors]
  exact currentChen_initial_actualRosser_lower N cap z L hzcap hL hzL

end

end ImbalancedChen
