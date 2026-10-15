import ImbalancedChen.ActualSmallRosserDensity
import ImbalancedChen.ChenInitialPrimeSource
import ImbalancedChen.FiniteSieveEuler
import MathlibNt.SieveTheory.Switching.SuzukiPrimeSums
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

/-!
# The actual Rosser density on the actual initial Chen sieve

The real prime cap and the natural ceiling level are preserved exactly.
The constructor is the genuine prime-receiver `chenInitialBoundingSieve`;
its source, weights and total mass are unchanged. Only the common prime
product and reciprocal-totient local density enter these finite identities.

The local dimension-one constant is supplied by the proved Mertens inverse
interval theorem for the actual odd prime carrier. No B8 switched source,
distribution estimate, or analytic density assumption is introduced.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple

theorem currentChen_model_primeFinset_eq_sievePrimes
    (N cap : ℕ) (z : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallPrimeFinset N cap z = sievePrimes N (Nat.ceil z) := by
  ext p
  rw [mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap hzcap,
    mem_sievePrimes_chen_real_cap]
  tauto

theorem currentChen_model_actualProduct_eq_sieveProduct
    (N cap : ℕ) (z : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallPrimeProduct N cap z = sieveProduct N (Nat.ceil z) := by
  unfold actualSmallPrimeProduct sieveProduct
  rw [currentChen_model_primeFinset_eq_sievePrimes N cap z hzcap]
  rfl

theorem currentChen_model_primeFactors (N : ℕ) (z : ℝ) (hEven : Even N) :
    (chenInitialBoundingSieve N z hEven).prodPrimes.primeFactors =
      sievePrimes N (Nat.ceil z) := by
  change (∏ p ∈ sievePrimes N (Nat.ceil z), p).primeFactors = _
  exact Nat.primeFactors_prod (fun p hp => (mem_sievePrimes.mp hp).2.1)

theorem currentChen_model_actualEuler_eq_finite
    (N cap : ℕ) (z : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallEulerProduct N cap z = finiteSieveDensity N (Nat.ceil z) := by
  unfold actualSmallEulerProduct finiteSieveDensity
  rw [currentChen_model_primeFinset_eq_sievePrimes N cap z hzcap]

theorem currentChen_model_actualEuler_pos (N cap : ℕ) (z : ℝ) (hEven : Even N) :
    0 < actualSmallEulerProduct N cap z := by
  unfold actualSmallEulerProduct
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) < p := by
    exact_mod_cast (actualSmallPrimeFinset_odd_of_even hEven hp).2
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))

theorem currentChen_model_minus_natCeil
    (N cap : ℕ) (z L : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallRosserMinus N cap z L =
      LinearSieve.lowerRosserWeight (sieveProduct N (Nat.ceil z)) (Nat.ceil L) := by
  unfold actualSmallRosserMinus ActualSmallRosserProvider.lowerWeight
  rw [LiLiuPrereqWF.SmallRosser.lowerWeight_eq_producer,
    currentChen_model_actualProduct_eq_sieveProduct N cap z hzcap]

/-- The main sum is exactly the same lower coefficient at `ceil L`,
including integer L; no floor-plus-one surrogate occurs. -/
theorem currentChen_model_minusDensity_eq_mainSum
    (N cap : ℕ) (z L : ℝ) (hEven : Even N) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallRosserMinusDensity N cap z L =
      (chenInitialBoundingSieve N z hEven).mainSum
        (LinearSieve.lowerRosserWeight
          (chenInitialBoundingSieve N z hEven).prodPrimes (Nat.ceil L)) := by
  unfold actualSmallRosserMinusDensity reciprocalTotientDensity BoundingSieve.mainSum
  rw [currentChen_model_minus_natCeil N cap z L hzcap]
  have hs : actualSmallRosserSupport N cap z =
      (chenInitialBoundingSieve N z hEven).prodPrimes.divisors := by
    change (actualSmallPrimeProduct N cap z).divisors =
      (sieveProduct N (Nat.ceil z)).divisors
    rw [currentChen_model_actualProduct_eq_sieveProduct N cap z hzcap]
  rw [hs]
  apply Finset.sum_congr rfl
  intro d hd
  change LinearSieve.lowerRosserWeight (sieveProduct N (Nat.ceil z)) (Nat.ceil L) d /
      (Nat.totient d : ℝ) =
    LinearSieve.lowerRosserWeight (sieveProduct N (Nat.ceil z)) (Nat.ceil L) d *
      (1 / (Nat.totient d : ℝ))
  ring

theorem currentChen_model_actualEuler_eq_sieveEuler
    (N cap : ℕ) (z : ℝ) (hEven : Even N) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallEulerProduct N cap z =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (chenInitialBoundingSieve N z hEven) := by
  rw [currentChen_model_actualEuler_eq_finite N cap z hzcap]
  unfold finiteSieveDensity AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
  rw [currentChen_model_primeFactors N z hEven]
  apply Finset.prod_congr rfl
  intro p hp
  rw [chenInitialBoundingSieve_prime_density N z hEven (mem_sievePrimes.mp hp).2.1]

/-- One proved Mertens constant works for every target and real cutoff.
Evenness removes prime two before the inverse local product is evaluated. -/
theorem exists_currentChen_model_dimensionOneLocalProductBound :
    ∃ K : ℝ, 1 < K ∧ ∀ (N : ℕ) (hEven : Even N) (z : ℝ),
      HasDimensionOneLocalProductBound (chenInitialBoundingSieve N z hEven) K := by
  obtain ⟨K, hK, hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N hEven z z1 z2 hz1 hz12
  let t := (chenInitialBoundingSieve N z hEven).prodPrimes.primeFactors.filter
    (fun p : ℕ => z1 ≤ (p : ℝ) ∧ (p : ℝ) < z2)
  have ht : ∀ p ∈ t, Nat.Prime p ∧ 2 < p := by
    intro p hp
    have hpf := (Finset.mem_filter.mp hp).1
    have hprime := Nat.prime_of_mem_primeFactors hpf
    have hd : p ∣ sieveProduct N (Nat.ceil z) :=
      (Nat.mem_primeFactors_of_ne_zero
        (chenInitialBoundingSieve N z hEven).prodPrimes_ne_zero).mp hpf |>.2
    exact ⟨hprime, two_lt_prime_of_dvd_sieveProduct hEven hprime hd⟩
  have hbound := hinterval t ht z1 z2 hz1 hz12
    (fun p hp => (Finset.mem_filter.mp hp).2)
  change (∏ p ∈ t, (1 - (chenInitialBoundingSieve N z hEven).nu p)⁻¹) ≤ _
  calc
    _ = ∏ p ∈ t, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [chenInitialBoundingSieve_prime_density N z hEven (ht p hp).1]
    _ ≤ _ := hbound

end

end ImbalancedChen
