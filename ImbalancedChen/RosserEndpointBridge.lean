import ImbalancedChen.ActualSmallRosserDensity
import MathlibNt.SieveTheory.LiLiuGoldbachB8FibreSieve

/-!
# Exact endpoint dictionary for the actual Rosser coefficients

The finite prime carrier, both coefficient functions, their reciprocal-totient
densities, and the Euler product agree literally with the fixed dependency's
Goldbach bounding sieve. The real strict level `R` is represented by `⌈R⌉₊`.
In particular it is not replaced by `Nat.floor R + 1`: these natural levels
differ when `R` is a nonnegative integer.

These are finite identities, valid without a lower bound on `R` or `y`.
Evenness of the target is used only where the actual Goldbach bounding sieve
is constructed. No density asymptotic or eighth-rank saving is asserted.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Once the enumeration cap covers the real cutoff, both libraries use
exactly the same primes `p < y`, with primes dividing `N` removed. -/
theorem actualSmallPrimeFinset_eq_goldbachB10SiftingPrimes
    (N cap : ℕ) (y : ℝ) (hycap : y ≤ (cap : ℝ)) :
    actualSmallPrimeFinset N cap y = goldbachB10SiftingPrimes N y := by
  ext p
  rw [mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap hycap,
    mem_goldbachB10SiftingPrimes_iff, Nat.lt_ceil]
  tauto

theorem actualSmallPrimeProduct_eq_goldbachB10ProdPrimes
    (N cap : ℕ) (y : ℝ) (hycap : y ≤ (cap : ℝ)) :
    actualSmallPrimeProduct N cap y = goldbachB10ProdPrimes N y := by
  unfold actualSmallPrimeProduct goldbachB10ProdPrimes
  rw [actualSmallPrimeFinset_eq_goldbachB10SiftingPrimes N cap y hycap]

theorem actualSmallRosserSupport_eq_goldbachB10_divisors
    (N cap : ℕ) (y : ℝ) (hycap : y ≤ (cap : ℝ)) :
    actualSmallRosserSupport N cap y = (goldbachB10ProdPrimes N y).divisors := by
  unfold actualSmallRosserSupport
  rw [actualSmallPrimeProduct_eq_goldbachB10ProdPrimes N cap y hycap]

/-- Literal equality of all lower coefficients at the strict real level.
The bridge applies to integer levels as well as noninteger levels. -/
theorem actualSmallRosserMinus_eq_lowerRosserWeight_natCeil
    (N cap : ℕ) (y R : ℝ) (hycap : y ≤ (cap : ℝ)) :
    actualSmallRosserMinus N cap y R =
      LinearSieve.lowerRosserWeight (goldbachB10ProdPrimes N y) ⌈R⌉₊ := by
  unfold actualSmallRosserMinus ActualSmallRosserProvider.lowerWeight
  rw [LiLiuPrereqWF.SmallRosser.lowerWeight_eq_producer,
    actualSmallPrimeProduct_eq_goldbachB10ProdPrimes N cap y hycap]

/-- Literal equality of all upper coefficients, retaining the strict cubic
tests at an integer level instead of changing them to non-strict tests. -/
theorem actualSmallRosserPlus_eq_upperRosserWeight_natCeil
    (N cap : ℕ) (y R : ℝ) (hycap : y ≤ (cap : ℝ)) :
    actualSmallRosserPlus N cap y R =
      LinearSieve.upperRosserWeight (goldbachB10ProdPrimes N y) ⌈R⌉₊ := by
  unfold actualSmallRosserPlus ActualSmallRosserProvider.upperWeight
  rw [LiLiuPrereqWF.SmallRosser.upperWeight_eq_producer,
    actualSmallPrimeProduct_eq_goldbachB10ProdPrimes N cap y hycap]

/-- A dictionary for every coefficient on this common displayed support.
The unrelated output weights of the B8 sieve do not enter its main sum. -/
theorem reciprocalTotientDensity_actualSmallSupport_eq_b8_mainSum
    (N cap : ℕ) (hEven : Even N) (y : ℝ) (hycap : y ≤ (cap : ℝ))
    (beta : ℕ → ℝ) :
    reciprocalTotientDensity (actualSmallRosserSupport N cap y) beta =
      (goldbachB8PlusBoundingSieve N hEven y).mainSum beta := by
  unfold reciprocalTotientDensity BoundingSieve.mainSum
  rw [actualSmallRosserSupport_eq_goldbachB10_divisors N cap y hycap]
  change (∑ d ∈ (goldbachB10ProdPrimes N y).divisors,
      beta d / (Nat.totient d : ℝ)) =
    ∑ d ∈ (goldbachB10ProdPrimes N y).divisors,
      beta d * (goldbachB8PlusBoundingSieve N hEven y).nu d
  apply Finset.sum_congr rfl
  intro d _hd
  rw [goldbachB8PlusBoundingSieve_nu_eq_inv_totient]
  ring

/-- The actual lower density is the main sum of the very same lower
Rosser coefficient at `⌈R⌉₊`. No sieve-density inequality is assumed. -/
theorem actualSmallRosserMinusDensity_eq_b8_mainSum_natCeil
    (N cap : ℕ) (hEven : Even N) (y R : ℝ) (hycap : y ≤ (cap : ℝ)) :
    actualSmallRosserMinusDensity N cap y R =
      (goldbachB8PlusBoundingSieve N hEven y).mainSum
        (LinearSieve.lowerRosserWeight
          (goldbachB8PlusBoundingSieve N hEven y).prodPrimes ⌈R⌉₊) := by
  unfold actualSmallRosserMinusDensity
  rw [reciprocalTotientDensity_actualSmallSupport_eq_b8_mainSum N cap hEven y hycap,
    actualSmallRosserMinus_eq_lowerRosserWeight_natCeil N cap y R hycap]
  rfl

/-- The actual upper density is the main sum of the very same upper
Rosser coefficient at `⌈R⌉₊`, including when `R` is an integer. -/
theorem actualSmallRosserPlusDensity_eq_b8_mainSum_natCeil
    (N cap : ℕ) (hEven : Even N) (y R : ℝ) (hycap : y ≤ (cap : ℝ)) :
    actualSmallRosserPlusDensity N cap y R =
      (goldbachB8PlusBoundingSieve N hEven y).mainSum
        (LinearSieve.upperRosserWeight
          (goldbachB8PlusBoundingSieve N hEven y).prodPrimes ⌈R⌉₊) := by
  unfold actualSmallRosserPlusDensity
  rw [reciprocalTotientDensity_actualSmallSupport_eq_b8_mainSum N cap hEven y hycap,
    actualSmallRosserPlus_eq_upperRosserWeight_natCeil N cap y R hycap]
  rfl

/-- The normalizing Euler product is also the product of the same actual
target-prime-deleted sieve, rather than a substitute prime carrier. -/
theorem actualSmallEulerProduct_eq_b8_sieveProductPrimeFactors
    (N cap : ℕ) (hEven : Even N) (y : ℝ) (hycap : y ≤ (cap : ℝ)) :
    actualSmallEulerProduct N cap y =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (goldbachB8PlusBoundingSieve N hEven y) := by
  unfold actualSmallEulerProduct AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
  change _ = ∏ p ∈ (goldbachB10ProdPrimes N y).primeFactors,
    (1 - (goldbachB8PlusBoundingSieve N hEven y).nu p)
  rw [goldbachB10ProdPrimes_primeFactors,
    ← actualSmallPrimeFinset_eq_goldbachB10SiftingPrimes N cap y hycap]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := actualSmallPrimeFinset_prime N cap y p hp
  rw [goldbachB8PlusBoundingSieve_nu_eq_inv_totient, Nat.totient_prime hprime,
    Nat.cast_sub hprime.one_le, Nat.cast_one]

end

end ImbalancedChen
