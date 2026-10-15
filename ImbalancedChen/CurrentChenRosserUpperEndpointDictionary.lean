import ImbalancedChen.CurrentChenRosserEndpointDictionary

/-!
# Exact upper coefficient dictionary on the actual initial Chen sieve

The actual prime-receiver sieve and its reciprocal-totient local densities
are unchanged. The actual plus coefficient has the identical product and
exact natural ceiling level, including integral real levels. No analytic
upper-density estimate is a premise.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open MathlibNt.SieveTheory

theorem currentChen_model_plus_natCeil
    (N cap : ℕ) (z L : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallRosserPlus N cap z L =
      LinearSieve.upperRosserWeight (sieveProduct N (Nat.ceil z)) (Nat.ceil L) := by
  unfold actualSmallRosserPlus ActualSmallRosserProvider.upperWeight
  rw [LiLiuPrereqWF.SmallRosser.upperWeight_eq_producer,
    currentChen_model_actualProduct_eq_sieveProduct N cap z hzcap]

/-- The main sum is exactly the same upper coefficient at `ceil L`,
including integer L; no floor-plus-one surrogate occurs. -/
theorem currentChen_model_plusDensity_eq_mainSum
    (N cap : ℕ) (z L : ℝ) (hEven : Even N) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallRosserPlusDensity N cap z L =
      (chenInitialBoundingSieve N z hEven).mainSum
        (LinearSieve.upperRosserWeight
          (chenInitialBoundingSieve N z hEven).prodPrimes (Nat.ceil L)) := by
  unfold actualSmallRosserPlusDensity reciprocalTotientDensity BoundingSieve.mainSum
  rw [currentChen_model_plus_natCeil N cap z L hzcap]
  have hs : actualSmallRosserSupport N cap z =
      (chenInitialBoundingSieve N z hEven).prodPrimes.divisors := by
    change (actualSmallPrimeProduct N cap z).divisors =
      (sieveProduct N (Nat.ceil z)).divisors
    rw [currentChen_model_actualProduct_eq_sieveProduct N cap z hzcap]
  rw [hs]
  apply Finset.sum_congr rfl
  intro d hd
  change LinearSieve.upperRosserWeight (sieveProduct N (Nat.ceil z)) (Nat.ceil L) d /
      (Nat.totient d : ℝ) =
    LinearSieve.upperRosserWeight (sieveProduct N (Nat.ceil z)) (Nat.ceil L) d *
      (1 / (Nat.totient d : ℝ))
  ring

end

end ImbalancedChen
