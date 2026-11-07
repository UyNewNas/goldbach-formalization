import ImbalancedChen.ActualSelbergMain
import Mathlib.Analysis.Real.Sqrt

/-!
# An optimized finite upper bound for the actual half-product source

The explicit finite Selberg coefficients give the actual sifted cardinality
an upper bound with the genuine source mass divided by the literal finite
normalizer

`G = ∑ d ∣ sieveProduct N z, d ≤ L, ∏ p ∣ d, 1 / (p - 2)`.

The exact error retains the genuine lambda-square coefficient and only the
allowed divisors at most `L²`. The proved roughness gate identifies its
remainder with the actual coprime-normalized source discrepancy. Neither
the coefficient bound, its support, nor the evaluation of the main sum is
assumed.

The final theorem consumes the literal unweighted primitive-residue
discrepancy estimate with exponent `2*A + 16` and gives the explicit
nonnegative error `sqrt (3 * 8^16 * C * N^2 / (log N)^(2*A))`.
That unweighted estimate is the only analytic input. The finite normalizer
is not replaced by an asymptotic estimate, and no final counting or
distribution theorem is claimed unconditionally.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The actual optimized error, with its exact allowed-divisor support and
its primitive-source discrepancy. The `L²` cutoff is proved from the
explicit coefficient formula; no support hypothesis is supplied. -/
theorem halfProduct_finiteSelbergWeight_errSum_eq_truncated_primitive
    (num den N : ℕ) (T : ℝ) (z L : ℕ) (hN : Even N)
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ)))) :
    (halfProductBoundingSieve num den N T z hN).errSum
        (BoundingSieve.lambdaSquared
          (finiteSelbergWeight (halfProductBoundingSieve num den N T z hN) L)) =
      ∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
        |BoundingSieve.lambdaSquared
          (finiteSelbergWeight (halfProductBoundingSieve num den N T z hN) L) d| *
        |halfProductCongruenceMass num den N T d -
          halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)| := by
  classical
  rw [boundingSieve_errSum_lambdaSquared_truncated
    (halfProductBoundingSieve num den N T z hN)
    (finiteSelbergWeight (halfProductBoundingSieve num den N T z hN) L) L
    (fun d hd => finiteSelbergWeight_eq_zero_of_level
      (halfProductBoundingSieve num den N T z hN) L d hd)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [halfProductBoundingSieve_rem_eq_primitive_discrepancy hN hnum hden hT hcap
    (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)]

/-- The actual sifted count with the evaluated finite main term and the
exact truncated primitive error. This finite statement has no distribution
hypothesis. The numerator is the cardinality of the original inclusive
source, and the denominator is the actual reciprocal-`p-2` normalizer. -/
theorem siftedHalfProductSource_card_le_optimized_truncated_primitive
    (num den N : ℕ) (T : ℝ) (z L : ℕ) (hN : Even N)
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ)))) (hL : 1 ≤ L) :
    ((siftedHalfProductSource num den N T z).card : ℝ) ≤
      ((halfProductSource num den N T).card : ℝ) /
        (∑ d ∈ (sieveProduct N z).divisors with d ≤ L,
          ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2)) +
      ∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
        |BoundingSieve.lambdaSquared
          (finiteSelbergWeight (halfProductBoundingSieve num den N T z hN) L) d| *
        |halfProductCongruenceMass num den N T d -
          halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)| := by
  have h := siftedSum_le_finiteSelbergNormalizer_add_errSum
    (halfProductBoundingSieve num den N T z hN) hL
  rw [halfProductBoundingSieve_siftedSum, halfProductBoundingSieve_totalMass,
    halfProduct_finiteSelbergNormalizer,
    halfProduct_finiteSelbergWeight_errSum_eq_truncated_primitive
      num den N T z L hN hnum hden hT hcap] at h
  exact h

/-- An explicit optimized upper bound for the actual sifted source.
The sole analytic premise is displayed as the unweighted discrepancy over
positive moduli at most `L²` coprime to `N`. The actual finite weights have
already been proved bounded by one, so `J = 0` pays exactly sixteen extra
logarithmic powers. The displayed square-root error is nonnegative. -/
theorem siftedHalfProductSource_card_le_optimized_of_unweighted_logBound
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N)
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ))))
    (L A : ℕ) (hL : 1 ≤ L) (hlevel : L * L ≤ N)
    (hN1 : 1 ≤ (N : ℝ)) (hlog : 1 ≤ Real.log (N : ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hdistribution :
      (∑ d ∈ Finset.Icc 1 (L * L) with Nat.Coprime d N,
        |halfProductCongruenceMass num den N T d -
          halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ (2 * A + 16)) :
    ((siftedHalfProductSource num den N T z).card : ℝ) ≤
      ((halfProductSource num den N T).card : ℝ) /
        (∑ d ∈ (sieveProduct N z).divisors with d ≤ L,
          ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2)) +
      Real.sqrt (3 * (8 : ℝ) ^ 16 * C * (N : ℝ) ^ 2 /
        (Real.log (N : ℝ)) ^ (2 * A)) := by
  have herr := halfProduct_finiteSelbergWeight_errSum_sq_le_of_unweighted_logBound
    num den N T z hN hnum hden hT hcap L A hL hlevel hN1 hlog C hC hdistribution
  have hcount := siftedSum_le_finiteSelbergNormalizer_add_errSum
    (halfProductBoundingSieve num den N T z hN) hL
  have h := hcount.trans (add_le_add le_rfl (Real.le_sqrt_of_sq_le herr))
  simpa only [halfProductBoundingSieve_siftedSum, halfProductBoundingSieve_totalMass,
    halfProduct_finiteSelbergNormalizer] using h

end

end ImbalancedChen
