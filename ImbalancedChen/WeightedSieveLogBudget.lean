import ImbalancedChen.WeightedSieveError
import ImbalancedChen.DivisorMomentBudget

/-!
# Explicit logarithmic cost of transferring the actual sieve error

The elementary squarefree divisor-moment bound is composed with the
actual lambda-square remainder transfer. The resulting bound contains
only the actual unweighted primitive-residue discrepancy sum and an
explicit logarithmic factor; there is no remaining divisor moment.

For fixed natural accuracies `A` and `J`, the last theorem gives the
finite implication

`Σ |Δ(d)| ≤ C * N / (log N)^(2*A + 16 + 4*J)`

`⇒ errSum(lambdaSquared w)^2 ≤ 3 * 8^16 * C * N^2 / (log N)^(2*A)`

when `|w n| ≤ (log N)^J`, the weights vanish above `L`, `L² ≤ N`, and
the existing roughness gate holds. The discrepancy sum runs over exactly
the positive moduli at most `L²` that are coprime to `N`. The sixteen
divisor powers and four coefficient powers are fully paid. The case
`J = 0` includes weights bounded by one.

The only analytic premise of that implication is displayed literally as
an unweighted source discrepancy estimate. This file does not prove it,
does not replace the source, and does not claim an optimized sieve or
the final transfer theorem.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The actual sieve error after paying the entire fourth divisor moment.
Only the literal unweighted discrepancy at primitive residues remains. -/
theorem halfProductBoundingSieve_errSum_lambdaSquared_sq_le_logBudget
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N)
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ))))
    (w : ℕ → ℝ) (L : ℕ) (hlevel : L * L ≤ N)
    (hcut : ∀ n : ℕ, L < n → w n = 0)
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ n : ℕ, n ≤ L → |w n| ≤ W) :
    ((halfProductBoundingSieve num den N T z hN).errSum
      (BoundingSieve.lambdaSquared w)) ^ 2 ≤
      W ^ 4 * (3 * (N : ℝ) *
        (4 * (1 + Real.log (max 1 ((L * L : ℕ) : ℝ)))) ^ 16) *
        (∑ d ∈ Finset.Icc 1 (L * L) with Nat.Coprime d N,
          |halfProductCongruenceMass num den N T d -
            halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) := by
  have hmoment := sum_sieveProduct_divisor_fourth_moment_le_log N z (L * L)
  refine (halfProductBoundingSieve_errSum_lambdaSquared_sq_le_unweighted_coprime_Icc
    num den N T z hN hnum hden hT hcap w L hlevel hcut W hW hw).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hmoment
        (mul_nonneg (by norm_num) (Nat.cast_nonneg N))) (pow_nonneg hW 4))
    (Finset.sum_nonneg fun _d _hd => abs_nonneg _)

/-- At any level `D ≤ N`, with `log N ≥ 1`, the elementary divisor-moment
majorant costs at most sixteen powers of `log N` and the constant `8^16`.
The empty level `D = 0` is covered by the literal `max 1 D`. -/
theorem divisor_moment_logBudget_le (D N : ℕ) (hD : D ≤ N)
    (hN : 1 ≤ (N : ℝ)) (hlog : 1 ≤ Real.log (N : ℝ)) :
    (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ 16 ≤
      (8 * Real.log (N : ℝ)) ^ 16 := by
  have hmaxpos : (0 : ℝ) < max 1 (D : ℝ) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmax : max 1 (D : ℝ) ≤ (N : ℝ) :=
    max_le hN (Nat.cast_le.mpr hD)
  have hlogD : Real.log (max 1 (D : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hmaxpos hmax
  have hlogD0 : 0 ≤ Real.log (max 1 (D : ℝ)) :=
    Real.log_nonneg (le_max_left _ _)
  apply pow_le_pow_left₀ (by linarith :
    (0 : ℝ) ≤ 4 * (1 + Real.log (max 1 (D : ℝ))))
  linarith

/-- Fixed logarithmic accuracy pays the complete weighted-error cost.
The premise is the actual unweighted primitive-residue discrepancy sum,
not a weighted error or a target-count bound. The exponent is fixed by
`A` and `J`; all remaining source, level, and weight choices are finite.
No extra logarithm buffer is needed for this explicit squared bound. -/
theorem halfProductBoundingSieve_errSum_lambdaSquared_sq_le_of_unweighted_logBound
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N)
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ))))
    (w : ℕ → ℝ) (L A J : ℕ) (hlevel : L * L ≤ N)
    (hcut : ∀ n : ℕ, L < n → w n = 0)
    (hN1 : 1 ≤ (N : ℝ)) (hlog : 1 ≤ Real.log (N : ℝ))
    (hw : ∀ n : ℕ, n ≤ L → |w n| ≤ (Real.log (N : ℝ)) ^ J)
    (C : ℝ) (hC : 0 ≤ C)
    (hdistribution :
      (∑ d ∈ Finset.Icc 1 (L * L) with Nat.Coprime d N,
        |halfProductCongruenceMass num den N T d -
          halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ (2 * A + 16 + 4 * J)) :
    ((halfProductBoundingSieve num den N T z hN).errSum
      (BoundingSieve.lambdaSquared w)) ^ 2 ≤
      3 * (8 : ℝ) ^ 16 * C * (N : ℝ) ^ 2 /
        (Real.log (N : ℝ)) ^ (2 * A) := by
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hW : 0 ≤ (Real.log (N : ℝ)) ^ J := pow_nonneg hlogpos.le J
  have hlogBudget := divisor_moment_logBudget_le (L * L) N hlevel hN1 hlog
  have hcost : ((Real.log (N : ℝ)) ^ J) ^ 4 *
      (3 * (N : ℝ) * (4 * (1 + Real.log (max 1 ((L * L : ℕ) : ℝ)))) ^ 16) ≤
      ((Real.log (N : ℝ)) ^ J) ^ 4 *
        (3 * (N : ℝ) * (8 * Real.log (N : ℝ)) ^ 16) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hlogBudget
        (mul_nonneg (by norm_num) (Nat.cast_nonneg N))) (pow_nonneg hW 4)
  calc
    _ ≤ ((Real.log (N : ℝ)) ^ J) ^ 4 *
        (3 * (N : ℝ) * (4 * (1 + Real.log (max 1 ((L * L : ℕ) : ℝ)))) ^ 16) *
        (∑ d ∈ Finset.Icc 1 (L * L) with Nat.Coprime d N,
          |halfProductCongruenceMass num den N T d -
            halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) :=
      halfProductBoundingSieve_errSum_lambdaSquared_sq_le_logBudget
        num den N T z hN hnum hden hT hcap w L hlevel hcut _ hW hw
    _ ≤ (((Real.log (N : ℝ)) ^ J) ^ 4 *
        (3 * (N : ℝ) * (8 * Real.log (N : ℝ)) ^ 16)) *
        (C * (N : ℝ) / (Real.log (N : ℝ)) ^ (2 * A + 16 + 4 * J)) :=
      mul_le_mul hcost hdistribution
        (Finset.sum_nonneg fun _d _hd => abs_nonneg _)
        (mul_nonneg (pow_nonneg hW 4)
          (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N))
            (pow_nonneg (mul_nonneg (by norm_num) hlogpos.le) 16)))
    _ = _ := by
      rw [← pow_mul, mul_pow (8 : ℝ) (Real.log (N : ℝ)) 16,
        show 2 * A + 16 + 4 * J = (J * 4 + 16) + 2 * A by omega,
        pow_add (Real.log (N : ℝ)) (J * 4 + 16) (2 * A),
        pow_add (Real.log (N : ℝ)) (J * 4) 16]
      field_simp [hlogpos.ne'] <;> ring

end

end ImbalancedChen
