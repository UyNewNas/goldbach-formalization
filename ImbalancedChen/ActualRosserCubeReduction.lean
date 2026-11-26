import ImbalancedChen.UpperRosserCubeCarrier
import ImbalancedChen.PrimeCubeCutoff
import ImbalancedChen.ActualSmallRosserDensity
import ImbalancedChen.RoughPowerParameters

/-!
# Exact first-cube reduction for the actual upper coefficient and density

The target-prime exclusions, finite enumeration cap, strict real endpoint
and actual coefficient are all retained. Cutting y down to min(y,R^(1/3))
does not change the upper coefficient, any weighted divisor sum, its
reciprocal-totient density, or its value on any integer test argument.

For power cutoffs with beta <= 3*u, the new cutoff is D^(beta/3). The exact
normalized density identity below separates the reduced density from the
Euler-product ratio. Neither factor's asymptotic is inferred from unrelated
one-sided sieve estimates; in particular this is not a proof of F(s).
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Literal equality of every actual upper coefficient, including zero
coefficients outside the displayed support. The enumeration cap may truncate
either prime carrier, and the real level may be zero. -/
theorem actualSmallRosserPlus_eq_cubeCutoff
    (N cap : ℕ) (y R : ℝ) (hR : 0 ≤ R) :
    actualSmallRosserPlus N cap y R =
      actualSmallRosserPlus N cap (min y (R ^ (1 / 3 : ℝ))) R := by
  have h := upperWeight_eq_cubeFilter (actualSmallPrimeFinset N cap y) R
    (actualSmallPrimeFinset_prime N cap y)
  rw [← actualSmallPrimeFinset_min_cubeRoot_eq_filter N cap y R hR] at h
  funext d
  exact DFunLike.congr_fun h d

/-- Weighted density equality on the two actual divisor carriers. Omitted
moduli have zero coefficient; no sign condition on the test function or
multiplicativity hypothesis is required. -/
theorem actualSmallRosserPlus_weighted_sum_eq_cubeCutoff
    (N cap : ℕ) (y R : ℝ) (hR : 0 ≤ R) (g : ℕ → ℝ) :
    (∑ d ∈ actualSmallRosserSupport N cap y,
      actualSmallRosserPlus N cap y R d * g d) =
    ∑ d ∈ actualSmallRosserSupport N cap (min y (R ^ (1 / 3 : ℝ))),
      actualSmallRosserPlus N cap (min y (R ^ (1 / 3 : ℝ))) R d * g d := by
  have h := upperWeight_density_eq_cubeFilter (actualSmallPrimeFinset N cap y) R
    (actualSmallPrimeFinset_prime N cap y) g
  rw [← actualSmallPrimeFinset_min_cubeRoot_eq_filter N cap y R hR] at h
  exact h

/-- The reciprocal-totient density of the literal actual coefficient is
unchanged, although its displayed divisor support has become smaller. -/
theorem actualSmallRosserPlusDensity_eq_cubeCutoff
    (N cap : ℕ) (y R : ℝ) (hR : 0 ≤ R) :
    actualSmallRosserPlusDensity N cap y R =
      actualSmallRosserPlusDensity N cap (min y (R ^ (1 / 3 : ℝ))) R := by
  simpa only [actualSmallRosserPlusDensity, reciprocalTotientDensity,
    div_eq_mul_inv, one_mul] using
    actualSmallRosserPlus_weighted_sum_eq_cubeCutoff N cap y R hR
      (fun d => 1 / (Nat.totient d : ℝ))

/-- The complete upper divisor polynomial is also unchanged on every
integer, including zero and negative arguments. -/
theorem actualSmallRosserPlusSum_eq_cubeCutoff
    (N cap : ℕ) (y R : ℝ) (hR : 0 ≤ R) (n : ℤ) :
    actualSmallRosserPlusSum N cap y R n =
      actualSmallRosserPlusSum N cap (min y (R ^ (1 / 3 : ℝ))) R n := by
  classical
  have h := actualSmallRosserPlus_weighted_sum_eq_cubeCutoff N cap y R hR
    (fun d => if d ∣ n.natAbs then (1 : ℝ) else 0)
  simpa only [actualSmallRosserPlusSum, supportedDivisorSum, Finset.sum_filter,
    mul_ite, mul_one, mul_zero] using h

/-- The strict first-cube reduction at literal power cutoffs, including
the equality beta=3*u. This statement is coefficientwise. -/
theorem actualSmallRosserPlus_power_eq_cubeCutoff
    (N cap : ℕ) {D beta u : ℝ} (hD : 1 < D) (hbetaU : beta ≤ 3 * u) :
    actualSmallRosserPlus N cap (D ^ u) (D ^ beta) =
      actualSmallRosserPlus N cap (D ^ (beta / 3)) (D ^ beta) := by
  have h := actualSmallRosserPlus_eq_cubeCutoff N cap (D ^ u) (D ^ beta)
    (Real.rpow_nonneg (by linarith : 0 ≤ D) _)
  rw [primeCubeCutoff_power hD hbetaU] at h
  exact h

/-- Exact density reduction to the cutoff D^(beta/3), whose logarithmic
coordinate is three when beta is positive, without changing the coefficient
or assuming a limiting sieve density. -/
theorem actualSmallRosserPlusDensity_power_eq_cubeCutoff
    (N cap : ℕ) {D beta u : ℝ} (hD : 1 < D) (hbetaU : beta ≤ 3 * u) :
    actualSmallRosserPlusDensity N cap (D ^ u) (D ^ beta) =
      actualSmallRosserPlusDensity N cap (D ^ (beta / 3)) (D ^ beta) := by
  have h := actualSmallRosserPlusDensity_eq_cubeCutoff N cap (D ^ u) (D ^ beta)
    (Real.rpow_nonneg (by linarith : 0 ≤ D) _)
  rw [primeCubeCutoff_power hD hbetaU] at h
  exact h

/-- The exact normalized reduction keeps the Euler ratio visible. A future
fixed-s limit must prove the limit of the reduced density and of this
target-prime-deleted Euler ratio on linked target power scales. -/
theorem actualSmallRosserPlusDensity_power_cube_ratio
    (N cap : ℕ) (hEven : Even N) {D beta u : ℝ}
    (hD : 1 < D) (hbetaU : beta ≤ 3 * u) :
    actualSmallRosserPlusDensity N cap (D ^ u) (D ^ beta) /
        actualSmallEulerProduct N cap (D ^ u) =
      (actualSmallRosserPlusDensity N cap (D ^ (beta / 3)) (D ^ beta) /
        actualSmallEulerProduct N cap (D ^ (beta / 3))) *
      (actualSmallEulerProduct N cap (D ^ (beta / 3)) /
        actualSmallEulerProduct N cap (D ^ u)) := by
  rw [actualSmallRosserPlusDensity_power_eq_cubeCutoff N cap hD hbetaU]
  have hV := (actualSmallEulerProduct_pos N cap (D ^ (beta / 3)) hEven).ne'
  field_simp [hV]

end

end ImbalancedChen
