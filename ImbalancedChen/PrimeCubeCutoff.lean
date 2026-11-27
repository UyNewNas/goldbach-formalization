import ImbalancedChen.ActualSmallRosser
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Strict prime-cube cutoffs for the actual finite carrier

Filtering the literal small-prime carrier by `p^3 < R` is exactly the
strict cutoff at `min y (R^(1/3))`. This includes the zero level and keeps
the endpoint `p^3 = R` excluded. The enumeration cap may be truncated.
The remaining results are exact real-power and logarithm identities; they
assert no Rosser-weight equality, sieve-density estimate, or prime theorem.
-/

namespace ImbalancedChen

noncomputable section

/-- The strict real cube-root test, with nonnegative bases including zero. -/
theorem real_lt_cubeRoot_iff {x R : ℝ} (hx : 0 ≤ x) (hR : 0 ≤ R) :
    x < R ^ (1 / 3 : ℝ) ↔ x ^ 3 < R := by
  simpa only [one_div, Real.rpow_ofNat] using
    (Real.lt_rpow_inv_iff_of_pos hx hR (by norm_num : (0 : ℝ) < 3))

/-- The carrier identity retains the target-prime exclusions and the
original finite enumeration cap. No assumption that the cap covers y is
needed, and primes with cube equal to R are excluded on both sides. -/
theorem actualSmallPrimeFinset_min_cubeRoot_eq_filter
    (N cap : ℕ) (y R : ℝ) (hR : 0 ≤ R) :
    actualSmallPrimeFinset N cap (min y (R ^ (1 / 3 : ℝ))) =
      (actualSmallPrimeFinset N cap y).filter (fun p : ℕ => (p : ℝ) ^ 3 < R) := by
  classical
  ext p
  simp only [mem_actualSmallPrimeFinset, Finset.mem_filter, lt_min_iff,
    real_lt_cubeRoot_iff (Nat.cast_nonneg p) hR]
  tauto

/-- In the first-cube range, the minimum cutoff is precisely D^(beta/3).
Equality beta = 3*u is included. Positivity of beta is unnecessary here. -/
theorem primeCubeCutoff_power {D beta u : ℝ}
    (hD : 1 < D) (hbetaU : beta ≤ 3 * u) :
    min (D ^ u) ((D ^ beta) ^ (1 / 3 : ℝ)) = D ^ (beta / 3) := by
  have hDnonneg : 0 ≤ D := (lt_trans zero_lt_one hD).le
  rw [← Real.rpow_mul hDnonneg]
  rw [show beta * (1 / 3 : ℝ) = beta / 3 by ring]
  exact min_eq_right (Real.rpow_le_rpow_of_exponent_le hD.le (by linarith))

/-- The reduced cutoff has residual logarithmic scale exactly three.
The positive exponent ensures that the denominator is nonzero. -/
theorem primeCubeCutoff_power_log_ratio {D beta u : ℝ}
    (hD : 1 < D) (hbeta : 0 < beta) (hbetaU : beta ≤ 3 * u) :
    Real.log (D ^ beta) /
      Real.log (min (D ^ u) ((D ^ beta) ^ (1 / 3 : ℝ))) = 3 := by
  have hDpos : 0 < D := lt_trans zero_lt_one hD
  rw [primeCubeCutoff_power hD hbetaU, Real.log_rpow hDpos, Real.log_rpow hDpos]
  field_simp [ne_of_gt hbeta, ne_of_gt (Real.log_pos hD)]

end

end ImbalancedChen
