import ImbalancedChen.ActualPrimeBoxEulerLower
import ImbalancedChen.RoughPowerParameters

/-!
# One threshold for a fixed prime box and varying outer exponent

The tuple carrier, its reciprocal weight and numerator Euler product are
fixed. Increasing the outer exponent decreases the positive denominator.
Consequently an existing lower threshold at a fixed positive exponent works
for every larger outer exponent whose cutoff is covered by the same cap.
This comparison does not assert monotonicity of signed Rosser coefficients.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

theorem actualPrimeBoxEulerMass_mono_outer
    {k : ℕ} (N cap : ℕ) (hN : 1 ≤ N) (hEven : Even N)
    (a b : Fin k → ℝ) (u₀ u : ℝ) (j : Fin k)
    (hu : u₀ ≤ u) (hcap : (N : ℝ) ^ u ≤ (cap : ℝ)) :
    actualPrimeBoxEulerMass N cap a b u₀ j ≤
      actualPrimeBoxEulerMass N cap a b u j := by
  have hpow : (N : ℝ) ^ u₀ ≤ (N : ℝ) ^ u :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hu
  have hV := actualSmallEulerProduct_antitone_cutoff N cap hEven _ _ hpow hcap
  unfold actualPrimeBoxEulerMass
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (actualPrimeBoxWeight_nonneg hp)
  exact div_le_div_of_nonneg_left
    (actualSmallEulerProduct_pos N cap (p j : ℝ) hEven).le
    (actualSmallEulerProduct_pos N cap ((N : ℝ) ^ u) hEven) hV

/-- Fixed absolute exponent boxes have a common lower threshold for every
outer exponent at least `u₀`. The asymptotic gain remains evaluated at `u₀`. -/
theorem exists_actualPrimeBoxEulerMass_uniform_outer_lower_threshold
    {k : ℕ} (a b : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (u₀ : ℝ) (hu₀ : 0 < u₀) (j : Fin k) (hbu : b j ≤ u₀)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ u : ℝ, u₀ ≤ u → ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        (u₀ / b j) * (∏ i, Real.log (b i / a i)) - eta ≤
          actualPrimeBoxEulerMass N cap a b u j := by
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualPrimeBoxEulerMass_lower_threshold a b ha hab u₀ hu₀ j hbu eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven u hu cap hcap
  have hN1 : 1 ≤ N := by omega
  have hpow : (N : ℝ) ^ u₀ ≤ (N : ℝ) ^ u :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) hu
  exact (hbound N hN hEven cap (hpow.trans hcap)).trans
    (actualPrimeBoxEulerMass_mono_outer N cap hN1 hEven a b u₀ u j hu hcap)

end

end ImbalancedChen
