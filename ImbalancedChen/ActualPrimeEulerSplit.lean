import ImbalancedChen.ActualSmallRosserDensity
import ImbalancedChen.RoughPowerParameters

/-!
# Exact Euler partition at an actual boundary prime

The same target-deleted finite prime carrier splits into primes below a
boundary prime, that prime itself, and primes above it. The lower product
is the literal strict actual Euler product at the boundary prime. No cap
coverage or asymptotic assumption is required for these finite identities.

For even targets every Euler factor is positive. The final identity rewrites
the normalized boundary term using only reciprocal p-1 densities and the
ratio of actual Euler products, ready for the proved prime-cell suppliers.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Restricting the actual carrier below a natural boundary preserves all
target exclusions and the original enumeration cap. -/
theorem actualSmallPrimeFinset_filter_lt
    (N cap : ℕ) (y : ℝ) (q : ℕ) (hq : (q : ℝ) ≤ y) :
    (actualSmallPrimeFinset N cap y).filter (fun p => p < q) =
      actualSmallPrimeFinset N cap (q : ℝ) := by
  ext p
  simp only [Finset.mem_filter, mem_actualSmallPrimeFinset]
  constructor
  · rintro ⟨⟨hcap, hprime, hnot, _hy⟩, hpq⟩
    exact ⟨hcap, hprime, hnot, by exact_mod_cast hpq⟩
  · rintro ⟨hcap, hprime, hnot, hpq⟩
    exact ⟨⟨hcap, hprime, hnot, hpq.trans_le hq⟩, by exact_mod_cast hpq⟩

/-- The lower Euler product excludes q itself; its missing factor is
displayed explicitly between the lower and upper products. -/
theorem actualSmallEulerProduct_split_at
    (N cap : ℕ) (y : ℝ) {q : ℕ}
    (hq : q ∈ actualSmallPrimeFinset N cap y) :
    actualSmallEulerProduct N cap y =
      actualSmallEulerProduct N cap (q : ℝ) * (1 - 1 / ((q : ℝ) - 1)) *
        ∏ p ∈ (actualSmallPrimeFinset N cap y).filter (fun p => q < p),
          (1 - 1 / ((p : ℝ) - 1)) := by
  classical
  have hqy : (q : ℝ) ≤ y := (mem_actualSmallPrimeFinset.mp hq).2.2.2.le
  have hrest : (actualSmallPrimeFinset N cap y).filter (fun p => ¬p < q) =
      insert q ((actualSmallPrimeFinset N cap y).filter (fun p => q < p)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hp, hpq⟩
      by_cases heq : p = q
      · exact Or.inl heq
      · exact Or.inr ⟨hp, by omega⟩
    · rintro (rfl | ⟨hp, hpq⟩)
      · exact ⟨hq, by omega⟩
      · exact ⟨hp, by omega⟩
  have hqAbove : q ∉ (actualSmallPrimeFinset N cap y).filter (fun p => q < p) := by
    simp
  calc
    actualSmallEulerProduct N cap y =
        (∏ p ∈ (actualSmallPrimeFinset N cap y).filter (fun p => p < q),
          (1 - 1 / ((p : ℝ) - 1))) *
        ∏ p ∈ (actualSmallPrimeFinset N cap y).filter (fun p => ¬p < q),
          (1 - 1 / ((p : ℝ) - 1)) :=
      (Finset.prod_filter_mul_prod_filter_not (actualSmallPrimeFinset N cap y)
        (fun p => p < q) (fun p => (1 : ℝ) - 1 / ((p : ℝ) - 1))).symm
    _ = actualSmallEulerProduct N cap (q : ℝ) *
        ((1 - 1 / ((q : ℝ) - 1)) *
          ∏ p ∈ (actualSmallPrimeFinset N cap y).filter (fun p => q < p),
            (1 - 1 / ((p : ℝ) - 1))) := by
      rw [hrest, Finset.prod_insert hqAbove,
        actualSmallPrimeFinset_filter_lt N cap y q hqy]
      rfl
    _ = _ := (mul_assoc _ _ _).symm

/-- Every factor in the actual carrier is strictly positive for even
targets, including the degenerate empty carrier at target zero. -/
theorem actualSmallPrimeFinset_euler_factor_pos
    {N cap : ℕ} {y : ℝ} {p : ℕ} (hEven : Even N)
    (hp : p ∈ actualSmallPrimeFinset N cap y) :
    0 < 1 - 1 / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) < p := by
    exact_mod_cast (actualSmallPrimeFinset_odd_of_even hEven hp).2
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))

/-- The apparent reciprocal p-2 term cancels with the Euler denominator.
The remaining local factor is exactly 1/(q-1), and the lower Euler product
is the strict product at q. The tail test mass t is arbitrary. -/
theorem actualSmallEulerProduct_boundary_term
    (N cap : ℕ) (hEven : Even N) (y : ℝ) {q : ℕ}
    (hq : q ∈ actualSmallPrimeFinset N cap y) (t : ℝ) :
    ((1 / ((q : ℝ) - 1)) / (1 - 1 / ((q : ℝ) - 1))) *
        (t / (∏ p ∈ (actualSmallPrimeFinset N cap y).filter (fun p => q < p),
          (1 - 1 / ((p : ℝ) - 1)))) =
      ((1 / ((q : ℝ) - 1)) * t) *
        (actualSmallEulerProduct N cap (q : ℝ) / actualSmallEulerProduct N cap y) := by
  have hbelow := (actualSmallEulerProduct_pos N cap (q : ℝ) hEven).ne'
  have hfactor := (actualSmallPrimeFinset_euler_factor_pos hEven hq).ne'
  have habove : (∏ p ∈ (actualSmallPrimeFinset N cap y).filter (fun p => q < p),
      (1 - 1 / ((p : ℝ) - 1))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (actualSmallPrimeFinset_euler_factor_pos hEven (Finset.mem_filter.mp hp).1).ne'
  have hq2 : (2 : ℝ) < q := by
    exact_mod_cast (actualSmallPrimeFinset_odd_of_even hEven hq).2
  have hqDen : (q : ℝ) - 1 ≠ 0 := by linarith
  rw [actualSmallEulerProduct_split_at N cap y hq]
  field_simp

end

end ImbalancedChen
