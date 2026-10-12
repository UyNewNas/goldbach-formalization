import ImbalancedChen.RosserEndpointBridge
import ImbalancedChen.ActualPrimeEulerSplit

/-!
# Exact positive boundary expansion of the actual upper Rosser density

The coefficient is the same actual coefficient on primes not dividing the
target. Its strict real level is represented by `Nat.ceil R`, including at
integer levels. Each boundary term retains the Euler ratio strictly below
its least prime over the full Euler product. Thus all selected primes carry
the density `1 / (p - 1)` and no new prime-mass supplier is assumed.

These are finite identities and inequalities. They do not assert a fixed-s
Rosser asymptotic or remove any analytic premise of such an asymptotic.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The literal divisor density equals the subset density of the same
actual prime carrier, with the real strict level encoded by its ceiling. -/
theorem actualSmallRosserPlusDensity_eq_setDensitySum
    (N cap : ℕ) (hEven : Even N) (y R : ℝ) (hcap : y ≤ (cap : ℝ)) :
    actualSmallRosserPlusDensity N cap y R =
      LinearSieve.upperRosserSetDensitySum (fun p : ℕ => 1 / ((p : ℝ) - 1))
        (Nat.ceil R) (actualSmallPrimeFinset N cap y) := by
  rw [actualSmallRosserPlusDensity_eq_b8_mainSum_natCeil N cap hEven y R hcap,
    LinearSieve.mainSum_upperRosserWeight_eq_setDensitySum]
  unfold LinearSieve.upperRosserSetDensitySum
  change (∑ s ∈ (goldbachB10ProdPrimes N y).primeFactors.powerset,
    LinearSieve.upperRosserSetWeight (Nat.ceil R) s *
      ∏ p ∈ s, (goldbachB8PlusBoundingSieve N hEven y).nu p) = _
  rw [goldbachB10ProdPrimes_primeFactors,
    ← actualSmallPrimeFinset_eq_goldbachB10SiftingPrimes N cap y hcap]
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := actualSmallPrimeFinset_prime N cap y p
    (Finset.mem_powerset.mp hs hp)
  rw [goldbachB8PlusBoundingSieve_nu_eq_inv_totient,
    Nat.totient_prime hprime, Nat.cast_sub hprime.one_le, Nat.cast_one]

/-- The selected even sets above the distinguished least prime that first
cross an upper Rosser constraint at the exact ceiling level. -/
def actualUpperRosserBoundarySets (N cap : ℕ) (y R : ℝ) (q : ℕ) :
    Finset (Finset ℕ) :=
  ((actualSmallPrimeFinset N cap y).filter (fun p => q < p)).powerset.filter
    (LinearSieve.UpperRosserBoundarySet (Nat.ceil R) q)

/-- A boundary term on the normalized density scale. The lower Euler
cutoff is strictly `p < q`, so the distinguished prime is not counted twice. -/
def actualUpperRosserBoundaryTerm (N cap : ℕ) (y : ℝ) (q : ℕ) (s : Finset ℕ) : ℝ :=
  ((1 / ((q : ℝ) - 1)) * ∏ p ∈ s, 1 / ((p : ℝ) - 1)) *
    (actualSmallEulerProduct N cap (q : ℝ) / actualSmallEulerProduct N cap y)

theorem actualUpperRosserBoundaryTerm_nonneg
    (N cap : ℕ) (hEven : Even N) (y : ℝ) {q : ℕ} {s : Finset ℕ}
    (hq : q ∈ actualSmallPrimeFinset N cap y)
    (hs : s ⊆ actualSmallPrimeFinset N cap y) :
    0 ≤ actualUpperRosserBoundaryTerm N cap y q s := by
  have hnu (p : ℕ) (hp : p ∈ actualSmallPrimeFinset N cap y) :
      0 ≤ 1 / ((p : ℝ) - 1) := by
    have hp2 : (2 : ℝ) < p := by
      exact_mod_cast (actualSmallPrimeFinset_odd_of_even hEven hp).2
    exact div_nonneg (by norm_num) (by linarith)
  exact mul_nonneg
    (mul_nonneg (hnu q hq) (Finset.prod_nonneg (fun p hp => hnu p (hs hp))))
    (div_nonneg (actualSmallEulerProduct_pos N cap (q : ℝ) hEven).le
      (actualSmallEulerProduct_pos N cap y hEven).le)

/-- Exact finite expansion into positive first-boundary contributions of
the same actual coefficient. Both the prime carrier and the strict ceiling
level remain literal; no density estimate is a premise. -/
theorem actualSmallRosserPlusDensity_ratio_eq_one_add_boundary
    (N cap : ℕ) (hEven : Even N) (y R : ℝ)
    (hcap : y ≤ (cap : ℝ)) (hR : 1 < R)
    (hlevel : ∀ p ∈ actualSmallPrimeFinset N cap y, (p : ℝ) < R) :
    actualSmallRosserPlusDensity N cap y R / actualSmallEulerProduct N cap y =
      1 + ∑ q ∈ actualSmallPrimeFinset N cap y,
        ∑ s ∈ actualUpperRosserBoundarySets N cap y R q,
          actualUpperRosserBoundaryTerm N cap y q s := by
  rw [actualSmallRosserPlusDensity_eq_setDensitySum N cap hEven y R hcap]
  change LinearSieve.upperRosserSetDensitySum (fun p : ℕ => 1 / ((p : ℝ) - 1))
      (Nat.ceil R) (actualSmallPrimeFinset N cap y) /
      (∏ p ∈ actualSmallPrimeFinset N cap y, (1 - 1 / ((p : ℝ) - 1))) = _
  rw [LinearSieve.upperRosserSetDensityRatio_eq_one_add_sum_boundary
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (actualSmallPrimeFinset N cap y)
    (Nat.lt_ceil.mpr (by simpa only [Nat.cast_one] using hR))
    (actualSmallPrimeFinset_prime N cap y)
    (fun p hp => Nat.lt_ceil.mpr (hlevel p hp))
    (fun p hp => ne_of_gt (actualSmallPrimeFinset_euler_factor_pos hEven hp))]
  apply congrArg (fun x : ℝ => 1 + x)
  apply Finset.sum_congr rfl
  intro q hq
  change ((1 / ((q : ℝ) - 1)) / (1 - 1 / ((q : ℝ) - 1))) *
      ((∑ s ∈ actualUpperRosserBoundarySets N cap y R q,
          ∏ p ∈ s, 1 / ((p : ℝ) - 1)) /
        (∏ p ∈ (actualSmallPrimeFinset N cap y).filter (fun p => q < p),
          (1 - 1 / ((p : ℝ) - 1)))) = _
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  exact actualSmallEulerProduct_boundary_term N cap hEven y hq
    (∏ p ∈ s, 1 / ((p : ℝ) - 1))

/-- Any genuinely selected subset of the finite boundary carrier gives
a lower bound. The omitted terms are nonnegative, as proved from the actual
prime carrier; no selected-mass or analytic inequality is assumed. -/
theorem actualSmallRosserPlusDensity_ratio_ge_selected_boundary
    (N cap : ℕ) (hEven : Even N) (y R : ℝ)
    (hcap : y ≤ (cap : ℝ)) (hR : 1 < R)
    (hlevel : ∀ p ∈ actualSmallPrimeFinset N cap y, (p : ℝ) < R)
    (Q : Finset ℕ) (T : ℕ → Finset (Finset ℕ))
    (hQ : Q ⊆ actualSmallPrimeFinset N cap y)
    (hT : ∀ q ∈ Q, T q ⊆ actualUpperRosserBoundarySets N cap y R q) :
    1 + ∑ q ∈ Q, ∑ s ∈ T q, actualUpperRosserBoundaryTerm N cap y q s ≤
      actualSmallRosserPlusDensity N cap y R / actualSmallEulerProduct N cap y := by
  rw [actualSmallRosserPlusDensity_ratio_eq_one_add_boundary
    N cap hEven y R hcap hR hlevel]
  apply add_le_add (le_refl (1 : ℝ))
  have hterm (q : ℕ) (hq : q ∈ actualSmallPrimeFinset N cap y)
      (s : Finset ℕ) (hs : s ∈ actualUpperRosserBoundarySets N cap y R q) :
      0 ≤ actualUpperRosserBoundaryTerm N cap y q s := by
    apply actualUpperRosserBoundaryTerm_nonneg N cap hEven y hq
    exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1).trans
      (Finset.filter_subset _ _)
  calc
    (∑ q ∈ Q, ∑ s ∈ T q, actualUpperRosserBoundaryTerm N cap y q s) ≤
        ∑ q ∈ Q, ∑ s ∈ actualUpperRosserBoundarySets N cap y R q,
          actualUpperRosserBoundaryTerm N cap y q s := by
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.sum_le_sum_of_subset_of_nonneg (hT q hq)
        (fun s hs _ => hterm q (hQ hq) s hs)
    _ ≤ ∑ q ∈ actualSmallPrimeFinset N cap y,
        ∑ s ∈ actualUpperRosserBoundarySets N cap y R q,
          actualUpperRosserBoundaryTerm N cap y q s :=
      Finset.sum_le_sum_of_subset_of_nonneg hQ
        (fun q hq _ => Finset.sum_nonneg (fun s hs => hterm q hq s hs))

end

end ImbalancedChen
