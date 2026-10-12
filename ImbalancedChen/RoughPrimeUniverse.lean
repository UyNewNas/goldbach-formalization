import ImbalancedChen.RetainedModuli
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# The manuscript's finite rough-prime universe

The raw positive upper-sieve tree is evaluated on the primes

`p ∤ N`, `w ≤ p`, and `p < z`,

in decreasing order.  This file constructs that finite ordered universe
without replacing either real endpoint by an unproved floor or ceiling.
Instead, `cap` is an explicit enumeration bound.  The theorem
`mem_roughPrimeUniverse_iff_of_cutoff_le_cap` removes that auxiliary bound
as soon as the caller proves `z ≤ cap`.

This is still the raw first-exit tree.  The manuscript's causal retention
predicate, boxed coefficient domination, density estimate, and distribution
error are separate obligations.
-/

namespace ImbalancedChen

noncomputable section

/-- The finite set of primes in the manuscript's rough range, enumerated
below an explicit natural-number cap.  The inequalities against `w` and `z`
are the literal real inequalities used in the manuscript. -/
def roughPrimeFinset (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  (Finset.range cap).filter fun p =>
    p.Prime ∧ ¬p ∣ N ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z

/-- Exact membership in the capped rough-prime finset. -/
@[simp] theorem mem_roughPrimeFinset {N cap p : ℕ} {w z : ℝ} :
    p ∈ roughPrimeFinset N cap w z ↔
      p < cap ∧ p.Prime ∧ ¬p ∣ N ∧
        w ≤ (p : ℝ) ∧ (p : ℝ) < z := by
  simp [roughPrimeFinset]

/-- Once `cap` lies above the real upper cutoff, capped membership is
exactly the manuscript predicate.  No floor or ceiling convention is used. -/
theorem mem_roughPrimeFinset_iff_of_cutoff_le_cap
    {N cap p : ℕ} {w z : ℝ} (hzcap : z ≤ (cap : ℝ)) :
    p ∈ roughPrimeFinset N cap w z ↔
      p.Prime ∧ ¬p ∣ N ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z := by
  constructor
  · exact fun hp => (mem_roughPrimeFinset.mp hp).2
  · intro hp
    have hpReal : (p : ℝ) < (cap : ℝ) :=
      lt_of_lt_of_le hp.2.2.2 hzcap
    have hpcap : p < cap := by
      exact_mod_cast hpReal
    exact mem_roughPrimeFinset.mpr ⟨hpcap, hp⟩

/-- The rough primes in the decreasing order required by the causal scan. -/
def roughPrimeUniverse (N cap : ℕ) (w z : ℝ) : List ℕ :=
  (roughPrimeFinset N cap w z).sort (· ≥ ·)

/-- Exact membership in the ordered rough-prime universe. -/
@[simp] theorem mem_roughPrimeUniverse {N cap p : ℕ} {w z : ℝ} :
    p ∈ roughPrimeUniverse N cap w z ↔
      p < cap ∧ p.Prime ∧ ¬p ∣ N ∧
        w ≤ (p : ℝ) ∧ (p : ℝ) < z := by
  simp [roughPrimeUniverse]

/-- The auxiliary enumeration cap disappears from ordered-universe
membership once it is known to dominate `z`. -/
theorem mem_roughPrimeUniverse_iff_of_cutoff_le_cap
    {N cap p : ℕ} {w z : ℝ} (hzcap : z ≤ (cap : ℝ)) :
    p ∈ roughPrimeUniverse N cap w z ↔
      p.Prime ∧ ¬p ∣ N ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z := by
  constructor
  · exact fun hp => (mem_roughPrimeUniverse.mp hp).2
  · intro hp
    have hpReal : (p : ℝ) < (cap : ℝ) :=
      lt_of_lt_of_le hp.2.2.2 hzcap
    have hpcap : p < cap := by
      exact_mod_cast hpReal
    exact mem_roughPrimeUniverse.mpr ⟨hpcap, hp⟩

/-- Sorting a finset supplies distinct primes; `Nodup` is not an analytic
hypothesis on the sieve. -/
theorem roughPrimeUniverse_nodup (N cap : ℕ) (w z : ℝ) :
    (roughPrimeUniverse N cap w z).Nodup := by
  simpa [roughPrimeUniverse] using
    (Finset.sort_nodup (roughPrimeFinset N cap w z) (· ≥ ·))

/-- Forgetting the decreasing order recovers exactly the original finite
rough-prime carrier. -/
@[simp] theorem roughPrimeUniverse_toFinset (N cap : ℕ) (w z : ℝ) :
    (roughPrimeUniverse N cap w z).toFinset =
      roughPrimeFinset N cap w z := by
  simpa [roughPrimeUniverse] using
    (Finset.sort_toFinset (roughPrimeFinset N cap w z) (· ≥ ·))

/-- The concrete universe is strictly decreasing, as required by the
manuscript's causal prefix history. -/
theorem roughPrimeUniverse_sortedGT (N cap : ℕ) (w z : ℝ) :
    (roughPrimeUniverse N cap w z).SortedGT := by
  simpa [roughPrimeUniverse] using
    (Finset.sortedGT_sort (roughPrimeFinset N cap w z))

/-- Pairwise form of the strict decreasing-order invariant. -/
theorem roughPrimeUniverse_pairwise_gt (N cap : ℕ) (w z : ℝ) :
    (roughPrimeUniverse N cap w z).Pairwise (· > ·) :=
  (roughPrimeUniverse_sortedGT N cap w z).pairwise

theorem mem_roughPrimeUniverse_prime
    {N cap p : ℕ} {w z : ℝ}
    (hp : p ∈ roughPrimeUniverse N cap w z) :
    p.Prime :=
  (mem_roughPrimeUniverse.mp hp).2.1

theorem mem_roughPrimeUniverse_not_dvd
    {N cap p : ℕ} {w z : ℝ}
    (hp : p ∈ roughPrimeUniverse N cap w z) :
    ¬p ∣ N :=
  (mem_roughPrimeUniverse.mp hp).2.2.1

theorem mem_roughPrimeUniverse_lower
    {N cap p : ℕ} {w z : ℝ}
    (hp : p ∈ roughPrimeUniverse N cap w z) :
    w ≤ (p : ℝ) :=
  (mem_roughPrimeUniverse.mp hp).2.2.2.1

theorem mem_roughPrimeUniverse_upper
    {N cap p : ℕ} {w z : ℝ}
    (hp : p ∈ roughPrimeUniverse N cap w z) :
    (p : ℝ) < z :=
  (mem_roughPrimeUniverse.mp hp).2.2.2.2

/-- Every retained branch over the concrete rough-prime universe has a
squarefree selected modulus. -/
theorem mem_roughPrimeRetainedLeaves_selectedProd_squarefree
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w z : ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h
      (roughPrimeUniverse N cap w z)) :
    Squarefree leaf.selected.prod := by
  exact mem_oddFirstExitRetainedLeaves_selectedProd_squarefree
    retainOdd h (roughPrimeUniverse N cap w z)
    (roughPrimeUniverse_nodup N cap w z)
    (fun p hp => mem_roughPrimeUniverse_prime hp) leaf hleaf

/-- On the concrete manuscript range, every retained leaf already has the
Möbius coefficient of its selected squarefree prime product. -/
theorem mem_roughPrimeRetainedLeaves_value_eq_moebius_mul_selected_prod
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w z : ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h
      (roughPrimeUniverse N cap w z)) :
    leaf.value =
      (ArithmeticFunction.moebius leaf.selected.prod : ℝ) *
        (leaf.selected.map h).prod := by
  exact mem_oddFirstExitRetainedLeaves_value_eq_moebius_mul_selected_prod
    retainOdd h (roughPrimeUniverse N cap w z)
    (roughPrimeUniverse_nodup N cap w z)
    (fun p hp => mem_roughPrimeUniverse_prime hp) leaf hleaf

/-- Concrete modulus-lookup form: the raw leaf value is its retained integer
coefficient times the local-weight product over the modulus's prime factors. -/
theorem mem_roughPrimeRetainedLeaves_value_eq_coefficient_mul_primeFactors
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w z : ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h
      (roughPrimeUniverse N cap w z)) :
    leaf.value =
      (oddFirstExitRetainedCoefficient retainOdd h
        (roughPrimeUniverse N cap w z) leaf.selected.prod : ℝ) *
        leaf.selected.prod.primeFactors.prod h := by
  exact
    mem_oddFirstExitRetainedLeaves_value_eq_coefficient_mul_primeFactors
      retainOdd h (roughPrimeUniverse N cap w z)
      (roughPrimeUniverse_nodup N cap w z)
      (fun p hp => mem_roughPrimeUniverse_prime hp) leaf hleaf

/-- On the concrete decreasing rough-prime universe, the entire retained
branch sum is exactly the natural-modulus `Finset.sum`.  Every modulus occurs
once; the source-list and selected-product `Nodup` proofs justify the lossless
reindex. -/
theorem roughPrimeRetainedLeaves_sum_eq_retainedModuli_sum
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w z : ℝ) :
    ((oddFirstExitRetainedLeaves retainOdd h
      (roughPrimeUniverse N cap w z)).map FirstExitLeaf.value).sum =
      ∑ d ∈ oddFirstExitRetainedModuli retainOdd h
          (roughPrimeUniverse N cap w z),
        (oddFirstExitRetainedCoefficient retainOdd h
          (roughPrimeUniverse N cap w z) d : ℝ) *
          d.primeFactors.prod h := by
  exact oddFirstExitRetainedLeaves_sum_eq_retainedModuli_sum
    retainOdd h (roughPrimeUniverse N cap w z)
    (roughPrimeUniverse_nodup N cap w z)
    (fun p hp => mem_roughPrimeUniverse_prime hp)

/-- The generic integer pointwise majorant, now stated over precisely the
manuscript's real half-open rough-prime range.  The enumeration cap is absent
from the indicator because `hzcap` proves it is semantically inert. -/
theorem manuscriptRoughIndicator_le_oddFirstExitRetainedPolynomial
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    (@ite ℝ
      (∀ p,
        (p.Prime ∧ ¬p ∣ N ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z) →
          ¬(p : ℤ) ∣ n)
      (Classical.propDecidable _)
      1 0) ≤
      oddFirstExitRetainedPolynomial retainOdd
        (integerDivisorIndicator n) (roughPrimeUniverse N cap w z) := by
  classical
  simpa only [mem_roughPrimeUniverse_iff_of_cutoff_le_cap hzcap] using
    integerRoughIndicator_le_oddFirstExitRetainedPolynomial retainOdd
      (roughPrimeUniverse N cap w z) n

end

end ImbalancedChen
