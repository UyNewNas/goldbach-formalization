import ImbalancedChen.CurrentChenUpsilon6ProductRestriction

/-!
# Literal ordinary sixth-row selectors and counts

The arithmetic source is a strict inner subset of the actual sixth pair
carrier, with the same real sieve cutoff and no deletion mask. Every
comparison below drops only nonnegative actual quotient-source counts.
These finite comparisons assert no arithmetic limit or sieve estimate.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical

/-- An actual inner selector. Both extra walls are strict; the retained
source outside these walls is unchanged. -/
def currentChenUpsilon6OrdinarySelector (N : ℕ) (eta : ℝ) : Finset (ℕ × ℕ) :=
  (currentChenUpsilon6RetainedSelector N (fun _ => False) eta).filter
    (fun t => (N : ℝ) ^ (19 / 125 : ℝ) < (t.2 : ℝ) ∧
      ((t.1 * t.2 : ℕ) : ℝ) < (N : ℝ) ^ ((833 / 2500 : ℝ) - eta))

/-- The original actual sifted quotient cards with their pair labels
and their original real sieve cutoff. -/
def currentChenUpsilon6OrdinaryCount (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
    ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
      ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)

theorem currentChenUpsilon6OrdinarySelector_subset_retained (N : ℕ) (eta : ℝ) :
    currentChenUpsilon6OrdinarySelector N eta ⊆
      currentChenUpsilon6RetainedSelector N (fun _ => False) eta :=
  Finset.filter_subset _ _

theorem currentChenUpsilon6OrdinarySelector_subset_original (N : ℕ) (eta : ℝ) :
    currentChenUpsilon6OrdinarySelector N eta ⊆
      chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)) := by
  intro t ht
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp
    (currentChenUpsilon6OrdinarySelector_subset_retained N eta ht)).1).1

theorem currentChenUpsilon6OrdinaryCount_nonneg (N : ℕ) (eta : ℝ) :
    0 ≤ currentChenUpsilon6OrdinaryCount N eta :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- This finite comparison drops only nonnegative actual counts. It does
not assert that the arithmetic wall contribution is zero. -/
theorem currentChenUpsilon6OrdinaryCount_le_retained (N : ℕ) (eta : ℝ) :
    currentChenUpsilon6OrdinaryCount N eta ≤
      currentChenUpsilon6Retained N (fun _ => False) eta :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (currentChenUpsilon6OrdinarySelector_subset_retained N eta)
    (fun _ _ _ => Nat.cast_nonneg _)

/-- The unmasked ordinary inner source gives a lower bound for the
unmasked actual sixth row, for every real buffer parameter. -/
theorem currentChenUpsilon6OrdinaryCount_le_currentChenUpsilon6_false
    (N : ℕ) (eta : ℝ) :
    currentChenUpsilon6OrdinaryCount N eta ≤
      currentChenUpsilon6 N (fun _ => False) :=
  (currentChenUpsilon6OrdinaryCount_le_retained N eta).trans
    (currentChenUpsilon6Retained_le N (fun _ => False) eta)

end

end ImbalancedChen
