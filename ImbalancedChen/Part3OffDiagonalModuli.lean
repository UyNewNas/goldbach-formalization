import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Divisors

namespace ImbalancedChen.Part3

open scoped BigOperators

/-- For unequal complete products, congruence moduli are precisely the divisors
of their natural distance. -/
theorem modEq_iff_mem_divisors_dist {q b N : ℕ} (h : b ≠ N) :
    b ≡ N [MOD q] ↔ q ∈ (Nat.dist b N).divisors := by
  rw [Nat.mem_divisors, and_iff_left (Nat.dist_pos_of_ne h).ne']
  rcases le_total b N with hle | hle
  · rw [Nat.dist_eq_sub_of_le hle, Nat.modEq_iff_dvd' hle]
  · rw [Nat.dist_eq_sub_of_le_right hle, ← Nat.modEq_iff_dvd' hle]
    exact ⟨Nat.ModEq.symm, Nat.ModEq.symm⟩

/-- Restrict the divisor finset to the original set of moduli. -/
theorem filter_modEq_eq_inter_divisors_dist (Q : Finset ℕ) {b N : ℕ} (h : b ≠ N) :
    Q.filter (fun q => b ≡ N [MOD q]) = Q ∩ (Nat.dist b N).divisors := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_inter, modEq_iff_mem_divisors_dist h]

theorem card_filter_modEq_le_card_divisors_dist (Q : Finset ℕ) {b N : ℕ} (h : b ≠ N) :
    (Q.filter (fun q => b ≡ N [MOD q])).card ≤ (Nat.dist b N).divisors.card := by
  rw [filter_modEq_eq_inter_divisors_dist Q h]
  exact Finset.card_le_card Finset.inter_subset_right

/-- Any nonnegative weight on the congruence moduli is bounded by its divisor sum. -/
theorem sum_filter_modEq_le_sum_divisors_dist {R : Type*} [AddCommMonoid R]
    [PartialOrder R] [IsOrderedAddMonoid R] (Q : Finset ℕ) {b N : ℕ} (h : b ≠ N)
    (w : ℕ → R) (hw : ∀ q, 0 ≤ w q) :
    (∑ q ∈ Q.filter (fun q => b ≡ N [MOD q]), w q) ≤
      ∑ q ∈ (Nat.dist b N).divisors, w q := by
  rw [filter_modEq_eq_inter_divisors_dist Q h]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun q _ _ => hw q)

/-- A weight bounded on the original moduli costs at most one copy of its bound
per divisor of the off-diagonal distance. -/
theorem sum_filter_modEq_le_card_divisors_dist_nsmul {R : Type*} [AddCommMonoid R]
    [PartialOrder R] [IsOrderedAddMonoid R] (Q : Finset ℕ) {b N : ℕ} (h : b ≠ N)
    (w : ℕ → R) {C : R} (hC : 0 ≤ C) (hw : ∀ q ∈ Q, w q ≤ C) :
    (∑ q ∈ Q.filter (fun q => b ≡ N [MOD q]), w q) ≤
      (Nat.dist b N).divisors.card • C := by
  calc
    _ ≤ ∑ q ∈ Q.filter (fun q => b ≡ N [MOD q]), C :=
      Finset.sum_le_sum fun q hq => hw q (Finset.mem_filter.mp hq).1
    _ ≤ _ := by
      rw [Finset.sum_const]
      exact nsmul_le_nsmul_left hC (card_filter_modEq_le_card_divisors_dist Q h)

/-- Exact weighted count, including the complete-product diagonal. -/
theorem sum_modEq_eq_sum_inter_divisors_dist {R : Type*} [AddCommMonoid R]
    (Q : Finset ℕ) (b N : ℕ) (w : ℕ → R) :
    (∑ q ∈ Q, if b ≡ N [MOD q] then w q else 0) =
      if b = N then ∑ q ∈ Q, w q else ∑ q ∈ Q ∩ (Nat.dist b N).divisors, w q := by
  by_cases h : b = N
  · subst b
    simp [Nat.ModEq.refl]
  · rw [if_neg h, ← Finset.sum_filter, filter_modEq_eq_inter_divisors_dist Q h]

end ImbalancedChen.Part3
