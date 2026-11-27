import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-! Uncompiled exact extraction candidate. No formal credit. -/
namespace ImbalancedChen.Part3
noncomputable section
open Classical
open scoped BigOperators
namespace CommonSmoothCutoff

theorem poisson_decay_step {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t / (1 + t * (n + 1)) ^ 2 ≤
      1 / (1 + t * n) - 1 / (1 + t * (n + 1)) := by
  have hA : 0 < 1 + t * (n : ℝ) := by positivity
  have hB : 0 < 1 + t * ((n : ℝ) + 1) := by positivity
  calc
    _ ≤ t / ((1 + t * n) * (1 + t * (n + 1))) := by
      apply div_le_div_of_nonneg_left ht.le (mul_pos hA hB)
      nlinarith
    _ = _ := by field_simp; ring

theorem poisson_decay_sum_range_le {t : ℝ} (ht : 0 < t) (N : ℕ) :
    (∑ n ∈ Finset.range N, t / (1 + t * ((n : ℝ) + 1)) ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        (1 / (1 + t * (n : ℝ)) - 1 / (1 + t * ((n : ℝ) + 1))) :=
      Finset.sum_le_sum (fun n _ ↦ poisson_decay_step ht n)
    _ = 1 - 1 / (1 + t * (N : ℝ)) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero, div_one]
        using Finset.sum_range_sub' (fun n : ℕ ↦ 1 / (1 + t * (n : ℝ))) N
    _ ≤ 1 := sub_le_self _ (by positivity)

theorem poisson_decay_summable_nat {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ ↦ t / (1 + t * ((n : ℝ) + 1)) ^ 2) :=
  summable_of_sum_range_le (fun _ ↦ by positivity) (poisson_decay_sum_range_le ht)

theorem poisson_decay_tsum_nat_le {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, t / (1 + t * ((n : ℝ) + 1)) ^ 2) ≤ 1 :=
  Real.tsum_le_of_sum_range_le (fun _ ↦ by positivity) (poisson_decay_sum_range_le ht)

def poissonNonzeroDecay (t : ℝ) (h : ℤ) : ℝ :=
  if h = 0 then 0 else t / (1 + |t * h|) ^ 2

theorem poissonNonzeroDecay_summable_tsum_le {t : ℝ} (ht : 0 < t) :
    Summable (poissonNonzeroDecay t) ∧ (∑' h : ℤ, poissonNonzeroDecay t h) ≤ 2 := by
  let a : ℕ → ℝ := fun n ↦ t / (1 + t * ((n : ℝ) + 1)) ^ 2
  have ha : Summable a := poisson_decay_summable_nat ht
  have hbound : (∑' n : ℕ, a n) ≤ 1 := poisson_decay_tsum_nat_le ht
  have hnat (n : ℕ) : poissonNonzeroDecay t ((n : ℤ) + 1) = a n := by
    have hn : (n : ℤ) + 1 ≠ 0 := by omega
    simp [poissonNonzeroDecay, hn, abs_mul, abs_of_pos ht,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1), a]
  have hneg (n : ℕ) : poissonNonzeroDecay t (-((n : ℤ) + 1)) = a n := by
    simpa only [poissonNonzeroDecay, neg_eq_zero, Int.cast_neg, mul_neg, abs_neg]
      using hnat n
  have hpos : Summable (fun n : ℕ ↦ poissonNonzeroDecay t (n : ℤ)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one, hnat] using ha
  have hminus : Summable (fun n : ℕ ↦ poissonNonzeroDecay t (-((n : ℤ) + 1))) := by
    simpa only [hneg] using ha
  refine ⟨hpos.of_nat_of_neg_add_one hminus, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hpos hminus, tsum_eq_zero_add']
  · simp only [Nat.cast_zero, show poissonNonzeroDecay t 0 = 0 from rfl,
      zero_add, Nat.cast_add, Nat.cast_one, hnat, hneg]
    linarith
  · simpa only [Nat.cast_add, Nat.cast_one, hnat] using ha

end CommonSmoothCutoff
end
end ImbalancedChen.Part3
