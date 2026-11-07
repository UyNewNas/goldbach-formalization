import ImbalancedChen.Part3SmoothIntegerUnitPartition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Seam-free unfolding for a merely measurable periodic function against the
actual compact integer unit partition. Its existing integer sums reduce
to two terms on [0,1]. Translation invariance of the genuine interval
integral then gives integral alpha*f = integral over one period f and
integral alpha'*f = 0. Only actual integrability of the compact products is
required; no trace, endpoint value, classical derivative or H1 seam input
is imposed on f.
-/
namespace ImbalancedChen.Part3.PeriodicCompactPartitionUnfolding20261026b
noncomputable section
open Set MeasureTheory Filter
open SmoothIntegerUnitPartition20261026b

private theorem two_term_integer_partition (χ : ℝ → ℝ) (c : ℝ)
    (hl : ∀ x ≤ -1, χ x = 0) (hr : ∀ x, 1 ≤ x → χ x = 0)
    (ht : ∀ x, (∑' k : ℤ, χ (x + (k : ℝ))) = c)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : χ x + χ (x - 1) = c := by
  classical
  have hf : ∀ k ∉ ({0, -1} : Finset ℤ), χ (x + (k : ℝ)) = 0 := by
    intro k hk
    have hk0 : k ≠ 0 := by intro h; apply hk; simp [h]
    have hk1 : k ≠ -1 := by intro h; apply hk; simp [h]
    have hc : k ≤ -2 ∨ 1 ≤ k := by omega
    rcases hc with h | h
    · have hcast : (k : ℝ) ≤ -2 := by exact_mod_cast h
      exact hl _ (by linarith [hx.2])
    · have hcast : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      exact hr _ (by linarith [hx.1])
  have h := ht x
  rw [tsum_eq_sum hf, Finset.sum_pair (by decide : (0 : ℤ) ≠ -1)] at h
  simpa only [Int.cast_zero, add_zero, Int.cast_neg, Int.cast_one, ← sub_eq_add_neg] using h

theorem partition_two_terms {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    horizontalUnitPartition x + horizontalUnitPartition (x - 1) = 1 :=
  two_term_integer_partition horizontalUnitPartition 1
    horizontalUnitPartition_zero_left horizontalUnitPartition_zero_right
    horizontalUnitPartition_integer_sum hx

theorem partition_derivative_zero_left (x : ℝ) (hx : x ≤ -1) :
    deriv horizontalUnitPartition x = 0 := by
  rw [horizontalUnitPartition_deriv, transition_deriv_nonpos _ (by linarith),
    transition_deriv_nonpos _ (by linarith), sub_self]

theorem partition_derivative_zero_right (x : ℝ) (hx : 1 ≤ x) :
    deriv horizontalUnitPartition x = 0 := by
  rw [horizontalUnitPartition_deriv, transition_deriv_one_le _ (by linarith),
    transition_deriv_one_le _ hx, sub_self]

theorem partition_derivative_two_terms {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv horizontalUnitPartition x + deriv horizontalUnitPartition (x - 1) = 0 :=
  two_term_integer_partition (deriv horizontalUnitPartition) 0
    partition_derivative_zero_left partition_derivative_zero_right
    horizontalUnitPartition_deriv_integer_sum hx

/-- Translation and the compact two-term partition are enough for
unfolding; f itself has no regularity or endpoint-trace premise. -/
theorem compact_periodic_weight_integral (χ : ℝ → ℝ) (c : ℝ)
    (hl : ∀ x ≤ -1, χ x = 0) (hr : ∀ x, 1 ≤ x → χ x = 0)
    (ht : ∀ x ∈ Icc (0 : ℝ) 1, χ x + χ (x - 1) = c)
    (f : ℝ → ℂ) (hp : Function.Periodic f 1)
    (hi : Integrable (fun x => (χ x : ℂ) * f x)) :
    (∫ x : ℝ, (χ x : ℂ) * f x) = (c : ℂ) * (∫ x in (0 : ℝ)..1, f x) := by
  have hfsub (x : ℝ) : f (x - 1) = f x := by
    simpa only [sub_add_cancel] using (hp (x - 1)).symm
  have hsupport : Function.support (fun x => (χ x : ℂ) * f x) ⊆ Ioc (-1 : ℝ) 1 := by
    intro x hx
    constructor
    · by_contra h
      exact hx (by rw [hl x (le_of_not_gt h)]; simp)
    · by_contra h
      exact hx (by rw [hr x (le_of_lt (lt_of_not_ge h))]; simp)
  have hshift : IntervalIntegrable (fun x => (χ (x - 1) : ℂ) * f x) volume 0 1 := by
    have h := (hi.intervalIntegrable (-1) 0).comp_sub_right 1
    simpa only [neg_add_cancel, zero_add, hfsub] using h
  have htranslate :
      (∫ x in (-1 : ℝ)..0, (χ x : ℂ) * f x) =
      ∫ x in (0 : ℝ)..1, (χ (x - 1) : ℂ) * f x := by
    have h := intervalIntegral.integral_comp_sub_right
      (fun x : ℝ => (χ x : ℂ) * f x) (a := 0) (b := 1) 1
    simpa only [zero_sub, sub_self, hfsub] using h.symm
  calc
    _ = ∫ x in (-1 : ℝ)..1, (χ x : ℂ) * f x :=
      (intervalIntegral.integral_eq_integral_of_support_subset hsupport).symm
    _ = (∫ x in (-1 : ℝ)..0, (χ x : ℂ) * f x) +
        (∫ x in (0 : ℝ)..1, (χ x : ℂ) * f x) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hi.intervalIntegrable (-1) 0) (hi.intervalIntegrable 0 1)).symm
    _ = ∫ x in (0 : ℝ)..1,
        (χ (x - 1) : ℂ) * f x + (χ x : ℂ) * f x := by
      rw [htranslate, intervalIntegral.integral_add hshift (hi.intervalIntegrable 0 1)]
    _ = ∫ x in (0 : ℝ)..1, (c : ℂ) * f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
      calc
        _ = ((χ x + χ (x - 1) : ℝ) : ℂ) * f x := by push_cast; ring
        _ = _ := by rw [ht x hx']
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem partition_unfold_periodic (f : ℝ → ℂ) (hp : Function.Periodic f 1)
    (hi : Integrable (fun x => (horizontalUnitPartition x : ℂ) * f x)) :
    (∫ x : ℝ, (horizontalUnitPartition x : ℂ) * f x) = ∫ x in (0 : ℝ)..1, f x := by
  simpa only [Complex.ofReal_one, one_mul] using
    compact_periodic_weight_integral horizontalUnitPartition 1
      horizontalUnitPartition_zero_left horizontalUnitPartition_zero_right
      (fun x hx => partition_two_terms hx) f hp hi

theorem partition_derivative_unfold_zero (f : ℝ → ℂ) (hp : Function.Periodic f 1)
    (hi : Integrable (fun x => (deriv horizontalUnitPartition x : ℂ) * f x)) :
    (∫ x : ℝ, (deriv horizontalUnitPartition x : ℂ) * f x) = 0 := by
  simpa only [Complex.ofReal_zero, zero_mul] using
    compact_periodic_weight_integral (deriv horizontalUnitPartition) 0
      partition_derivative_zero_left partition_derivative_zero_right
      (fun x hx => partition_derivative_two_terms hx) f hp hi

end
end ImbalancedChen.Part3.PeriodicCompactPartitionUnfolding20261026b
