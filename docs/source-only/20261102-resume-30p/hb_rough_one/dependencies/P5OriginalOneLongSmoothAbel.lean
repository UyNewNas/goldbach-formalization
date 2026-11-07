import ImbalancedChen.P5OriginalOneLongSharpBrun
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Calculus.MeanValue

-- UNCOMPILED_ZERO_CREDIT. Original section 7 smooth profiles and section 9
-- individual sharp intervals. Finite Abel summation retains BOTH arithmetic
-- kernels. The variation is charged once, independently of every sieve divisor.

namespace ImbalancedChen
namespace OriginalOneLongSmoothAbel

noncomputable section
open Finset
open scoped BigOperators
open OriginalOneLongFiniteBrun OriginalOneLongSharpBrun

def variation (K : ℕ) (f : ℕ → ℂ) : ℝ :=
  ‖f (K - 1)‖ + ∑ j ∈ range (K - 1), ‖f (j + 1) - f j‖

-- Exact complex Abel estimate; the bound is for each literal prefix interval.
theorem finite_abel_norm_le (K : ℕ) (f c : ℕ → ℂ) (E : ℝ)
    (hprefix : ∀ k ≤ K, ‖∑ j ∈ range k, c j‖ ≤ E) :
    ‖∑ j ∈ range K, f j * c j‖ ≤ E * variation K f := by
  have hid := Finset.sum_range_by_parts (R := ℂ) (M := ℂ) f c K
  simp only [smul_eq_mul] at hid
  rw [hid]
  calc
    _ ≤ ‖f (K - 1) * ∑ j ∈ range K, c j‖ +
        ‖∑ i ∈ range (K - 1), (f (i + 1) - f i) * ∑ j ∈ range (i + 1), c j‖ :=
      norm_sub_le _ _
    _ ≤ ‖f (K - 1)‖ * E +
        ∑ i ∈ range (K - 1), ‖(f (i + 1) - f i) * ∑ j ∈ range (i + 1), c j‖ := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix K le_rfl) (norm_nonneg _)
      · exact norm_sum_le _ _
    _ ≤ ‖f (K - 1)‖ * E +
        ∑ i ∈ range (K - 1), ‖f (i + 1) - f i‖ * E := by
      apply add_le_add_left
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hprefix (i + 1) (by
        have := mem_range.mp hi; omega)) (norm_nonneg _)
    _ = E * variation K f := by rw [← Finset.sum_mul]; unfold variation; ring

def sampled (F : ℝ → ℂ) (u : ℝ) (L : ℕ) (j : ℕ) : ℂ := F ((L + j : ℕ) / u)

-- The manuscript's compact smooth extension is defined on all real inputs.
-- Its amplitude and derivative bounds include admitted logarithms/twists.
-- These are profile norms, independent of d, q, m, primitive residue and endpoints.
theorem sampled_increment_norm_le (F : ℝ → ℂ) (u B : ℝ) (L j : ℕ)
    (hu : 0 < u) (hF : Differentiable ℝ F)
    (hderiv : ∀ x : ℝ, ‖deriv F x‖ ≤ B) :
    ‖sampled F u L (j + 1) - sampled F u L j‖ ≤ B / u := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hF x) (fun x _ => hderiv x)
    (Set.mem_univ (((L + j : ℕ) : ℝ) / u))
    (Set.mem_univ (((L + (j + 1) : ℕ) : ℝ) / u))
  have hstep : (((L + (j + 1) : ℕ) : ℝ) / u) - (((L + j : ℕ) : ℝ) / u) = 1 / u := by
    push_cast
    ring
  simpa [sampled, hstep, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hu), div_eq_mul_inv] using h

theorem sampled_variation_le (F : ℝ → ℂ) (u A B R : ℝ) (L K : ℕ)
    (hu : 0 < u) (hB : 0 ≤ B) (hF : Differentiable ℝ F)
    (hamplitude : ∀ x : ℝ, ‖F x‖ ≤ A)
    (hderiv : ∀ x : ℝ, ‖deriv F x‖ ≤ B) (hwidth : (K : ℝ) ≤ R * u) :
    variation K (sampled F u L) ≤ A + R * B := by
  have hsum : (∑ j ∈ range (K - 1),
      ‖sampled F u L (j + 1) - sampled F u L j‖) ≤ (K : ℝ) * (B / u) := by
    calc
      _ ≤ ∑ _j ∈ range (K - 1), B / u := Finset.sum_le_sum fun j hj =>
        sampled_increment_norm_le F u B L j hu hF hderiv
      _ = ((K - 1 : ℕ) : ℝ) * (B / u) := by simp
      _ ≤ (K : ℝ) * (B / u) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.sub_le K 1) (div_nonneg hB hu.le)
  have hwidth' : (K : ℝ) * (B / u) ≤ R * B := by
    have h := mul_le_mul_of_nonneg_right hwidth (div_nonneg hB hu.le)
    have he : (R * u) * (B / u) = R * B := by field_simp [hu.ne']; ring
    rw [he] at h
    exact h
  unfold variation
  exact add_le_add (hamplitude _) (hsum.trans hwidth')

def actualCoefficient (q a m primeProduct n : ℕ) : ℂ :=
  ((actualRough primeProduct n * (actualCount q a m n - actualMean q m n) : ℝ) : ℂ)

theorem actual_prefix_eq (L k q a m primeProduct : ℕ) :
    (∑ j ∈ range k, actualCoefficient q a m primeProduct (L + j)) =
      discrepancy (Ico L (L + k)) (actualCount q a m) (actualMean q m)
        (actualRough primeProduct) (fun _ => 1) := by
  unfold discrepancy actualCoefficient
  simp only [one_mul]
  rw [Finset.sum_Ico_eq_sum_range]
  simp

-- Actual complex smooth-long estimate obtained from the literal sharp-prefix
-- estimate. E is a UNIFORM sharp bound (supplied by Phase2), never a smooth
-- rough target. Normalized support width R is fixed before the scale grows.
theorem smooth_actual_one_long_of_sharp_prefix
    (L K q a m primeProduct : ℕ) (F : ℝ → ℂ) (u A B R E : ℝ)
    (hu : 0 < u) (hB : 0 ≤ B) (hE : 0 ≤ E) (hF : Differentiable ℝ F)
    (hamplitude : ∀ x : ℝ, ‖F x‖ ≤ A)
    (hderiv : ∀ x : ℝ, ‖deriv F x‖ ≤ B) (hwidth : (K : ℝ) ≤ R * u)
    (hsharp : ∀ k ≤ K,
      ‖discrepancy (Ico L (L + k)) (actualCount q a m) (actualMean q m)
        (actualRough primeProduct) (fun _ => 1)‖ ≤ E) :
    ‖∑ j ∈ range K, F (((L + j : ℕ) : ℝ) / u) *
      actualCoefficient q a m primeProduct (L + j)‖ ≤ E * (A + R * B) := by
  have hp (k : ℕ) (hk : k ≤ K) :
      ‖∑ j ∈ range k, actualCoefficient q a m primeProduct (L + j)‖ ≤ E := by
    rw [actual_prefix_eq]
    exact hsharp k hk
  exact (finite_abel_norm_le K (sampled F u L)
    (fun j => actualCoefficient q a m primeProduct (L + j)) E hp).trans
    (mul_le_mul_of_nonneg_left
      (sampled_variation_le F u A B R L K hu hB hF hamplitude hderiv hwidth) hE)

end
end OriginalOneLongSmoothAbel
end ImbalancedChen
