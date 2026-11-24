import ImbalancedChen.Part3RectangularCorners
import ImbalancedChen.Part3MixedFiniteDifference
import Mathlib.Analysis.Complex.Basic

/-!
# Rectangular partial summation for a smooth sampled weight

The arithmetic array is arbitrary. The smooth weight on the grid is
evaluated at the sum of the individual coordinate vectors. A convex
set containing the sample points contains every interpolation box.
-/

namespace ImbalancedChen.Part3.RectangularAbel

noncomputable section

open Classical Finset Set
open scoped BigOperators ContDiff

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem sum_shiftedSample_eq (p : ι → ℕ → E) (y : ι → ℕ) (T : Finset ι) :
    (∑ i, p i (y i + if i ∈ T then 1 else 0)) =
      (∑ i, p i (y i)) + ∑ i ∈ T, (p i (y i + 1) - p i (y i)) := by
  have hT : univ.filter (fun i => i ∈ T) = T := by ext i; simp
  rw [← hT, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ T <;> simp [hi]

/-- A mixed difference of samples is controlled by the norm of the
derivatives and the product of the actual neighboring step lengths. -/
theorem norm_sampledMixedDifference_le
    (lo hi : ι → ℕ) (p : ι → ℕ → E) (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (S : Set E) (hS : Convex ℝ S) (C : ℝ)
    (hP : ∀ z ∈ rectangle lo hi, (∑ i, p i (z i)) ∈ S)
    (hD : ∀ j ≤ Fintype.card ι, ∀ z ∈ S, ‖iteratedFDeriv ℝ j f z‖ ≤ C)
    {y : ι → ℕ} (hy : y ∈ rectangle lo hi) :
    ‖mixedDifference lo hi (fun z => f (∑ i, p i (z i))) y‖ ≤
      C * ∏ i, if y i = hi i then 1 else ‖p i (y i + 1) - p i (y i)‖ := by
  let active := (univ : Finset ι).filter (fun i => y i < hi i)
  let v (i : ι) := p i (y i + 1) - p i (y i)
  let x := ∑ i, p i (y i)
  let steps := active.toList.map v
  have hverts (T : Finset ι) (hT : T ⊆ active.toList.toFinset) : x + ∑ i ∈ T, v i ∈ S := by
    have hT' : T ⊆ active := by simpa only [toList_toFinset] using hT
    have hz : (fun i => y i + if i ∈ T then 1 else 0) ∈ rectangle lo hi := by
      obtain ⟨hlo, hhi⟩ := mem_rectangle.mp hy
      apply mem_rectangle.mpr
      constructor
      · intro i
        exact (hlo i).trans (Nat.le_add_right _ _)
      · intro i
        by_cases hm : i ∈ T
        · have hlt := (mem_filter.mp (hT' hm)).2
          simpa only [if_pos hm] using Nat.succ_le_of_lt hlt
        · simpa only [if_neg hm, add_zero] using hhi i
    have h := hP _ hz
    rwa [sum_shiftedSample_eq] at h
  have hbox := displacementBox_mem_convex_of_vertices active.toList
    (nodup_toList _) v x S hS hverts
  have hsize : steps.length ≤ Fintype.card ι := by
    simp only [steps, List.length_map, length_toList]
    exact card_le_univ _
  have hd := norm_listDifference_le steps f hf x S C hbox
    (fun j hj => hD j (hj.trans hsize))
  have hEq : mixedDifference lo hi (fun z => f (∑ i, p i (z i))) y =
      listDifference steps f x := by
    rw [mixedDifference_eq_corner_sum _ _ _ hy,
      listDifference_eq_sum_subsets _ (nodup_toList _) v f x, toList_toFinset]
    apply sum_congr rfl
    intro T _
    rw [sum_shiftedSample_eq]
    simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, x, v]
  rw [hEq]
  apply hd.trans_eq
  simp only [steps, List.map_map, prod_map_toList, Function.comp_apply, active, prod_filter]
  congr 1
  apply prod_congr rfl
  intro i _
  rcases lt_or_eq_of_le ((mem_rectangle.mp hy).2 i) with h | h
  · simp only [if_pos h, if_neg h.ne, v]
  · simp only [h, lt_self_iff_false, if_false, if_true]

/-- The exact variation bound on the sampled rectangular sum. There is one
boundary term and the sum of step lengths in each coordinate. -/
theorem norm_sum_sampledRectangle_le
    (lo hi : ι → ℕ) (hlo : lo ≤ hi) (p : ι → ℕ → E)
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (S : Set E) (hS : Convex ℝ S)
    (b : (ι → ℕ) → ℂ) {B C : ℝ} (hB0 : 0 ≤ B)
    (hP : ∀ z ∈ rectangle lo hi, (∑ i, p i (z i)) ∈ S)
    (hD : ∀ j ≤ Fintype.card ι, ∀ z ∈ S, ‖iteratedFDeriv ℝ j f z‖ ≤ C)
    (hB : ∀ y ∈ rectangle lo hi, ‖∑ x ∈ rectangle lo y, b x‖ ≤ B) :
    ‖∑ x ∈ rectangle lo hi, b x * f (∑ i, p i (x i))‖ ≤
      C * (∏ i, (1 + ∑ j ∈ Ico (lo i) (hi i), ‖p i (j + 1) - p i j‖)) * B :=
  norm_sum_rectangle_mul_le_of_productVariation lo hi b _ hB0
    (fun i j => ‖p i (j+1) - p i j‖) hlo hB
    (fun _ hy => norm_sampledMixedDifference_le lo hi p f hf S hS C hP hD hy)

private theorem sum_Ico_forward_sub (g : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∑ j ∈ Ico a b, (g (j + 1) - g j)) = g b - g a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [sum_Ico_succ_top hn, ih]; ring

/-- For monotone scalar coordinates on directions of norm at most one,
the exact rectangular variation pays only the endpoint lengths. -/
theorem norm_sum_scalarGrid_le
    (lo hi : ι → ℕ) (hlo : lo ≤ hi)
    (p : ι → ℕ → ℝ) (v : ι → E) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hm : ∀ i, MonotoneOn (p i) (Set.Icc (lo i) (hi i)))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (S : Set E) (hS : Convex ℝ S)
    (b : (ι → ℕ) → ℂ) {B C L : ℝ} (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hL : ∀ i, p i (hi i) - p i (lo i) ≤ L)
    (hP : ∀ z ∈ rectangle lo hi, (∑ i, p i (z i) • v i) ∈ S)
    (hD : ∀ j ≤ Fintype.card ι, ∀ z ∈ S, ‖iteratedFDeriv ℝ j f z‖ ≤ C)
    (hB : ∀ y ∈ rectangle lo hi, ‖∑ x ∈ rectangle lo y, b x‖ ≤ B) :
    ‖∑ x ∈ rectangle lo hi, b x * f (∑ i, p i (x i) • v i)‖ ≤
      C * (1 + L) ^ Fintype.card ι * B := by
  have h := norm_sum_sampledRectangle_le lo hi hlo (fun i j => p i j • v i) f hf S hS
    b hB0 hP hD hB
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC0) hB0)
  have heq : (∏ _i : ι, (1 + L)) = (1 + L) ^ Fintype.card ι := by simp
  rw [← heq]
  apply prod_le_prod
  · intro i _
    positivity
  · intro i _
    gcongr
    calc
      _ ≤ ∑ j ∈ Ico (lo i) (hi i), (p i (j + 1) - p i j) := by
        apply sum_le_sum
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        have hmon := hm i ⟨hj'.1, hj'.2.le⟩ ⟨hj'.1.trans (Nat.le_succ _), Nat.succ_le_of_lt hj'.2⟩
          (Nat.le_succ _)
        rw [← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hmon)]
        exact mul_le_of_le_one_right (sub_nonneg.mpr hmon) (hv i)
      _ = _ := sum_Ico_forward_sub (p i) _ _ (hlo i)
      _ ≤ _ := hL i

end

end ImbalancedChen.Part3.RectangularAbel
