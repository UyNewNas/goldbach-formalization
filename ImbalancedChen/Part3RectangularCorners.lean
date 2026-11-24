import ImbalancedChen.Part3RectangularAbel

/-!
# Corner expansion of the rectangular forward difference

The coordinate set with `y i < hi i` lists exactly the directions where a
successor is still in the rectangle. Expanding the incidences therefore
retains the forward differences on these coordinates and the boundary value
on the other coordinates.
-/

namespace ImbalancedChen.Part3.RectangularAbel

noncomputable section

open Classical Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

private def corner (y : ι → ℕ) (T : Finset ι) : ι → ℕ :=
  fun i => y i + if i ∈ T then 1 else 0

private theorem prod_edgeKernel_eq_corners (y z : ι → ℕ) :
    (∏ i, edgeKernel (y i) (z i)) =
      ∑ T ∈ (univ : Finset ι).powerset,
        (-1 : ℂ) ^ T.card * (if corner y T = z then 1 else 0) := by
  unfold edgeKernel
  rw [Finset.prod_sub]
  apply sum_congr rfl
  intro T _
  rw [mul_assoc]
  congr 1
  calc
    _ = ∏ i, (if i ∈ T then (if y i + 1 = z i then 1 else 0)
          else (if y i = z i then 1 else 0) : ℂ) := by
      rw [prod_ite (s := (univ : Finset ι)) (p := fun i => i ∈ T),
        filter_mem_eq_inter, univ_inter, filter_notMem_eq_sdiff, mul_comm]
    _ = ∏ i, (if corner y T i = z i then 1 else 0 : ℂ) := by
      apply prod_congr rfl
      intro i _
      by_cases hi : i ∈ T <;> simp [corner, hi]
    _ = _ := by simp only [Fintype.prod_boole, ← funext_iff]

private theorem corner_mem_rectangle_iff {lo hi y : ι → ℕ} (hy : y ∈ rectangle lo hi)
    (T : Finset ι) :
    corner y T ∈ rectangle lo hi ↔ T ⊆ (univ : Finset ι).filter (fun i => y i < hi i) := by
  obtain ⟨hylo, hyhi⟩ := mem_rectangle.mp hy
  rw [mem_rectangle]
  constructor
  · intro h i hiT
    refine mem_filter.mpr ⟨mem_univ i, Nat.succ_le_iff.mp ?_⟩
    simpa only [corner, if_pos hiT] using h.2 i
  · intro h
    refine ⟨fun i => (hylo i).trans (Nat.le_add_right _ _), fun i => ?_⟩
    by_cases hiT : i ∈ T
    · simpa only [corner, if_pos hiT] using Nat.succ_le_iff.mpr (mem_filter.mp (h hiT)).2
    · simpa only [corner, if_neg hiT, add_zero] using hyhi i

/-- The exact signed corner expansion uses only successors inside the
rectangle, so it also applies at upper boundary points. -/
theorem mixedDifference_eq_corner_sum (lo hi : ι → ℕ) (w : (ι → ℕ) → ℂ)
    {y : ι → ℕ} (hy : y ∈ rectangle lo hi) :
    mixedDifference lo hi w y =
      ∑ T ∈ ((univ : Finset ι).filter (fun i => y i < hi i)).powerset,
        (-1 : ℂ) ^ T.card * w (fun i => y i + if i ∈ T then 1 else 0) := by
  change _ = ∑ T ∈ ((univ : Finset ι).filter (fun i => y i < hi i)).powerset,
    (-1 : ℂ) ^ T.card * w (corner y T)
  unfold mixedDifference
  simp only [prod_edgeKernel_eq_corners, mul_sum]
  rw [sum_comm]
  have hset : ((univ : Finset ι).powerset.filter (fun T => corner y T ∈ rectangle lo hi)) =
      ((univ : Finset ι).filter (fun i => y i < hi i)).powerset := by
    ext T
    simp only [mem_filter, mem_powerset, subset_univ, true_and, corner_mem_rectangle_iff hy T]
  rw [← hset, sum_filter]
  apply sum_congr rfl
  intro T _
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq]
  split_ifs
  · exact mul_comm _ _
  · rfl

end

end ImbalancedChen.Part3.RectangularAbel
