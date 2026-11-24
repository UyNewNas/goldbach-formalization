import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Exact finite partial summation on a rectangle

The coefficient array is unchanged. Every prefix uses one simultaneous
choice of the coordinate endpoints. The forward differences include
the forced boundary terms, which are obtained by extending the weight
by zero at the upper faces.
-/

namespace ImbalancedChen.Part3.RectangularAbel

noncomputable section

open Classical Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The full Cartesian rectangle of natural index positions. -/
def rectangle (lo hi : ι → ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset (fun i => Icc (lo i) (hi i))

theorem mem_rectangle {lo hi x : ι → ℕ} :
    x ∈ rectangle lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  simp only [rectangle, Fintype.mem_piFinset, mem_Icc, Pi.le_def, forall_and]

private theorem rectangle_filter_above {lo hi x : ι → ℕ} (hx : lo ≤ x) :
    (rectangle lo hi).filter (fun y => x ≤ y) = rectangle x hi := by
  ext y
  rw [mem_filter, mem_rectangle, mem_rectangle]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hx.trans h.1, h.2⟩, h.1⟩⟩

private theorem rectangle_filter_below {lo hi x : ι → ℕ} (hx : x ≤ hi) :
    (rectangle lo hi).filter (fun y => y ≤ x) = rectangle lo x := by
  ext y
  rw [mem_filter, mem_rectangle, mem_rectangle]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hx⟩, h.2⟩⟩

/-- The signed edge incidence, pairing a position with its successor. -/
def edgeKernel (y z : ℕ) : ℂ :=
  (if y = z then 1 else 0) - (if y + 1 = z then 1 else 0)

private theorem sum_edgeKernel (a H z : ℕ) (hz : z ≤ H) :
    (∑ y ∈ Icc a H, edgeKernel y z) = if z = a then 1 else 0 := by
  simp only [edgeKernel, sum_sub_distrib, sum_ite_eq', mem_Icc, hz, and_true]
  by_cases hz0 : z = 0
  · subst z
    have hnot (y : ℕ) : ¬y + 1 = 0 := by omega
    simp only [hnot, if_false, sum_const_zero, sub_zero]
    by_cases ha : a = 0 <;> simp [ha, eq_comm]
  · have hstep (y : ℕ) : y + 1 = z ↔ y = z - 1 := by omega
    have hprev : z - 1 ≤ H := by omega
    simp only [hstep, sum_ite_eq', mem_Icc, hprev, and_true]
    split_ifs <;> norm_num <;> omega

/-- Full forward difference of the zero extension on the upper faces.
Every coordinate receives one difference, with the boundary value retained. -/
def mixedDifference (lo hi : ι → ℕ) (w : (ι → ℕ) → ℂ) (y : ι → ℕ) : ℂ :=
  ∑ z ∈ rectangle lo hi, w z * ∏ i, edgeKernel (y i) (z i)

private theorem prod_eq_pointIndicator (x z : ι → ℕ) :
    (∏ i, (if z i = x i then 1 else 0 : ℂ)) = if z = x then 1 else 0 := by
  by_cases h : z = x
  · subst z
    simp
  · have hi : ∃ i, z i ≠ x i := by
      simpa only [funext_iff, not_forall] using h
    obtain ⟨i, hi⟩ := hi
    have hz := prod_eq_zero (f := fun j => if z j = x j then (1 : ℂ) else 0) (mem_univ i)
      (show (if z i = x i then 1 else 0 : ℂ) = 0 by simp only [if_neg hi])
    rw [hz, if_neg h]

/-- Telescoping over the upper orthant recovers the original weight. -/
theorem sum_mixedDifference_rectangle (lo hi : ι → ℕ) (w : (ι → ℕ) → ℂ)
    {x : ι → ℕ} (hx : x ∈ rectangle lo hi) :
    (∑ y ∈ rectangle x hi, mixedDifference lo hi w y) = w x := by
  unfold mixedDifference
  rw [sum_comm]
  simp_rw [← mul_sum]
  calc
    _ = ∑ z ∈ rectangle lo hi, w z * (∏ i, if z i = x i then 1 else 0) := by
      apply sum_congr rfl
      intro z hz
      congr 1
      rw [rectangle, ← prod_univ_sum (fun i => Icc (x i) (hi i)) (fun i u => edgeKernel u (z i))]
      apply prod_congr rfl
      intro i _
      exact sum_edgeKernel (x i) (hi i) (z i) ((mem_rectangle.mp hz).2 i)
    _ = _ := by
      simp only [prod_eq_pointIndicator, mul_ite, mul_one, mul_zero, sum_ite_eq', hx, if_true]

/-- Exact multidimensional Abel summation, including every upper face. -/
theorem sum_rectangle_mul_eq (lo hi : ι → ℕ) (b w : (ι → ℕ) → ℂ) :
    (∑ x ∈ rectangle lo hi, b x * w x) =
      ∑ y ∈ rectangle lo hi, mixedDifference lo hi w y *
        (∑ x ∈ rectangle lo y, b x) := by
  calc
    _ = ∑ x ∈ rectangle lo hi, b x *
        (∑ y ∈ rectangle lo hi, if x ≤ y then mixedDifference lo hi w y else 0) := by
      apply sum_congr rfl
      intro x hx
      rw [← sum_filter, rectangle_filter_above (mem_rectangle.mp hx).1,
        sum_mixedDifference_rectangle lo hi w hx]
    _ = _ := by
      simp only [mul_sum, mul_ite, mul_zero]
      rw [sum_comm]
      apply sum_congr rfl
      intro y hy
      rw [← sum_filter, rectangle_filter_below (mem_rectangle.mp hy).2]
      apply sum_congr rfl
      intro x _
      exact mul_comm _ _

/-- A common prefix bound pays the exact total variation of the weight. -/
theorem norm_sum_rectangle_mul_le (lo hi : ι → ℕ) (b w : (ι → ℕ) → ℂ) (B : ℝ)
    (hB : ∀ y ∈ rectangle lo hi, ‖∑ x ∈ rectangle lo y, b x‖ ≤ B) :
    ‖∑ x ∈ rectangle lo hi, b x * w x‖ ≤
      (∑ y ∈ rectangle lo hi, ‖mixedDifference lo hi w y‖) * B := by
  rw [sum_rectangle_mul_eq, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun y hy => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB y hy) (norm_nonneg _)

/-- A pointwise product bound for the mixed differences gives the sum of
all edge variations, including one boundary contribution per coordinate. -/
theorem norm_sum_rectangle_mul_le_of_productVariation
    (lo hi : ι → ℕ) (b w : (ι → ℕ) → ℂ) {B C : ℝ} (hB0 : 0 ≤ B)
    (L : ι → ℕ → ℝ) (hbox : lo ≤ hi)
    (hB : ∀ y ∈ rectangle lo hi, ‖∑ x ∈ rectangle lo y, b x‖ ≤ B)
    (hvar : ∀ y ∈ rectangle lo hi, ‖mixedDifference lo hi w y‖ ≤
      C * ∏ i, if y i = hi i then 1 else L i (y i)) :
    ‖∑ x ∈ rectangle lo hi, b x * w x‖ ≤
      C * (∏ i, (1 + ∑ j ∈ Ico (lo i) (hi i), L i j)) * B := by
  refine (norm_sum_rectangle_mul_le lo hi b w B hB).trans ?_
  apply mul_le_mul_of_nonneg_right _ hB0
  calc
    _ ≤ ∑ y ∈ rectangle lo hi, C * ∏ i, if y i = hi i then 1 else L i (y i) :=
      sum_le_sum hvar
    _ = _ := by
      rw [← mul_sum, rectangle, ← prod_univ_sum (fun i => Icc (lo i) (hi i))
        (fun i j => if j = hi i then (1 : ℝ) else L i j)]
      congr 1
      apply prod_congr rfl
      intro i _
      have hm : hi i ∈ Icc (lo i) (hi i) := mem_Icc.mpr ⟨hbox i, le_rfl⟩
      rw [← sum_erase_add _ _ hm, Icc_erase_right, if_pos rfl, add_comm]
      congr 1
      apply sum_congr rfl
      intro j hj
      exact if_neg (mem_Ico.mp hj).2.ne

end

end ImbalancedChen.Part3.RectangularAbel
