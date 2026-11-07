import ImbalancedChen.Part5OriginalH430LiteralLogBinding
import ImbalancedChen.Part5OriginalH430ClosedOwner
import ImbalancedChen.Part5RenewalTablePrimitive

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original per-product integer suffix is a LOWER enclosure for the
actual closed-table integral. No analytic H/h count licence is needed.
The earlier scalar-AE primitive supplies the integral identity; it is
never used to discard a knot in an arithmetic prime sum.
-/
namespace ImbalancedChen.Part5OriginalH430SuffixIntegral

noncomputable section
open Set
open scoped Classical BigOperators
open P2Selected430LiteralActionData (logWeights q)
open P2Selected430CausalOccurrenceExporter
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5UpperTables.Renewal
open P5OriginalFeedbackTableKernels
open Part5OriginalH430ClosedOwner Part5OriginalH430LiteralLogBinding

/-- This is only a reindexing; no sign, monotonicity or convergence is
needed. All suffix positions appear exactly once. -/
theorem sum_range_suffix {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) {k : ℕ} (hk : k ≤ 200) :
    (∑ j ∈ Finset.range (200-k), f (k+j)) =
      ∑ i : Fin 200, if k ≤ i.val then f i.val else 0 := by
  calc
    _ = ∑ i ∈ (Finset.univ : Finset (Fin 200)).filter (fun i => k ≤ i.val), f i.val := by
      refine Finset.sum_bij
        (fun j hj => (⟨k+j, by have := Finset.mem_range.mp hj; omega⟩ : Fin 200))
        ?_ ?_ ?_ ?_
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩
      · intro j hj l hl he
        have hv := congrArg Fin.val he
        dsimp at hv
        omega
      · intro i hi
        have hki := (Finset.mem_filter.mp hi).2
        refine ⟨i.val-k, Finset.mem_range.mpr (by have := i.isLt; omega), ?_⟩
        apply Fin.ext
        dsimp
        omega
      · intro j hj
        rfl
    _ = _ := by rw [Finset.sum_filter]

/-- Preserve the stored coefficient and EVERY integer division. -/
theorem suffix_eq_fin_sum (old : Table) (up : Bool) {k : ℕ} (hk : k ≤ 200) :
    suffix old up k = ∑ i : Fin 200,
      if k ≤ i.val then old up i*logWeights i/q else 0 := by
  unfold suffix
  rw [sum_range_suffix _ hk]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : k ≤ i.val
  · simp only [if_pos hi, read, dif_pos i.isLt]
  · simp only [if_neg hi]

/-- Exact primitive at any suffix grid knot, including the empty k=200
case. This remains an identity for arbitrary SIGNED old arrays. -/
theorem tableTail_at_grid (nums : Fin 200 → ℤ) {k : ℕ} (hk : k ≤ 200) :
    tableTail nums (floorGrid k) = ∑ i : Fin 200,
      if k ≤ i.val then
        floorValue nums i * Real.log (floorGrid (i.val+1)/floorGrid i.val) else 0 := by
  rw [tableTail_eq_finite_log]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : k ≤ i.val
  · have hc : clippedCellLeft i (floorGrid k) = floorGrid i.val := by
      rw [clippedCellLeft, max_eq_right (grid_mono hi),
        min_eq_right (grid_mono (Nat.le_succ _))]
    rw [if_pos hi, hc]
  · have hik : i.val+1 ≤ k := by omega
    have hc : clippedCellLeft i (floorGrid k) = floorGrid (i.val+1) := by
      rw [clippedCellLeft, max_eq_left (grid_mono (by omega : i.val ≤ k)),
        min_eq_left (grid_mono hik)]
    have hp : 0 < floorGrid (i.val+1) :=
      zero_lt_one.trans_le (grid_bounds (by omega : i.val+1 ≤ 200)).1
    simp only [if_neg hi, hc, div_self hp.ne', Real.log_one, mul_zero]

/-- No integral estimate is an input. Literal log soundness and product
flooring supply the whole oriented suffix comparison. -/
theorem suffix_le_tableTail (old : Table) (up : Bool) {k : ℕ}
    (hk : k ≤ 200) (hn : ∀ i, 0 ≤ old up i) :
    ((suffix old up k : ℤ) : ℝ)/(2:ℝ)^80 ≤ tableTail (old up) (floorGrid k) := by
  rw [suffix_eq_fin_sum old up hk, tableTail_at_grid _ hk]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : k ≤ i.val
  · simp only [if_pos hi]
    exact literal_product_le_log (hn i) i
  · simp only [if_neg hi, Int.cast_zero, zero_div, le_refl]

/-- Nonnegative old numerators suffice; no artificial upper bound one
on the actual 430 iterates is introduced. -/
theorem floorAtom_nonneg {nums : Fin 200 → ℤ} (hn : ∀ i, 0 ≤ nums i)
    (b : FloorAtom) : 0 ≤ floorAtomValue nums b := by
  rw [atomOwner_value]
  exact div_nonneg (by exact_mod_cast hn (atomOwner nums b)) (by positivity)

theorem tableFunction_nonneg {nums : Fin 200 → ℤ} (hn : ∀ i, 0 ≤ nums i)
    (lower : Bool) (s : ℝ) : 0 ≤ tableFunction lower nums s := by
  unfold tableFunction
  apply Finset.sum_nonneg
  intro b _
  by_cases hb : s ∈ tableAtomSet lower b
  · rw [indicator_of_mem hb]
    exact floorAtom_nonneg hn b
  · simp only [indicator_of_notMem hb, le_refl]

/-- A moving start shrinks a nonnegative old-table tail. The exact
clipped-log formula also covers empty tails beyond five. -/
theorem tableTail_antitone {nums : Fin 200 → ℤ} (hn : ∀ i, 0 ≤ nums i) :
    Antitone (tableTail nums) := by
  intro c d hcd
  rw [tableTail_eq_finite_log, tableTail_eq_finite_log]
  apply Finset.sum_le_sum
  intro i _
  have hc : 0 < clippedCellLeft i c :=
    zero_lt_one.trans_le (clippedCellLeft_bounds i c).1
  have hd : 0 < clippedCellLeft i d :=
    zero_lt_one.trans_le (clippedCellLeft_bounds i d).1
  have hg : 0 < floorGrid (i.val+1) :=
    zero_lt_one.trans_le (grid_bounds (by omega : i.val+1 ≤ 200)).1
  have hden : clippedCellLeft i c ≤ clippedCellLeft i d :=
    min_le_min le_rfl (max_le_max hcd le_rfl)
  have hlog := Real.log_le_log (div_pos hg hd)
    (div_le_div_of_nonneg_left hg.le hc hden)
  exact mul_le_mul_of_nonneg_left hlog
    (div_nonneg (by exact_mod_cast hn i) (by positivity))

end
end ImbalancedChen.Part5OriginalH430SuffixIntegral
