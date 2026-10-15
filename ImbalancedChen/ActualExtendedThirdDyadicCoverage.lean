import ImbalancedChen.ActualExtendedThirdPhysicalCell
import Mathlib.Order.Interval.Set.Union

/-!
# Actual ownership and retention coverage for the extended-third dyadic cells

This is the literal dyadic grid of `ActualExtendedThirdPhysicalCell`, with
right-owned `[lo,hi)` intervals in all three coordinates. The closed ordered
portion used for the cap certificate contains its owned portion, including
points on either ordering wall. No ordered rectangle is silently discarded.

Every point below the actual first-stop wall by one mesh width has a unique
retained owner. Consequently the omitted points are confined to the explicit
strip `rho - 4e - mesh < x`. At fixed positive wall clearance, one sufficiently
fine common grid covers every point, including the ordering walls. The same
endpoint estimate controls the full-envelope dispatch at `mu - 4e`.

These are geometric coverage and diameter statements, not a density estimate
or a proof that the robust branch infima converge to the ideal envelope.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology MeasureTheory
open VariableEnvelope
open scoped Classical

def actualExtendedThirdDyadicStep (m : ℕ) : ℝ := thirdPrefixRho / (2 : ℝ) ^ m

theorem actualExtendedThirdDyadicStep_pos (m : ℕ) :
    0 < actualExtendedThirdDyadicStep m := by
  exact div_pos (by norm_num [thirdPrefixRho]) (by positivity)

theorem tendsto_actualExtendedThirdDyadicStep :
    Tendsto actualExtendedThirdDyadicStep atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show 0 ≤ (2 : ℝ)⁻¹ by norm_num) (show (2 : ℝ)⁻¹ < 1 by norm_num)
  change Tendsto (fun m : ℕ => thirdPrefixRho / (2 : ℝ) ^ m) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, inv_pow, mul_zero] using
    hp.const_mul thirdPrefixRho

theorem actualExtendedThirdDyadicHi_eq_lo_add_step (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) (i : Fin 3) :
    actualExtendedThirdDyadicHi m j i =
      actualExtendedThirdDyadicLo m j i + actualExtendedThirdDyadicStep m := by
  simp only [actualExtendedThirdDyadicHi, actualExtendedThirdDyadicLo,
    actualExtendedThirdDyadicStep, Nat.cast_add, Nat.cast_one]
  ring

theorem actualExtendedThirdDyadic_bounds (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) (i : Fin 3) :
    0 ≤ actualExtendedThirdDyadicLo m j i ∧
      actualExtendedThirdDyadicLo m j i < actualExtendedThirdDyadicHi m j i ∧
      actualExtendedThirdDyadicHi m j i ≤ thirdPrefixRho := by
  have hp : 0 < (2 : ℝ) ^ m := by positivity
  have hr : 0 ≤ thirdPrefixRho := by norm_num [thirdPrefixRho]
  have hn : ((j i).val + 1 : ℝ) ≤ (2 : ℝ) ^ m := by
    exact_mod_cast Nat.succ_le_of_lt (j i).isLt
  refine ⟨div_nonneg (mul_nonneg hr (Nat.cast_nonneg _)) hp.le, ?_, ?_⟩
  · rw [actualExtendedThirdDyadicHi_eq_lo_add_step]
    exact lt_add_of_pos_right _ (actualExtendedThirdDyadicStep_pos m)
  · unfold actualExtendedThirdDyadicHi
    apply (div_le_iff₀ hp).mpr
    simpa only [Nat.cast_add, Nat.cast_one] using mul_le_mul_of_nonneg_left hn hr

/-- Actual right ownership. The scalar cap is still certified on the closed
ordered portion, so equality on an ordering wall is included here. -/
def actualExtendedThirdOwnedCell (m : ℕ) (j : ActualExtendedThirdDyadicLabel m) :
    Set (Fin 3 → ℝ) :=
  Set.univ.pi (fun i => Ico (actualExtendedThirdDyadicLo m j i)
    (actualExtendedThirdDyadicHi m j i)) ∩ actualExtendedThirdClosedOrder

theorem measurableSet_actualExtendedThirdOwnedCell (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) :
    MeasurableSet (actualExtendedThirdOwnedCell m j) :=
  (MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).inter
    isClosed_actualExtendedThirdClosedOrder.measurableSet

theorem actualExtendedThirdOwnedCell_subset_physicalCell (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) :
    actualExtendedThirdOwnedCell m j ⊆ actualExtendedThirdPhysicalCell m j := by
  intro t ht
  exact ⟨fun i hi => ⟨(ht.1 i hi).1, (ht.1 i hi).2.le⟩, ht.2⟩

theorem actualExtendedThirdDyadicHi_le_point_add_step {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j) (i : Fin 3) :
    actualExtendedThirdDyadicHi m j i ≤ t i + actualExtendedThirdDyadicStep m := by
  rw [actualExtendedThirdDyadicHi_eq_lo_add_step]
  linarith [(ht.1 i (mem_univ _)).1]

/-- Every closed ordered portion has diameter at most one mesh width in the
actual `Fin 3` sup metric, including cells meeting either ordering wall. -/
theorem actualExtendedThirdPhysicalCell_dist_le_step {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {s t : Fin 3 → ℝ}
    (hs : s ∈ actualExtendedThirdPhysicalCell m j)
    (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    dist s t ≤ actualExtendedThirdDyadicStep m := by
  apply (dist_pi_le_iff (actualExtendedThirdDyadicStep_pos m).le).mpr
  intro i
  obtain ⟨hsl, hsh⟩ := hs.1 i (mem_univ _)
  obtain ⟨htl, hth⟩ := ht.1 i (mem_univ _)
  have he := actualExtendedThirdDyadicHi_eq_lo_add_step m j i
  rw [Real.dist_eq]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem exists_actualExtendedThirdDyadicInterval (m : ℕ) {x : ℝ}
    (hx : x ∈ Ico 0 thirdPrefixRho) :
    ∃ i : Fin (2 ^ m), x ∈ Ico (thirdPrefixRho * i.val / (2 : ℝ) ^ m)
      (thirdPrefixRho * (i.val + 1 : ℕ) / (2 : ℝ) ^ m) := by
  let p : ℕ → ℝ := fun i => thirdPrefixRho * i / (2 : ℝ) ^ m
  have hp : (2 : ℝ) ^ m ≠ 0 := by positivity
  have hx' : x ∈ Ico (p 0) (p (2 ^ m)) := by
    simpa [p, Nat.cast_pow, hp] using hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp
    (Ico_subset_biUnion_Ico (2 ^ m) p hx')
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, hxi⟩

theorem exists_actualExtendedThirdOwnedCell {m : ℕ} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdClosedOrder) (hx : t 0 < thirdPrefixRho) :
    ∃ j : ActualExtendedThirdDyadicLabel m, t ∈ actualExtendedThirdOwnedCell m j := by
  have hcoords : ∀ i : Fin 3, t i ∈ Ico 0 thirdPrefixRho := by
    intro i
    fin_cases i
    · exact ⟨ht.1.trans (ht.2.1.trans ht.2.2), hx⟩
    · exact ⟨ht.1.trans ht.2.1, ht.2.2.trans_lt hx⟩
    · exact ⟨ht.1, ht.2.1.trans_lt (ht.2.2.trans_lt hx)⟩
  choose j hj using fun i => exists_actualExtendedThirdDyadicInterval m (hcoords i)
  exact ⟨j, ⟨fun i _ => hj i, ht⟩⟩

theorem actualExtendedThirdOwnedCell_unique {m : ℕ}
    {j k : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (hj : t ∈ actualExtendedThirdOwnedCell m j)
    (hk : t ∈ actualExtendedThirdOwnedCell m k) : j = k := by
  have hp : 0 ≤ (2 : ℝ) ^ m := by positivity
  have hr : 0 ≤ thirdPrefixRho := by norm_num [thirdPrefixRho]
  funext i
  apply Fin.ext
  by_contra hi
  rcases lt_or_gt_of_ne hi with h | h
  · have hsep : actualExtendedThirdDyadicHi m j i ≤ actualExtendedThirdDyadicLo m k i := by
      apply div_le_div_of_nonneg_right ?_ hp
      apply mul_le_mul_of_nonneg_left _ hr
      exact_mod_cast Nat.succ_le_of_lt h
    exact (not_lt_of_ge hsep) ((hk.1 i (mem_univ _)).1.trans_lt (hj.1 i (mem_univ _)).2)
  · have hsep : actualExtendedThirdDyadicHi m k i ≤ actualExtendedThirdDyadicLo m j i := by
      apply div_le_div_of_nonneg_right ?_ hp
      apply mul_le_mul_of_nonneg_left _ hr
      exact_mod_cast Nat.succ_le_of_lt h
    exact (not_lt_of_ge hsep) ((hj.1 i (mem_univ _)).1.trans_lt (hk.1 i (mem_univ _)).2)

def actualExtendedThirdRetainedRegion (e : ℝ) (m : ℕ) : Set (Fin 3 → ℝ) :=
  ⋃ j ∈ actualExtendedThirdRetainedCells e m, actualExtendedThirdOwnedCell m j

theorem measurableSet_actualExtendedThirdRetainedRegion (e : ℝ) (m : ℕ) :
    MeasurableSet (actualExtendedThirdRetainedRegion e m) :=
  MeasurableSet.iUnion (fun j => MeasurableSet.iUnion
    (fun _ => measurableSet_actualExtendedThirdOwnedCell m j))

/-- A literal one-mesh loss pays the first-stop retention wall. The coverage
includes both ordering walls, since membership is tested on their ordered
portions and not by requiring the entire rectangle to be ordered. -/
theorem actualExtendedThirdRetained_unique_cover {e : ℝ} {m : ℕ}
    (he : 0 ≤ e) {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdClosedOrder)
    (hx : t 0 + actualExtendedThirdDyadicStep m ≤ thirdPrefixRho - 4 * e) :
    ∃! j : ActualExtendedThirdDyadicLabel m,
      j ∈ actualExtendedThirdRetainedCells e m ∧ t ∈ actualExtendedThirdOwnedCell m j := by
  have hxrho : t 0 < thirdPrefixRho := by
    linarith [actualExtendedThirdDyadicStep_pos m]
  obtain ⟨j, hj⟩ := exists_actualExtendedThirdOwnedCell ht hxrho
  have hjc := actualExtendedThirdOwnedCell_subset_physicalCell m j hj
  have hjr : j ∈ actualExtendedThirdRetainedCells e m := by
    apply mem_actualExtendedThirdRetainedCells.mpr
    exact ⟨⟨t, hjc⟩, (actualExtendedThirdDyadicHi_le_point_add_step hjc 0).trans hx⟩
  refine ⟨j, ⟨hjr, hj⟩, ?_⟩
  intro k hk
  exact actualExtendedThirdOwnedCell_unique hk.2 hj

theorem actualExtendedThirdUncovered_in_stop_strip {e : ℝ} {m : ℕ}
    (he : 0 ≤ e) {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdClosedOrder)
    (hmiss : t ∉ actualExtendedThirdRetainedRegion e m) :
    thirdPrefixRho - 4 * e - actualExtendedThirdDyadicStep m < t 0 := by
  by_contra hn
  have hx : t 0 + actualExtendedThirdDyadicStep m ≤ thirdPrefixRho - 4 * e := by
    linarith [le_of_not_gt hn]
  obtain ⟨j, ⟨hjr, hj⟩, _⟩ := actualExtendedThirdRetained_unique_cover he ht hx
  exact hmiss (Set.mem_iUnion₂.mpr ⟨j, hjr, hj⟩)

/-- One common grid threshold covers every ordered point with a prescribed
positive first-stop clearance. It is not a different mesh for each point. -/
theorem actualExtendedThirdRetained_uniform_cover {e δ : ℝ} (he : 0 ≤ e) (hδ : 0 < δ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ t ∈ actualExtendedThirdClosedOrder,
      t 0 ≤ thirdPrefixRho - 4 * e - δ → t ∈ actualExtendedThirdRetainedRegion e m := by
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp
    (tendsto_actualExtendedThirdDyadicStep.eventually (gt_mem_nhds hδ))
  refine ⟨m₀, ?_⟩
  intro m hm t ht hx
  have hx' : t 0 + actualExtendedThirdDyadicStep m ≤ thirdPrefixRho - 4 * e := by
    linarith [hm₀ m hm]
  obtain ⟨j, ⟨hjr, hj⟩, _⟩ := actualExtendedThirdRetained_unique_cover he ht hx'
  exact Set.mem_iUnion₂.mpr ⟨j, hjr, hj⟩

/-- The same true endpoint geometry pays the full-envelope transition test.
There is no replacement of the upper endpoint by a sampled coordinate. -/
theorem actualExtendedThirdFullGamma_on_cleared_cell {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hx : t 0 + actualExtendedThirdDyadicStep m ≤ mu - 4 * e) :
    actualExtendedThirdPhysicalGamma e m j = actualExtendedThirdFullGamma e m j := by
  exact if_pos ((actualExtendedThirdDyadicHi_le_point_add_step ht 0).trans hx)

end

end ImbalancedChen
