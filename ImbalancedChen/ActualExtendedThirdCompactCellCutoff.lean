import ImbalancedChen.ActualExtendedThirdFiniteCellIntegral

/-!
# A fixed positive cutoff on the actual retained cells

This constructs a new finite lookup. Its active cells are precisely the
original retained cells whose third lower endpoint is at least h. The old
level is used everywhere else. Unique ownership evaluates the nonlinear
kernel before it is written as a finite sum of the original cell kernels.

Only the nonnegative continuous correction is compared with the full
lookup. No monotonicity of signed arithmetic weights is asserted. A dropped
cell can meet z < h + mesh, so the loss uses that enlarged cutoff.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology MeasureTheory
open VariableEnvelope
open scoped Classical BigOperators ENNReal

def actualExtendedThirdCompactCells (e h : ℝ) (m : ℕ) :
    Finset (ActualExtendedThirdDyadicLabel m) :=
  (actualExtendedThirdRetainedCells e m).filter
    (fun j => h ≤ actualExtendedThirdDyadicLo m j 2)

theorem actualExtendedThirdCompactCells_subset (e h : ℝ) (m : ℕ) :
    actualExtendedThirdCompactCells e h m ⊆ actualExtendedThirdRetainedCells e m :=
  Finset.filter_subset _ _

def actualExtendedThirdCompactCellLevel (e h : ℝ) (m : ℕ) (t : Fin 3 → ℝ) : ℝ :=
  thirdPrefixTheta - 2 * e + ∑ j ∈ actualExtendedThirdCompactCells e h m,
    if t ∈ actualExtendedThirdOwnedCell m j then
      actualExtendedThirdPhysicalLevel e m j - (thirdPrefixTheta - 2 * e) else 0

theorem actualExtendedThirdCompactCellLevel_on_cell {e h : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdOwnedCell m j) :
    actualExtendedThirdCompactCellLevel e h m t = actualExtendedThirdPhysicalLevel e m j := by
  unfold actualExtendedThirdCompactCellLevel
  rw [Finset.sum_eq_single_of_mem j hj]
  · rw [if_pos ht]
    ring
  · intro k _hk hkj
    apply if_neg
    intro htk
    exact hkj (actualExtendedThirdOwnedCell_unique htk ht)

theorem actualExtendedThirdCompactCellLevel_outside {e h : ℝ} {m : ℕ} {t : Fin 3 → ℝ}
    (ht : ∀ j ∈ actualExtendedThirdCompactCells e h m,
      t ∉ actualExtendedThirdOwnedCell m j) :
    actualExtendedThirdCompactCellLevel e h m t = thirdPrefixTheta - 2 * e := by
  unfold actualExtendedThirdCompactCellLevel
  rw [Finset.sum_eq_zero (fun j hj => if_neg (ht j hj)), add_zero]

def actualExtendedThirdCompactCellKernel (e h : ℝ) (m : ℕ) (t : Fin 3 → ℝ) : ℝ :=
  actualExtendedThirdCapKernel e (actualExtendedThirdCompactCellLevel e h m t)
    (t 0) (t 1) (t 2)

theorem actualExtendedThirdCompactCellKernel_eq_sum_cells (e h : ℝ) (m : ℕ)
    (t : Fin 3 → ℝ) :
    actualExtendedThirdCompactCellKernel e h m t =
      ∑ j ∈ actualExtendedThirdCompactCells e h m,
        actualExtendedThirdRetainedCellKernel e m j t := by
  by_cases hcell : ∃ j ∈ actualExtendedThirdCompactCells e h m,
      t ∈ actualExtendedThirdOwnedCell m j
  · obtain ⟨j, hj, ht⟩ := hcell
    rw [Finset.sum_eq_single_of_mem j hj]
    · unfold actualExtendedThirdCompactCellKernel actualExtendedThirdRetainedCellKernel
      rw [actualExtendedThirdCompactCellLevel_on_cell hj ht, indicator_of_mem ht]
    · intro k _hk hkj
      have hnot : t ∉ actualExtendedThirdOwnedCell m k := by
        intro htk
        exact hkj (actualExtendedThirdOwnedCell_unique htk ht)
      simp only [actualExtendedThirdRetainedCellKernel, indicator_of_notMem hnot]
  · have hout : ∀ j ∈ actualExtendedThirdCompactCells e h m,
        t ∉ actualExtendedThirdOwnedCell m j := by
      intro j hj ht
      exact hcell ⟨j, hj, ht⟩
    have hzero : actualExtendedThirdCompactCellKernel e h m t = 0 := by
      rw [actualExtendedThirdCompactCellKernel, actualExtendedThirdCompactCellLevel_outside hout]
      simp only [actualExtendedThirdCapKernel, sub_self, mul_zero, zero_div]
    rw [hzero]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    simp only [actualExtendedThirdRetainedCellKernel, indicator_of_notMem (hout j hj)]

theorem actualExtendedThirdCompactCellKernel_eq_full {e h : ℝ} {m : ℕ}
    {t : Fin 3 → ℝ} (hz : h + actualExtendedThirdDyadicStep m ≤ t 2) :
    actualExtendedThirdCompactCellKernel e h m t = actualExtendedThirdFiniteKernel e m t := by
  rw [actualExtendedThirdCompactCellKernel_eq_sum_cells,
    actualExtendedThirdFiniteKernel_eq_sum_cells]
  apply Finset.sum_subset (actualExtendedThirdCompactCells_subset e h m)
  intro j hj hjnot
  have hnot : t ∉ actualExtendedThirdOwnedCell m j := by
    intro ht
    have hjlo : ¬ h ≤ actualExtendedThirdDyadicLo m j 2 := by
      intro hjlo
      exact hjnot (Finset.mem_filter.mpr ⟨hj, hjlo⟩)
    have hthi := (ht.1 2 (mem_univ _)).2
    rw [actualExtendedThirdDyadicHi_eq_lo_add_step] at hthi
    linarith
  simp only [actualExtendedThirdRetainedCellKernel, indicator_of_notMem hnot]

theorem actualExtendedThirdCompactCellKernel_eq_zero {e h : ℝ} {m : ℕ}
    {t : Fin 3 → ℝ} (hz : t 2 < h) :
    actualExtendedThirdCompactCellKernel e h m t = 0 := by
  rw [actualExtendedThirdCompactCellKernel_eq_sum_cells]
  apply Finset.sum_eq_zero
  intro j hj
  have hnot : t ∉ actualExtendedThirdOwnedCell m j := by
    intro ht
    have hjlo := (Finset.mem_filter.mp hj).2
    have htlo := (ht.1 2 (mem_univ _)).1
    linarith
  simp only [actualExtendedThirdRetainedCellKernel, indicator_of_notMem hnot]

theorem actualExtendedThirdCompactCellKernel_bounds {e h : ℝ} {m : ℕ}
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdClosedOrderRegion thirdPrefixRho) :
    0 ≤ actualExtendedThirdCompactCellKernel e h m t ∧
      actualExtendedThirdCompactCellKernel e h m t ≤ actualExtendedThirdFiniteKernel e m t := by
  have hnonneg (j : ActualExtendedThirdDyadicLabel m)
      (hj : j ∈ actualExtendedThirdRetainedCells e m) :
      0 ≤ actualExtendedThirdRetainedCellKernel e m j t := by
    rw [actualExtendedThirdRetainedCellKernel_eq_indicator hj]
    by_cases hjt : t ∈ actualExtendedThirdOwnedCell m j
    · rw [indicator_of_mem hjt]
      exact actualExtendedThirdFiniteKernel_nonneg ht.1 ht.2.2.1 ht.2.2.2.1
    · simp only [indicator_of_notMem hjt, le_refl]
  rw [actualExtendedThirdCompactCellKernel_eq_sum_cells,
    actualExtendedThirdFiniteKernel_eq_sum_cells]
  exact ⟨Finset.sum_nonneg (fun j hj => hnonneg j
    (actualExtendedThirdCompactCells_subset e h m hj)),
    Finset.sum_le_sum_of_subset_of_nonneg (actualExtendedThirdCompactCells_subset e h m)
      (fun j hj _ => hnonneg j hj)⟩

theorem integrableOn_actualExtendedThirdCompactCellKernel {e h : ℝ} {m : ℕ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) :
    IntegrableOn (actualExtendedThirdCompactCellKernel e h m)
      (actualExtendedThirdClosedOrderRegion thirdPrefixRho) := by
  change Integrable (fun t : Fin 3 → ℝ => actualExtendedThirdCompactCellKernel e h m t)
    (volume.restrict (actualExtendedThirdClosedOrderRegion thirdPrefixRho))
  simp_rw [actualExtendedThirdCompactCellKernel_eq_sum_cells]
  exact integrable_finsetSum _ (fun j hj =>
    integrableOn_actualExtendedThirdRetainedCellKernel he0 he
      (actualExtendedThirdCompactCells_subset e h m hj))

def actualExtendedThirdCompactCellFunctional (e h : ℝ) (m : ℕ) : ℝ :=
  ∫ t in actualExtendedThirdClosedOrderRegion thirdPrefixRho,
    actualExtendedThirdCompactCellKernel e h m t

theorem actualExtendedThirdCompactCellFunctional_eq_sum_cells {e h : ℝ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (m : ℕ) :
    actualExtendedThirdCompactCellFunctional e h m =
      ∑ j ∈ actualExtendedThirdCompactCells e h m, actualExtendedThirdRetainedCellIntegral e m j := by
  unfold actualExtendedThirdCompactCellFunctional
  simp_rw [actualExtendedThirdCompactCellKernel_eq_sum_cells]
  rw [integral_finsetSum _ (fun j hj => integrableOn_actualExtendedThirdRetainedCellKernel
    he0 he (actualExtendedThirdCompactCells_subset e h m hj))]
  apply Finset.sum_congr rfl
  intro j _hj
  exact integral_actualExtendedThirdRetainedCellKernel e m j

end

end ImbalancedChen
