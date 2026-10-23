import ImbalancedChen.ActualExtendedThirdFunctionalConvergence

/-!
# Exact cell decomposition of the actual finite policy integral

The nonlinear finite lookup is evaluated before it is decomposed. Unique
dyadic ownership identifies its value on each retained cell, and its old
level outside every retained cell has zero correction. This proves an
exact finite sum of the literal cell kernels, not a linearization of the
lower sieve function.

Full-domain integrability supplies every cell's integrability. The finite
sum of the actual ordered cell integrals therefore has the same proved
limit as the finite-policy functional. No arithmetic density limit or
factorization license is supplied or asserted here.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology MeasureTheory
open VariableEnvelope
open scoped Classical BigOperators

def actualExtendedThirdRetainedCellKernel (e : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) (t : Fin 3 → ℝ) : ℝ :=
  (actualExtendedThirdOwnedCell m j).indicator
    (fun t => actualExtendedThirdCapKernel e (actualExtendedThirdPhysicalLevel e m j)
      (t 0) (t 1) (t 2)) t

theorem actualExtendedThirdRetainedCellKernel_eq_indicator {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdRetainedCells e m) :
    actualExtendedThirdRetainedCellKernel e m j =
      (actualExtendedThirdOwnedCell m j).indicator (actualExtendedThirdFiniteKernel e m) := by
  funext t
  unfold actualExtendedThirdRetainedCellKernel
  by_cases ht : t ∈ actualExtendedThirdOwnedCell m j
  · simp only [indicator_of_mem ht]
    rw [actualExtendedThirdFiniteKernel, actualExtendedThirdFiniteLevel_on_cell hj ht]
  · simp only [indicator_of_notMem ht]

/-- Unique ownership is used after evaluating the nonlinear cap kernel. -/
theorem actualExtendedThirdFiniteKernel_eq_sum_cells (e : ℝ) (m : ℕ) (t : Fin 3 → ℝ) :
    actualExtendedThirdFiniteKernel e m t =
      ∑ j ∈ actualExtendedThirdRetainedCells e m, actualExtendedThirdRetainedCellKernel e m j t := by
  by_cases hcell : ∃ j ∈ actualExtendedThirdRetainedCells e m,
      t ∈ actualExtendedThirdOwnedCell m j
  · obtain ⟨j, hj, ht⟩ := hcell
    rw [Finset.sum_eq_single_of_mem j hj]
    · rw [actualExtendedThirdRetainedCellKernel_eq_indicator hj, indicator_of_mem ht]
    · intro k _hk hkj
      have hnot : t ∉ actualExtendedThirdOwnedCell m k := by
        intro htk
        exact hkj (actualExtendedThirdOwnedCell_unique htk ht)
      simp only [actualExtendedThirdRetainedCellKernel, indicator_of_notMem hnot]
  · have hout : ∀ j ∈ actualExtendedThirdRetainedCells e m,
        t ∉ actualExtendedThirdOwnedCell m j := by
      intro j hj ht
      exact hcell ⟨j, hj, ht⟩
    have hzero : actualExtendedThirdFiniteKernel e m t = 0 := by
      rw [actualExtendedThirdFiniteKernel, actualExtendedThirdFiniteLevel_outside hout]
      simp only [actualExtendedThirdCapKernel, sub_self, mul_zero, zero_div]
    rw [hzero]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    simp only [actualExtendedThirdRetainedCellKernel, indicator_of_notMem (hout j hj)]

theorem integrableOn_actualExtendedThirdRetainedCellKernel {e : ℝ} {m : ℕ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdRetainedCells e m) :
    IntegrableOn (actualExtendedThirdRetainedCellKernel e m j)
      (actualExtendedThirdClosedOrderRegion thirdPrefixRho) := by
  rw [actualExtendedThirdRetainedCellKernel_eq_indicator hj]
  exact (integrableOn_actualExtendedThirdFiniteKernel_full he0 he m).indicator
    (measurableSet_actualExtendedThirdOwnedCell m j)

def actualExtendedThirdRetainedCellIntegral (e : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) : ℝ :=
  ∫ t in actualExtendedThirdOwnedCell m j ∩ actualExtendedThirdClosedOrderRegion thirdPrefixRho,
    actualExtendedThirdCapKernel e (actualExtendedThirdPhysicalLevel e m j) (t 0) (t 1) (t 2)

theorem integral_actualExtendedThirdRetainedCellKernel (e : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) :
    (∫ t in actualExtendedThirdClosedOrderRegion thirdPrefixRho,
      actualExtendedThirdRetainedCellKernel e m j t) =
        actualExtendedThirdRetainedCellIntegral e m j := by
  unfold actualExtendedThirdRetainedCellKernel actualExtendedThirdRetainedCellIntegral
  rw [integral_indicator (measurableSet_actualExtendedThirdOwnedCell m j),
    Measure.restrict_restrict (measurableSet_actualExtendedThirdOwnedCell m j)]

theorem integrableOn_actualExtendedThirdRetainedCellCapKernel {e : ℝ} {m : ℕ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdRetainedCells e m) :
    IntegrableOn (fun t : Fin 3 → ℝ =>
      actualExtendedThirdCapKernel e (actualExtendedThirdPhysicalLevel e m j) (t 0) (t 1) (t 2))
      (actualExtendedThirdOwnedCell m j ∩ actualExtendedThirdClosedOrderRegion thirdPrefixRho) := by
  have hI := integrableOn_actualExtendedThirdRetainedCellKernel he0 he hj
  change Integrable ((actualExtendedThirdOwnedCell m j).indicator
    (fun t => actualExtendedThirdCapKernel e (actualExtendedThirdPhysicalLevel e m j)
      (t 0) (t 1) (t 2)))
      (volume.restrict (actualExtendedThirdClosedOrderRegion thirdPrefixRho)) at hI
  change Integrable _ (volume.restrict _)
  rw [← Measure.restrict_restrict (measurableSet_actualExtendedThirdOwnedCell m j)]
  exact (integrable_indicator_iff (measurableSet_actualExtendedThirdOwnedCell m j)).1 hI

/-- An exact sum on the original ordered domain, with genuine integrability
of every summand. No infinite sum or limiting operation is interchanged. -/
theorem actualExtendedThirdFiniteFunctional_eq_sum_cells {e : ℝ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (m : ℕ) :
    actualExtendedThirdFiniteFunctional e m =
      ∑ j ∈ actualExtendedThirdRetainedCells e m, actualExtendedThirdRetainedCellIntegral e m j := by
  unfold actualExtendedThirdFiniteFunctional
  simp_rw [actualExtendedThirdFiniteKernel_eq_sum_cells]
  rw [integral_finsetSum _
    (fun j hj => integrableOn_actualExtendedThirdRetainedCellKernel he0 he hj)]
  apply Finset.sum_congr rfl
  intro j _hj
  exact integral_actualExtendedThirdRetainedCellKernel e m j

theorem actualExtendedThirdRetainedCellIntegral_sum_uniform_approx {ε : ℝ} (hε : 0 < ε) :
    ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 384 ∧ ∃ m₀ : ℕ,
      ∀ e : ℝ, 0 ≤ e → e ≤ e₀ → ∀ m : ℕ, m₀ ≤ m →
        |(∑ j ∈ actualExtendedThirdRetainedCells e m, actualExtendedThirdRetainedCellIntegral e m j) -
          actualExtendedThirdIdealFunctional| ≤ ε := by
  obtain ⟨e₀, he₀, he₀cap, m₀, hb⟩ := actualExtendedThirdFiniteFunctional_uniform_approx hε
  refine ⟨e₀, he₀, he₀cap, m₀, ?_⟩
  intro e he0 he m hm
  rw [← actualExtendedThirdFiniteFunctional_eq_sum_cells he0 (he.trans he₀cap) m]
  exact hb e he0 he m hm

end

end ImbalancedChen
