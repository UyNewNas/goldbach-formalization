import ImbalancedChen.HistoricalUpperFiveCellGeometry
import ImbalancedChen.ActualPrimeOwnCubeIcoIntegral

/-!
# Actual prime integrals on common historical fifth cells

The data are fixed before `N`.  The actual fifth candidates come from the
third-capped rank-four parent.  On a common cell its first gate still uses
the original level, its third gate uses the effective third ancestor, and
its old fifth residual uses the effective fourth ancestor.  Both own-cube
indicators are retained separately.

This file supplies the actual prime-tuple cell identities and their genuine
integrals.  It does not identify the separately reported, unavailable global
fifth-integral candidate or assert a complete adopted-policy density limit.
The imported Ico supplier pays the actual discrete prime boundary strips
before using continuous null-wall identities.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory
open scoped Classical BigOperators

namespace HistoricalPrefixCapData

/-- The normalized actual residual difference at the two levels read from
this same tuple's complete fifth and fourth histories. -/
def fifthTupleOwnCubeDifference (D : HistoricalPrefixCapData)
    (N cap : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  actualPrimeTupleOwnCubeMinus N cap
      (D.exponent5 (actualPrimeTupleLog N p) : ℝ) p -
    actualPrimeTupleOwnCubeMinus N cap
      (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5)
        (actualPrimeTupleLog N p)) : ℝ) p

/-- The actual candidate sum on one half-open cell.  The summand already
contains the residual normalization `log N / singularSeries N`. -/
def fifthCellPrimeCorrection (D : HistoricalPrefixCapData)
    (N cap : ℕ) (j : Fin 5 → Fin (D.m + 1)) : ℝ :=
  ∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
        then D.fifthTupleOwnCubeDifference N cap p else 0)

/-- The complete tuple correction on the actual third-capped parent,
including every fifth candidate rejected by the old own-cube test. -/
def fifthPrimeCorrection (D : HistoricalPrefixCapData) (N cap : ℕ) : ℝ :=
  ∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
    (∏ i, 1 / ((p i : ℝ) - 1)) * D.fifthTupleOwnCubeDifference N cap p

theorem fifthTupleOwnCubeDifference_on_cell (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5)
    (p : Fin 5 → ℕ)
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.fifthTupleOwnCubeDifference N cap p =
      actualPrimeTupleOwnCubeMinus N cap (D.cap5 j : ℝ) p -
        actualPrimeTupleOwnCubeMinus N cap (D.old5 j : ℝ) p := by
  unfold fifthTupleOwnCubeDifference
  rw [D.exponent5_on_cell hab _ j ht,
    D.exponent4_on_cell hab _ _
      (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 4 ≤ 5) ht)]
  simp only [cell5, if_pos hj, old5]

/-- The unselected fifth cell keeps its complete fourth history exactly. -/
theorem fifthTupleOwnCubeDifference_on_unselected_cell
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (N cap : ℕ)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∉ D.cells5)
    (p : Fin 5 → ℕ)
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.fifthTupleOwnCubeDifference N cap p = 0 := by
  unfold fifthTupleOwnCubeDifference
  rw [D.exponent5_on_cell hab _ j ht,
    D.exponent4_on_cell hab _ _
      (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 4 ≤ 5) ht)]
  simp only [cell5, if_neg hj, old5, sub_self]

/-- Exact fallback is proved for actual residuals before taking limits. -/
theorem fifthTupleOwnCubeDifference_outside (D : HistoricalPrefixCapData)
    (N cap : ℕ) (p : Fin 5 → ℕ)
    (hout : ∀ j ∈ D.cells5, actualPrimeTupleLog N p ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.fifthTupleOwnCubeDifference N cap p = 0 := by
  unfold fifthTupleOwnCubeDifference
  rw [D.exponent5_outside _ hout, sub_self]

theorem fifthCellPrimeCorrection_eq_zero_of_not_mem
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (N cap : ℕ)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∉ D.cells5) :
    D.fifthCellPrimeCorrection N cap j = 0 := by
  unfold fifthCellPrimeCorrection
  apply Finset.sum_eq_zero
  intro p _hp
  by_cases ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
  · rw [if_pos ht, D.fifthTupleOwnCubeDifference_on_unselected_cell hab N cap j hj p ht,
      mul_zero]
  · rw [if_neg ht, mul_zero]

/-- The same tuple difference is supported on its unique selected cell. -/
theorem fifthTupleOwnCubeDifference_eq_cell_indicators
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N cap : ℕ) (p : Fin 5 → ℕ) :
    D.fifthTupleOwnCubeDifference N cap p =
      ∑ j ∈ D.cells5,
        if actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
          then D.fifthTupleOwnCubeDifference N cap p else 0 := by
  calc
    _ = ∑ j ∈ D.cells5,
        if actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          actualPrimeTupleOwnCubeMinus N cap (D.cap5 j : ℝ) p -
            actualPrimeTupleOwnCubeMinus N cap (D.old5 j : ℝ) p else 0 :=
      D.exponent5_apply_sub hab (actualPrimeTupleLog N p)
        (fun lambda => actualPrimeTupleOwnCubeMinus N cap (lambda : ℝ) p)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases ht : actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
      · rw [if_pos ht, if_pos ht]
        exact (D.fifthTupleOwnCubeDifference_on_cell hab N cap j hj p ht).symm
      · rw [if_neg ht, if_neg ht]

/-- Finite common-cell decomposition without a discarded prime tail or
an arithmetic-boundary remainder. -/
theorem fifthPrimeCorrection_eq_cells (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ) :
    D.fifthPrimeCorrection N cap =
      ∑ j ∈ D.cells5, D.fifthCellPrimeCorrection N cap j := by
  calc
    _ = ∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          ∑ j ∈ D.cells5,
            if actualPrimeTupleLog N p ∈
                logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
              then D.fifthTupleOwnCubeDifference N cap p else 0 := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact congrArg (fun x : ℝ => (∏ i, 1 / ((p i : ℝ) - 1)) * x)
        (D.fifthTupleOwnCubeDifference_eq_cell_indicators hab N cap p)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      rfl

/-- The actual historical parent and its geometric cell have identical
weighted sums, for any summand. -/
theorem fifthFrontier_cell_weighted_sum (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (D.m + 1)) (f : (Fin 5 → ℕ) → ℝ) :
    (∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then f p else 0)) =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 5 => (D.a : ℝ))
          (fun _ => (D.b : ℝ)),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
              primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)
            then f p else 0) := by
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter,
    historicalUpperFiveFrontierTuples_cell_filter D hab hold hcheck N cap hN hcap j]

/-- Each old/new residual retains its own fifth-cube admission, while
both use the same actual third-capped parent region. -/
theorem fifthCellPrimeCorrection_eq_residual_sums (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5) :
    D.fifthCellPrimeCorrection N cap j =
      actualPrimeBoxOwnCubeMinusSum 4 N cap (D.a : ℝ) (D.b : ℝ) (D.cap5 j : ℝ)
        (logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
          primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)) -
      actualPrimeBoxOwnCubeMinusSum 4 N cap (D.a : ℝ) (D.b : ℝ) (D.old5 j : ℝ)
        (logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
          primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)) := by
  have hcell : D.fifthCellPrimeCorrection N cap j =
      ∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈
              logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
            actualPrimeTupleOwnCubeMinus N cap (D.cap5 j : ℝ) p -
              actualPrimeTupleOwnCubeMinus N cap (D.old5 j : ℝ) p else 0) := by
    apply Finset.sum_congr rfl
    intro p _hp
    by_cases ht : actualPrimeTupleLog N p ∈
        logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
    · rw [if_pos ht, if_pos ht,
        D.fifthTupleOwnCubeDifference_on_cell hab.le N cap j hj p ht]
    · rw [if_neg ht, if_neg ht]
  rw [hcell, D.fifthFrontier_cell_weighted_sum hab hold hcheck N cap hN hcap j]
  simp only [actualPrimeBoxOwnCubeMinusSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  split_ifs <;> ring

/-- The literal difference of two real Ico-cell integrals. -/
def fifthCellIntegral (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : ℝ :=
  primeOwnCubeIcoIntegral (D.a : ℝ) (D.b : ℝ) (D.cap5 j : ℝ) D.m j
      ordinaryUpperFiveGateForms (D.fifthParentGateBounds j) -
    primeOwnCubeIcoIntegral (D.a : ℝ) (D.b : ℝ) (D.old5 j : ℝ) D.m j
      ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)

def fifthCorrectionIntegral (D : HistoricalPrefixCapData) : ℝ :=
  ∑ j ∈ D.cells5, D.fifthCellIntegral j

theorem fifthCellIntegral_eq_integral (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1)) :
    D.fifthCellIntegral j =
      ∫ t in logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
        primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j),
        (primeOwnCubeGatedProfile (D.cap5 j : ℝ) t -
          primeOwnCubeGatedProfile (D.old5 j : ℝ) t) * ∏ i, 1 / t i :=
  primeOwnCubeIcoIntegral_sub_eq_integral (by exact_mod_cast ha)
    (by exact_mod_cast hab) (D.old5 j : ℝ) (D.cap5 j : ℝ) D.m j
    ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)

theorem fifthCorrectionIntegral_eq_integrals (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) :
    D.fifthCorrectionIntegral =
      ∑ j ∈ D.cells5,
        ∫ t in logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
          primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j),
          (primeOwnCubeGatedProfile (D.cap5 j : ℝ) t -
            primeOwnCubeGatedProfile (D.old5 j : ℝ) t) * ∏ i, 1 / t i := by
  apply Finset.sum_congr rfl
  intro j _hj
  exact D.fifthCellIntegral_eq_integral ha hab j

/-- The actual prime sum on a selected historical cell has the literal
integral limit; no integral bound or convergence is assumed by the caller. -/
theorem tendsto_fifthCellPrimeCorrection (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => D.fifthCellPrimeCorrection N (cap N) j)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (D.fifthCellIntegral j)) := by
  have hlim := tendsto_actualPrimeBoxOwnCubeMinus_difference_IcoCell_affineGates 4
    (D.a : ℝ) (D.b : ℝ) (D.old5 j : ℝ) (D.cap5 j : ℝ)
    (by exact_mod_cast ha) (by exact_mod_cast hab) D.m j
    ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)
    ordinaryUpperFiveGateForms_ne_zero cap hcap
  change Tendsto _ _ (𝓝 (D.fifthCellIntegral j)) at hlim
  apply hlim.congr'
  have hlarge : ∀ᶠ N : ℕ in
      atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  exact (D.fifthCellPrimeCorrection_eq_residual_sums
    hab hold hcheck N (cap N) hN hc j hj).symm

/-- Summing a fixed finite family of the actual historical cells commutes
with the limit after the exact fallback identity has been proved. -/
theorem tendsto_fifthPrimeCorrection (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => D.fifthPrimeCorrection N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral) := by
  have hlim := tendsto_finsetSum D.cells5 (fun j hj =>
    D.tendsto_fifthCellPrimeCorrection ha hab hold hcheck j hj cap hcap)
  change Tendsto _ _ (𝓝 D.fifthCorrectionIntegral) at hlim
  apply hlim.congr'
  exact Eventually.of_forall (fun N => (D.fifthPrimeCorrection_eq_cells hab.le N (cap N)).symm)

/-- The literal ceil enumeration supplies its own cap-coverage proof. -/
theorem tendsto_fifthPrimeCorrection_ceil (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) :
    Tendsto (fun N : ℕ =>
      D.fifthPrimeCorrection N (Nat.ceil ((N : ℝ) ^ (D.b : ℝ))))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral) :=
  D.tendsto_fifthPrimeCorrection ha hab hold hcheck _
    (Eventually.of_forall (fun N => Nat.le_ceil ((N : ℝ) ^ (D.b : ℝ))))

end HistoricalPrefixCapData

end

end ImbalancedChen
