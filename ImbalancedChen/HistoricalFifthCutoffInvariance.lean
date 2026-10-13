import ImbalancedChen.ActualHistoricalFifthSavingIntegral

/-!
# Outer-cutoff invariance of the actual historical fifth saving

The fifth update is supported on a fixed finite family of owned Ico
cells in `[a,b)^5`.  On such a cell every actual prime is strictly below
`N^b`.  Raising only the outer rough-prime cutoff therefore preserves the
entire normalized saving.  The target, enumeration cap, residual cap,
parent policy and both own-cube indicators remain the same.

This is first an exact finite identity, including actual primes on cell
boundaries.  The integral corollaries then reuse the existing discrete
boundary-payment and common-cell limit.  They do not change the residual
enumeration cap or claim a limit of either individual full policy density.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped Classical BigOperators

/-- On one owned cell an arbitrary actual parent has the same candidates
at any larger outer cutoff.  The strict enumeration-cap test, target
deletion, sorting and complete proper-parent validity all remain literal. -/
theorem actualPrimeFrontierTuples_ownedCell_cutoff_invariant
    (k : ℕ) (parent : Bool → List ℕ → Bool) (N cap : ℕ) (hN : 1 < N)
    (a b : ℝ) (hab : a < b) (m : ℕ)
    (j : Fin (k + 1) → Fin (m + 1)) (z : ℝ) (hz : (N : ℝ) ^ b ≤ z) :
    (firstExitFrontierTuples k parent (roughPrimeUniverse N cap 0 z)).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j) =
      (firstExitFrontierTuples k parent
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b))).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j) := by
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, ht⟩
    rw [mem_actualPrimeFrontierTuples_iff] at hp
    refine ⟨(mem_actualPrimeFrontierTuples_iff k parent N cap 0
      ((N : ℝ) ^ b) p).mpr ⟨hp.1, ?_, hp.2.2⟩, ht⟩
    intro i
    refine ⟨(hp.2.1 i).1, (hp.2.1 i).2.1, (hp.2.1 i).2.2.1,
      (hp.2.1 i).2.2.2.1, ?_⟩
    have hb := (mem_logPrimeBox.mp (logPrimeMeshCell_subset_box hab m j ht) i).2
    rw [← actualPrimeTupleLog_rpow hN p (fun q => (hp.2.1 q).2.1.pos) i]
    exact Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hN) hb
  · rintro ⟨hp, ht⟩
    rw [mem_actualPrimeFrontierTuples_iff] at hp
    refine ⟨(mem_actualPrimeFrontierTuples_iff k parent N cap 0 z p).mpr
      ⟨hp.1, ?_, hp.2.2⟩, ht⟩
    exact fun i => ⟨(hp.2.1 i).1, (hp.2.1 i).2.1, (hp.2.1 i).2.2.1,
      (hp.2.1 i).2.2.2.1, (hp.2.1 i).2.2.2.2.trans_le hz⟩

namespace HistoricalPrefixCapData

/-- Outside the selected fifth cells the actual residuals agree before
normalization, because the complete fourth ancestor is inherited exactly. -/
theorem fifthOwnCubeDifference_outside (D : HistoricalPrefixCapData)
    (N cap : ℕ) {history : List ℕ} (hlen : history.length = 5)
    (hout : ∀ j ∈ D.cells5, primeHistoryLogCoordinates (N : ℝ) 5 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    actualOwnCubeGatedMinusDensity N cap (D.level5 (N : ℝ)) history -
      actualOwnCubeGatedMinusDensity N cap
        (fun pre => D.level4 (N : ℝ) (rosserAncestor 4 pre)) history = 0 := by
  have hlevel := D.level5_outside (N : ℝ) history hlen hout
  simp only [actualOwnCubeGatedMinusDensity, hlevel, sub_self]

/-- Exact zero outside the selected cells also holds for the actual
normalized residual difference, without any assumption on the target. -/
theorem fifthOwnCubeDifference_normalized_outside (D : HistoricalPrefixCapData)
    (N cap : ℕ) {history : List ℕ} (hlen : history.length = 5)
    (hout : ∀ j ∈ D.cells5, primeHistoryLogCoordinates (N : ℝ) 5 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (actualOwnCubeGatedMinusDensity N cap (D.level5 (N : ℝ)) history -
      actualOwnCubeGatedMinusDensity N cap
        (fun pre => D.level4 (N : ℝ) (rosserAncestor 4 pre)) history) *
        Real.log (N : ℝ) / singularSeries N = 0 := by
  rw [D.fifthOwnCubeDifference_outside N cap hlen hout, zero_mul, zero_div]

/-- The full tuple saving is unchanged when only the outer rough cutoff
is raised.  The same enumeration cap occurs in both residuals throughout. -/
theorem fifthTupleSum_cutoff_invariant (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (N cap : ℕ) (hN : 1 < N)
    (z : ℝ) (hz : (N : ℝ) ^ (D.b : ℝ) ≤ z) :
    (∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 z),
      (∏ i, 1 / ((p i : ℝ) - 1)) * D.fifthTupleOwnCubeDifference N cap p) =
      D.fifthPrimeCorrection N cap := by
  have hcell (j : Fin 5 → Fin (D.m + 1)) :
      (∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
            then D.fifthTupleOwnCubeDifference N cap p else 0)) =
        D.fifthCellPrimeCorrection N cap j := by
    unfold fifthCellPrimeCorrection
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter, ← Finset.sum_filter,
      actualPrimeFrontierTuples_ownedCell_cutoff_invariant 4
        (D.upperThirdPolicy (N : ℝ)) N cap hN (D.a : ℝ) (D.b : ℝ)
        (by exact_mod_cast hab) D.m j z hz]
  calc
    _ = ∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          ∑ j ∈ D.cells5,
            if actualPrimeTupleLog N p ∈
                logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
              then D.fifthTupleOwnCubeDifference N cap p else 0 := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact congrArg (fun x : ℝ => (∏ i, 1 / ((p i : ℝ) - 1)) * x)
        (D.fifthTupleOwnCubeDifference_eq_cell_indicators hab.le N cap p)
    _ = ∑ j ∈ D.cells5, D.fifthCellPrimeCorrection N cap j := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      exact hcell j
    _ = _ := (D.fifthPrimeCorrection_eq_cells hab.le N cap).symm

/-- Exact invariance of the normalized actual nested saving.  Only the
outer cutoff changes; no coverage or replacement of the residual cap is
needed for this finite identity. -/
theorem actualHistoricalFifthSaving_eq_fifthPrimeCorrection_of_cutoff_ge
    (D : HistoricalPrefixCapData) (hab : D.a < D.b)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) (hz : (N : ℝ) ^ (D.b : ℝ) ≤ z) :
    actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z *
        Real.log (N : ℝ) / singularSeries N = D.fifthPrimeCorrection N cap := by
  rw [D.actualHistoricalFifthSaving_eq_tupleSum_at_cutoff,
    D.fifthTupleSum_cutoff_invariant hab N cap hN z hz]

/-- A moving outer cutoff eventually containing the fixed selected cube
has the same actual saving integral.  The residual enumeration cap is
the one fixed on both sides and need only cover `N^b` eventually. -/
theorem tendsto_actualHistoricalFifthSaving_of_cutoff_ge (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) (cap : ℕ → ℕ) (z : ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ))
    (hz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ z N) :
    Tendsto (fun N : ℕ =>
      actualHistoricalFifthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N (cap N) (z N) *
          Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral) := by
  apply (D.tendsto_fifthPrimeCorrection ha hab hold hcheck cap hcap).congr'
  have hlarge : ∀ᶠ N : ℕ in
      atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hz] with N hN hzN
  exact (D.actualHistoricalFifthSaving_eq_fifthPrimeCorrection_of_cutoff_ge
    hab N (cap N) hN (z N) hzN).symm

/-- The actual policy density difference at a larger outer cutoff is
the same normalized correction after the finite history check. -/
theorem upperFourthToFifthSaving_normalized_eq_fifthPrimeCorrection_of_cutoff_ge
    (D : HistoricalPrefixCapData) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) (hz : (N : ℝ) ^ (D.b : ℝ) ≤ z) :
    (firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)) *
        Real.log (N : ℝ) / singularSeries N = D.fifthPrimeCorrection N cap := by
  rw [D.upperFourthToFifthSaving_eq hab.le hcheck N cap (by exact_mod_cast hN),
    D.actualHistoricalFifthSaving_eq_fifthPrimeCorrection_of_cutoff_ge hab N cap hN z hz]

/-- The normalized actual fourth-to-fifth policy difference has its
common-cell integral limit at any eventually covering moving outer
cutoff, with the original target-deleted carrier and residual cap. -/
theorem tendsto_upperFourthToFifthSaving_of_cutoff_ge (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) (cap : ℕ → ℕ) (z : ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ))
    (hz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ z N) :
    Tendsto (fun N : ℕ =>
      (firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N (cap N) 0 (z N)) -
        firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 (z N))) *
          Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral) := by
  apply (D.tendsto_fifthPrimeCorrection ha hab hold hcheck cap hcap).congr'
  have hlarge : ∀ᶠ N : ℕ in
      atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hz] with N hN hzN
  exact (D.upperFourthToFifthSaving_normalized_eq_fifthPrimeCorrection_of_cutoff_ge
    hab hcheck N (cap N) hN (z N) hzN).symm

end HistoricalPrefixCapData

end

end ImbalancedChen
