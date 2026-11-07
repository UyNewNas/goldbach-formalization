import ImbalancedChen.ActualSelectedPrefixCellDecomposition
import ImbalancedChen.OrdinaryLowerFourFrontier

/-!
# Actual lower fourth-prefix restoration on its owned cells

The lower rank-three parent retains precisely its second cube test and
strict processing order. Both fourth own-cube indicators stay inside their
respective actual residuals. The fixed Ico ownership gives exact fallback
cancellation, so the full finite selected family decomposes with no
small-prime or mesh-boundary term discarded.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- Exact equality of the actual candidate cube and the four-row affine
region. In particular, the old fourth-cube test is absent. -/
theorem ordinaryLowerFourFrontierTuples_cube_filter
    (N cap : ℕ) (a b old : ℝ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) :
    (firstExitFrontierTuples 3 (ordinaryParityRosserPolicy true ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b))).filter
        (fun p => p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b)) =
      (actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b)).filter
        (fun p => actualPrimeTupleLog N p ∈
          primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)) := by
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hf, hp⟩
    have hh := (mem_ordinaryLowerFourFrontierTuples_iff_log N cap old 0 _ hN hcap p).mp hf
    refine ⟨hp, (mem_ordinaryLowerFourGateRegion old _).mpr ⟨?_, hh.2.2⟩⟩
    exact (actualPrimeTupleLog_strictAnti_iff hN p (fun i => (hh.2.1 i).1.pos)).mpr hh.1
  · rintro ⟨hp, hg⟩
    have hpi := mem_actualPrimeBoxTuples_iff.mp hp
    have hh := (mem_ordinaryLowerFourGateRegion old _).mp hg
    refine ⟨(mem_ordinaryLowerFourFrontierTuples_iff_log N cap old 0 _ hN hcap p).mpr
      ⟨?_, ?_, hh.2⟩, hp⟩
    · exact (actualPrimeTupleLog_strictAnti_iff hN p (fun i => (hpi i).1.pos)).mp hh.1
    · exact fun i => ⟨(hpi i).1, (hpi i).2.1, Nat.cast_nonneg _, (hpi i).2.2.2⟩

/-- A cell already lies in the positive logarithmic cube. Filtering the
actual parent by that cell therefore gives exactly its affine region. -/
theorem ordinaryLowerFourFrontierTuples_cell_filter
    (N cap : ℕ) (a b old : ℝ) (hab : a < b) (hN : 1 < N)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) (m : ℕ) (j : Fin 4 → Fin (m + 1)) :
    (firstExitFrontierTuples 3 (ordinaryParityRosserPolicy true ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b))).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j) =
      (actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b)).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j ∩
          primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)) := by
  have hfilter := ordinaryLowerFourFrontierTuples_cube_filter N cap a b old hN hcap
  ext p
  simp only [Finset.mem_filter, Set.mem_inter_iff]
  constructor
  · rintro ⟨hf, hj⟩
    have hpi := (mem_actualPrimeFrontierTuples_iff 3
      (ordinaryParityRosserPolicy true ((N : ℝ) ^ old)) N cap 0 _ p).mp hf
    have hp : p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b) :=
      (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
        ⟨fun i => ⟨(hpi.2.1 i).2.1, (hpi.2.1 i).2.2.1⟩,
          logPrimeMeshCell_subset_box hab m j hj⟩
    have hmem := Finset.mem_filter.mpr ⟨hf, hp⟩
    rw [hfilter] at hmem
    exact ⟨hp, hj, (Finset.mem_filter.mp hmem).2⟩
  · rintro ⟨hp, hj, hg⟩
    have hmem : p ∈ (actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b)).filter
        (fun p => actualPrimeTupleLog N p ∈
          primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)) :=
      Finset.mem_filter.mpr ⟨hp, hg⟩
    rw [← hfilter] at hmem
    exact ⟨(Finset.mem_filter.mp hmem).1, hj⟩

/-- The finite cell identity applies to an arbitrary real summand,
without positivity, continuity, or a limit assumption. -/
theorem ordinaryLowerFourFrontier_cell_weighted_sum
    (N cap : ℕ) (a b old : ℝ) (hab : a < b) (hN : 1 < N)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) (m : ℕ) (j : Fin 4 → Fin (m + 1))
    (f : (Fin 4 → ℕ) → ℝ) :
    (∑ p ∈ firstExitFrontierTuples 3
      (ordinaryParityRosserPolicy true ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b)),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j then f p else 0)) =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j ∩
            primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)
          then f p else 0) := by
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter,
    ordinaryLowerFourFrontierTuples_cell_filter N cap a b old hab hN hcap m j]

/-- One owned cell contributes the difference of two actual residual
sums, each with its own strict fourth-cube test. -/
theorem ordinaryLowerFourFrontier_cell_ownCube_difference
    (N cap : ℕ) (a b old lambda : ℝ) (hab : a < b) (hN : 1 < N)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) (m : ℕ) (j : Fin 4 → Fin (m + 1)) :
    (∑ p ∈ firstExitFrontierTuples 3
      (ordinaryParityRosserPolicy true ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b)),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j then
          actualPrimeTupleOwnCubeMinus N cap lambda p - actualPrimeTupleOwnCubeMinus N cap old p
        else 0)) =
      actualPrimeBoxOwnCubeMinusSum 3 N cap a b lambda
        (logPrimeMeshCell a b m j ∩
          primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)) -
      actualPrimeBoxOwnCubeMinusSum 3 N cap a b old
        (logPrimeMeshCell a b m j ∩
          primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)) := by
  rw [ordinaryLowerFourFrontier_cell_weighted_sum N cap a b old hab hN hcap m j]
  simp only [actualPrimeBoxOwnCubeMinusSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  split_ifs <;> ring

/-- The full selected ordinary-parent saving is exactly a finite sum of
cell contributions. There is no discarded small-prime or boundary term. -/
theorem actualSelectedPrefixLowerOwnCubeSum_eq_cells
    (N cap : ℕ) (I : Finset (Fin 4)) (old nu a b : ℚ)
    (hab : a < b) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (b : ℝ) ≤ (cap : ℝ))
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) :
    actualSelectedPrefixOwnCubeSum true N cap ((N : ℝ) ^ (b : ℝ)) I old nu a b m J *
        Real.log (N : ℝ) / singularSeries N =
      ∑ j ∈ J,
        (actualPrimeBoxOwnCubeMinusSum 3 N cap (a : ℝ) (b : ℝ)
          (selectedPrefixCellCap I old nu a b m j : ℝ)
          (logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
            primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)) -
        actualPrimeBoxOwnCubeMinusSum 3 N cap (a : ℝ) (b : ℝ) (old : ℝ)
          (logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
            primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old))) := by
  rw [actualSelectedPrefixOwnCubeSum_eq_normalized_tuple_sum 3]
  simp_rw [actualSelectedOwnCubeTuple_difference_cells N cap I old nu a b hab.le m J,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  exact ordinaryLowerFourFrontier_cell_ownCube_difference N cap a b old
    (selectedPrefixCellCap I old nu a b m j) (by exact_mod_cast hab) hN hcap m j

end

end ImbalancedChen
