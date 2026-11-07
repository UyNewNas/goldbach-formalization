import ImbalancedChen.ActualSelectedPrefixCellDecomposition

/-!
# Exact selected fifth-prefix saving as a finite sum over owned cells

The ordinary rank-four parent retains its inherited first and third cube
tests. Half-open ownership supplies the selected cap and the lower cube
cutoff; candidates outside all adopted cells cancel exactly. Both old and
new fifth own-cube tests remain inside the actual residual densities.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- A cell already lies in the positive logarithmic cube. Filtering the
actual parent by that cell therefore gives exactly its affine region. -/
theorem ordinaryUpperFiveFrontierTuples_cell_filter
    (N cap : ℕ) (a b old : ℝ) (hab : a < b) (hN : 1 < N) (hold : 0 < old)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) (m : ℕ) (j : Fin 5 → Fin (m + 1)) :
    (firstExitFrontierTuples 4 (ordinaryParityRosserPolicy false ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b))).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j) =
      (actualPrimeBoxTuples N (fun _ : Fin 5 => a) (fun _ => b)).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j ∩
          primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old)) := by
  have hfilter := ordinaryUpperFiveFrontierTuples_cube_filter N cap a b old hN hold hcap
  ext p
  simp only [Finset.mem_filter, Set.mem_inter_iff]
  constructor
  · rintro ⟨hf, hj⟩
    have hpi := (mem_actualPrimeFrontierTuples_iff 4
      (ordinaryParityRosserPolicy false ((N : ℝ) ^ old)) N cap 0 _ p).mp hf
    have hp : p ∈ actualPrimeBoxTuples N (fun _ : Fin 5 => a) (fun _ => b) :=
      (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
        ⟨fun i => ⟨(hpi.2.1 i).2.1, (hpi.2.1 i).2.2.1⟩,
          logPrimeMeshCell_subset_box hab m j hj⟩
    have hmem := Finset.mem_filter.mpr ⟨hf, hp⟩
    rw [hfilter] at hmem
    exact ⟨hp, hj, (Finset.mem_filter.mp hmem).2⟩
  · rintro ⟨hp, hj, hg⟩
    have hmem : p ∈ (actualPrimeBoxTuples N (fun _ : Fin 5 => a) (fun _ => b)).filter
        (fun p => actualPrimeTupleLog N p ∈
          primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old)) :=
      Finset.mem_filter.mpr ⟨hp, hg⟩
    rw [← hfilter] at hmem
    exact ⟨(Finset.mem_filter.mp hmem).1, hj⟩

/-- The finite cell identity applies to an arbitrary real summand,
without positivity, continuity, or a limit assumption. -/
theorem ordinaryUpperFiveFrontier_cell_weighted_sum
    (N cap : ℕ) (a b old : ℝ) (hab : a < b) (hN : 1 < N) (hold : 0 < old)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) (m : ℕ) (j : Fin 5 → Fin (m + 1))
    (f : (Fin 5 → ℕ) → ℝ) :
    (∑ p ∈ firstExitFrontierTuples 4
      (ordinaryParityRosserPolicy false ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b)),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j then f p else 0)) =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 5 => a) (fun _ => b),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j ∩
            primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old)
          then f p else 0) := by
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter,
    ordinaryUpperFiveFrontierTuples_cell_filter N cap a b old hab hN hold hcap m j]

/-- One owned cell contributes the difference of two actual residual
sums, each with its own strict fifth-cube test. -/
theorem ordinaryUpperFiveFrontier_cell_ownCube_difference
    (N cap : ℕ) (a b old lambda : ℝ) (hab : a < b) (hN : 1 < N) (hold : 0 < old)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) (m : ℕ) (j : Fin 5 → Fin (m + 1)) :
    (∑ p ∈ firstExitFrontierTuples 4
      (ordinaryParityRosserPolicy false ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b)),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j then
          actualPrimeTupleOwnCubeMinus N cap lambda p - actualPrimeTupleOwnCubeMinus N cap old p
        else 0)) =
      actualPrimeBoxOwnCubeMinusSum 4 N cap a b lambda
        (logPrimeMeshCell a b m j ∩
          primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old)) -
      actualPrimeBoxOwnCubeMinusSum 4 N cap a b old
        (logPrimeMeshCell a b m j ∩
          primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old)) := by
  rw [ordinaryUpperFiveFrontier_cell_weighted_sum N cap a b old hab hN hold hcap m j]
  simp only [actualPrimeBoxOwnCubeMinusSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  split_ifs <;> ring

/-- The full selected ordinary-parent saving is exactly a finite sum of
cell contributions. There is no discarded small-prime or boundary term. -/
theorem actualSelectedPrefixUpperOwnCubeSum_eq_cells
    (N cap : ℕ) (I : Finset (Fin 5)) (old nu a b : ℚ)
    (hab : a < b) (hN : 1 < N) (hold : 0 < old)
    (hcap : (N : ℝ) ^ (b : ℝ) ≤ (cap : ℝ))
    (m : ℕ) (J : Finset (Fin 5 → Fin (m + 1))) :
    actualSelectedPrefixOwnCubeSum false N cap ((N : ℝ) ^ (b : ℝ)) I old nu a b m J *
        Real.log (N : ℝ) / singularSeries N =
      ∑ j ∈ J,
        (actualPrimeBoxOwnCubeMinusSum 4 N cap (a : ℝ) (b : ℝ)
          (selectedPrefixCellCap I old nu a b m j : ℝ)
          (logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
            primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old)) -
        actualPrimeBoxOwnCubeMinusSum 4 N cap (a : ℝ) (b : ℝ) (old : ℝ)
          (logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
            primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old))) := by
  rw [actualSelectedPrefixOwnCubeSum_eq_normalized_tuple_sum 4]
  simp_rw [actualSelectedOwnCubeTuple_difference_cells N cap I old nu a b hab.le m J,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  exact ordinaryUpperFiveFrontier_cell_ownCube_difference N cap a b old
    (selectedPrefixCellCap I old nu a b m j) (by exact_mod_cast hab) hN
    (by exact_mod_cast hold) hcap m j

end

end ImbalancedChen
