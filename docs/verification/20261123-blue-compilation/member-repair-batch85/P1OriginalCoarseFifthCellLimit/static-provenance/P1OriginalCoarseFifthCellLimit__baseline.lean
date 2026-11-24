import ImbalancedChen.P1OriginalCoarseFifthResidualDictionary
import ImbalancedChen.P1OriginalCoarseFifthCellIntegral
import ImbalancedChen.ActualPrimeOwnCubeAffineIntegral
import ImbalancedChen.ActualPrimeIcoCellTestFunctions

/-!
# Actual fifth mean on the original coarse T3 candidate tree

The original first-stop, initial/current first cubes, third cube and rough
activation are retained.  New and inherited own-cube gates are separate
actual residuals and never filter the candidate carrier.  The positive
cube [a,19/96)^5 is explicit; every smaller-coordinate tuple is retained
in a named arithmetic remainder, with no a-to-zero assertion.
-/

namespace ImbalancedChen.P1OriginalFifthLimit
noncomputable section
open Filter Topology MeasureTheory Set
open scoped Classical BigOperators
open P1OriginalCoarseFifthContinuation
open HistoricalThirdCoarse.P1OriginalCoarseFifth

def sourceRegion (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m) : Set (Fin 5 → ℝ) :=
  logPrimeMeshCell 0 (19 / 96) m j ∩ jointRegion (e : ℝ) chi m omega j

theorem sourceRegion_eq_if (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5) :
    sourceRegion e chi m omega j =
      if P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck (e : ℝ) m j = true then
        logPrimeMeshCell 0 (19 / 96) m j ∩ primeAffineGateRegion historicalUnorderedThirdGateForms
          (P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e m j)
      else ∅ := by
  have heq : sourceRegion e chi m omega j =
      P1OriginalHistoricalFifthOwnCubeAffineGates.candidateCell e m omega j := by
    ext t
    constructor
    · rintro ⟨ht, hg⟩
      exact ⟨ht, (P1OriginalHistoricalFifthOwnCubeAffineGates.jointRegion_on_selected_cell
        e chi m omega J5 j hj ht).mp hg⟩
    · rintro ⟨ht, hg⟩
      exact ⟨ht, (P1OriginalHistoricalFifthOwnCubeAffineGates.jointRegion_on_selected_cell
        e chi m omega J5 j hj ht).mpr hg⟩
  rw [heq]
  exact P1OriginalHistoricalFifthOwnCubeAffineGates.candidateCell_eq_if e chi m omega J5 j hj

theorem truncatedCell_eq_inter_sourceRegion (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (j : Label5 m) :
    P1OriginalFifthIntegral.truncatedCell e chi m omega a j =
      logPrimeBox (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ)) ∩ sourceRegion e chi m omega j := by
  rfl

theorem tendsto_test_cube_IcoBox_affineGates {r : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (lo hi : Fin 5 → ℝ)
    (L : Fin r → (Fin 5 → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (hL : ∀ i, L i ≠ 0)
    (f : (Fin 5 → ℝ) → ℝ)
    (hf : ContinuousOn f (univ.pi (fun _ : Fin 5 => Icc a b))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 5 => a) (fun _ => b)
        ((logPrimeBox lo hi ∩ primeAffineGateRegion L c).indicator f)) atTop
      (𝓝 (∫ t in logPrimeBox (fun _ : Fin 5 => a) (fun _ => b) ∩
          (logPrimeBox lo hi ∩ primeAffineGateRegion L c), f t * ∏ i, 1 / t i)) := by
  have hlo : primeAffineGateRegion (primeIcoBoxGateForms L) (primeIcoBoxGateBounds lo hi c) ⊆
      logPrimeBox lo hi ∩ primeAffineGateRegion L c := by
    intro t ht
    obtain ⟨hbox, hg⟩ := (mem_primeIcoBoxStrictGateRegion lo hi L c t).mp ht
    exact ⟨mem_logPrimeBox.mpr (fun i => ⟨(hbox i).1.le, (hbox i).2⟩), hg⟩
  have hhi : ∀ t ∈ logPrimeBox lo hi ∩ primeAffineGateRegion L c,
      ∀ i, primeIcoBoxGateForms L i t ≤ primeIcoBoxGateBounds lo hi c i := by
    intro t ht
    simp only [primeIcoBoxGateForms, primeIcoBoxGateBounds, Fin.forall_fin_add,
      Fin.append_left, Fin.append_right, neg_apply, ContinuousLinearMap.proj_apply, neg_le_neg_iff]
    exact ⟨fun i => (mem_logPrimeBox.mp ht.1 i).1,
      fun i => (mem_logPrimeBox.mp ht.1 i).2.le, fun i => (ht.2 i).le⟩
  exact tendsto_actualPrimeBoxTestSum_cube_affineSandwich ha hab
    (primeIcoBoxGateForms L) (primeIcoBoxGateBounds lo hi c) (primeIcoBoxGateForms_ne_zero L hL)
    (logPrimeBox lo hi ∩ primeAffineGateRegion L c)
    ((measurableSet_logPrimeBox lo hi).inter (measurableSet_primeAffineGateRegion L c)) hlo hhi f hf

/-- Actual prime integration on the original parent cell, retaining the
original first-stop false branch and all seven strict parent rows. -/
theorem tendsto_test_original_sourceRegion
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J5 : Finset (Label5 m)) (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (f : (Fin 5 → ℝ) → ℝ)
    (hf : ContinuousOn f (univ.pi (fun _ : Fin 5 => Icc a (19 / 96 : ℝ)))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
        ((sourceRegion e chi m omega j).indicator f)) atTop
      (𝓝 (∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
        f t * ∏ i, 1 / t i)) := by
  simp only [truncatedCell_eq_inter_sourceRegion, sourceRegion_eq_if e chi m omega J5 j hj]
  by_cases hs : P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck (e : ℝ) m j = true
  · simp only [if_pos hs]
    exact tendsto_test_cube_IcoBox_affineGates ha haRho
      (logPrimeMeshLo 0 (19 / 96) m j) (logPrimeMeshHi 0 (19 / 96) m j)
      historicalUnorderedThirdGateForms (P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e m j)
      historicalUnorderedThirdGateForms_ne_zero f hf
  · simp only [if_neg hs]
    simpa only [Set.indicator_empty, actualPrimeBoxTestSum, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, inter_empty, integral_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- One actual own-cube residual, with its literal strict arithmetic
indicator, converges to its own separately gated true integral. -/
theorem tendsto_original_box_ownCubeMinus
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J5 : Finset (Label5 m)) (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (lambda : ℝ) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualPrimeBoxOwnCubeMinusSum 4 N (cap N) a (19 / 96) lambda
        (sourceRegion e chi m omega j))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
        primeOwnCubeGatedProfile lambda t * ∏ i, 1 / t i)) := by
  have herror := tendsto_actualPrimeBoxOwnCubeMinus_error 4 a (19 / 96) lambda ha haRho
    (sourceRegion e chi m omega j) cap hcap
  change Tendsto (fun N : ℕ => actualPrimeBoxOwnCubeMinusSum 4 N (cap N) a (19 / 96) lambda
      (sourceRegion e chi m omega j) - actualPrimeBoxTestSum N (fun _ : Fin 5 => a)
      (fun _ => (19 / 96 : ℝ)) ((sourceRegion e chi m omega j).indicator (primeOwnCubeGatedProfile lambda)))
    _ (𝓝 0) at herror
  have hfixed := (tendsto_test_original_sourceRegion e chi m omega a ha haRho J5 j hj
    (primeOwnCubeGatedProfile lambda) (P1OriginalFifthIntegral.continuousOn_gatedProfile ha lambda)).mono_left
      (show (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) ≤ atTop from inf_le_left)
  have hh := herror.add hfixed
  simpa only [sub_add_cancel, zero_add] using hh

/-- Additional positive truncation cuts the same original candidate
carrier.  Neither old nor new own-cube test occurs in this reindexing. -/
theorem positive_candidates_weighted_sum
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) (j : Label5 m)
    (f : (Fin 5 → ℕ) → ℝ) :
    (∑ p ∈ (firstExitFrontierTuples 4
        (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
          (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then f p else 0)) =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ)),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ sourceRegion e chi m omega j then f p else 0) := by
  let S := candidates (e : ℝ) chi m omega N cap
  have hfin : (S.filter (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i)).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) =
      (actualPrimeBoxTuples N (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈ sourceRegion e chi m omega j) := by
    have hsource := P1OriginalHistoricalFifthOwnCubeAffineGates.truncated_candidates_filter
      (e : ℝ) chi m omega N cap hN hcap j a
    have hcondition : (S.filter (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i)).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) =
        S.filter (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j ∧
          actualPrimeTupleLog N p ∈ logPrimeBox (fun _ => a) (fun _ => (19 / 96 : ℝ))) := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hp, hlarge⟩, ht⟩
        refine ⟨hp, ht, mem_logPrimeBox.mpr (fun i => ⟨hlarge i, ?_⟩)⟩
        exact (mem_logPrimeBox.mp
          (logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) < 19 / 96) m j ht) i).2
      · rintro ⟨hp, ht, hbox⟩
        exact ⟨⟨hp, fun i => (mem_logPrimeBox.mp hbox i).1⟩, ht⟩
    rw [hcondition]
    simpa only [S, sourceRegion] using hsource
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter, hfin]

def positiveCellCorrection (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (N cap : ℕ) (j : Label5 m) : ℝ :=
  ∑ p ∈ (firstExitFrontierTuples 4
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
        (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
        actualPrimeTupleOwnCubeMinus N cap (cap5 j : ℝ) p -
          actualPrimeTupleOwnCubeMinus N cap (old5 e chi m omega J4 cap4 j : ℝ) p else 0)

def smallCellRemainder (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (N cap : ℕ) (j : Label5 m) : ℝ :=
  ∑ p ∈ (firstExitFrontierTuples 4
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
        (fun p => ∃ i, actualPrimeTupleLog N p i < a),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
        actualPrimeTupleOwnCubeMinus N cap (cap5 j : ℝ) p -
          actualPrimeTupleOwnCubeMinus N cap (old5 e chi m omega J4 cap4 j : ℝ) p else 0)

def positiveCorrection (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (N cap : ℕ) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5,
    positiveCellCorrection e chi m omega a J4 cap4 J5 cap5 N cap j

def smallRemainder (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (N cap : ℕ) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5,
    smallCellRemainder e chi m omega a J4 cap4 J5 cap5 N cap j

theorem actualSaving_eq_positive_add_smallRemainder
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (N cap : ℕ) (hN : 1 < N) :
    actualHistoricalFifthSaving (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ))
        (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)) N cap ((N : ℝ) ^ (19 / 96 : ℝ)) *
          Real.log (N : ℝ) / singularSeries N =
      positiveCorrection e chi m omega a J4 cap4 J5 cap5 N cap +
        smallRemainder e chi m omega a J4 cap4 J5 cap5 N cap := by
  rw [P1OriginalCoarseFifthResidual.actualSaving_eq_cells]
  unfold positiveCorrection smallRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact P1OriginalCoarseFifthResidual.cellCorrection_eq_positiveTruncation_add_smallRemainder
    e chi m omega J4 cap4 J5 cap5 N cap hN ((N : ℝ) ^ (19 / 96 : ℝ)) a j hj

theorem positiveCellCorrection_eq_box_residual_difference
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) (j : Label5 m) :
    positiveCellCorrection e chi m omega a J4 cap4 J5 cap5 N cap j =
      actualPrimeBoxOwnCubeMinusSum 4 N cap a (19 / 96) (cap5 j : ℝ) (sourceRegion e chi m omega j) -
        actualPrimeBoxOwnCubeMinusSum 4 N cap a (19 / 96)
          (old5 e chi m omega J4 cap4 j : ℝ) (sourceRegion e chi m omega j) := by
  unfold positiveCellCorrection
  rw [positive_candidates_weighted_sum e chi m omega a N cap hN hcap j]
  unfold actualPrimeBoxOwnCubeMinusSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  split_ifs <;> ring

/-- No level-order checker is needed to subtract two true gated limits.
The h45 check belongs to the subsequent policy-saving identity. -/
theorem tendsto_positiveCellCorrection
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => positiveCellCorrection e chi m omega a J4 cap4 J5 cap5 N (cap N) j)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (P1OriginalFifthIntegral.cellIntegral e chi m omega a J4 cap4 cap5 j)) := by
  have hnew := tendsto_original_box_ownCubeMinus e chi m omega a ha haRho J5 j hj (cap5 j : ℝ) cap hcap
  have hold := tendsto_original_box_ownCubeMinus e chi m omega a ha haRho J5 j hj
    (old5 e chi m omega J4 cap4 j : ℝ) cap hcap
  have hlim := hnew.sub hold
  rw [← P1OriginalFifthIntegral.cellIntegral_eq_gated_difference e chi m omega ha J4 cap4 cap5 j] at hlim
  apply hlim.congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  exact (positiveCellCorrection_eq_box_residual_difference e chi m omega a J4 cap4 J5 cap5 N (cap N) hN hc j).symm

theorem tendsto_positiveCorrection
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => positiveCorrection e chi m omega a J4 cap4 J5 cap5 N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (P1OriginalFifthIntegral.selectedIntegral e chi m omega a J4 cap4 J5 cap5)) := by
  exact tendsto_finsetSum (selectedFifthCells e chi m omega J5) (fun j hj =>
    tendsto_positiveCellCorrection e chi m omega a ha haRho J4 cap4 J5 cap5 j hj cap hcap)

theorem tendsto_actualSaving_sub_smallRemainder
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualHistoricalFifthSaving
        (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ))
        (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)) N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) *
          Real.log (N : ℝ) / singularSeries N - smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (P1OriginalFifthIntegral.selectedIntegral e chi m omega a J4 cap4 J5 cap5)) := by
  apply (tendsto_positiveCorrection e chi m omega a ha haRho J4 cap4 J5 cap5 cap hcap).congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge] with N hN
  rw [actualSaving_eq_positive_add_smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N) hN]
  ring

theorem tendsto_actualSaving_sub_smallRemainder_ceil
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) :
    Tendsto (fun N : ℕ => actualHistoricalFifthSaving
        (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ))
        (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ))
        N (Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ))) ((N : ℝ) ^ (19 / 96 : ℝ)) *
          Real.log (N : ℝ) / singularSeries N -
        smallRemainder e chi m omega a J4 cap4 J5 cap5 N (Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ))))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (P1OriginalFifthIntegral.selectedIntegral e chi m omega a J4 cap4 J5 cap5)) := by
  exact tendsto_actualSaving_sub_smallRemainder e chi m omega a ha haRho J4 cap4 J5 cap5 _
    (Eventually.of_forall (fun N => Nat.le_ceil ((N : ℝ) ^ (19 / 96 : ℝ))))

theorem tendsto_originalFourthToFifthSaving_sub_smallRemainder
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      (firstExitRetainedPolynomial
          (fourthCappedUpperPolicy (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
            (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
            (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ)))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 ((N : ℝ) ^ (19 / 96 : ℝ))) -
        firstExitRetainedPolynomial (policy5 e chi m omega J4 cap4 J5 cap5 (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 ((N : ℝ) ^ (19 / 96 : ℝ)))) *
          Real.log (N : ℝ) / singularSeries N - smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (P1OriginalFifthIntegral.selectedIntegral e chi m omega a J4 cap4 J5 cap5)) := by
  apply (tendsto_actualSaving_sub_smallRemainder e chi m omega a ha haRho J4 cap4 J5 cap5 cap hcap).congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge] with N hN
  rw [actualFourthToFifthSaving_eq e chi m omega J4 cap4 J5 cap5 h34 h45 N (cap N) hN]

end
end ImbalancedChen.P1OriginalFifthLimit
