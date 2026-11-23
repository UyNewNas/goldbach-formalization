import ImbalancedChen.P1HistoricalFourthFullCellLimit
import ImbalancedChen.P1OriginalCoarseFourthJointGeometry
import ImbalancedChen.P1OriginalCoarseFourthResidualDictionary
import ImbalancedChen.P1OriginalCoarseFourthCellIntegral

/-!
# Actual fourth mean on the original coarse T3 policy, in a positive cube

The initial first stop, initial first cube, current third level's first
cube, third cube, and rough activation are all inherited from the literal
original coarse policy.  The old exponent is Gamma-2e, even when it is
below the initial Theta-2e.  A positive cutoff a is explicit throughout;
the complementary small-prime contribution remains an exact remainder.
-/

namespace ImbalancedChen.P1OriginalFourthLimit
noncomputable section
open Filter Topology MeasureTheory Set
open scoped Classical BigOperators
open P1FourthFullCellIntegral
open P1OriginalCoarseContinuation
open HistoricalThirdCoarse.P1OriginalFourth

/-- A fixed Ico box may use endpoints different from the ambient positive
prime cube.  Its lower faces are paid by the actual mixed-gate supplier. -/
theorem tendsto_test_cube_IcoBox_affineGates {r : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (lo hi : Fin 4 → ℝ)
    (L : Fin r → (Fin 4 → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (hL : ∀ i, L i ≠ 0)
    (f : (Fin 4 → ℝ) → ℝ)
    (hf : ContinuousOn f (univ.pi (fun _ : Fin 4 => Icc a b))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => b)
        ((logPrimeBox lo hi ∩ primeAffineGateRegion L c).indicator f)) atTop
      (𝓝 (∫ t in logPrimeBox (fun _ : Fin 4 => a) (fun _ => b) ∩
          (logPrimeBox lo hi ∩ primeAffineGateRegion L c),
        f t * ∏ i, 1 / t i)) := by
  have hlo : primeAffineGateRegion (primeIcoBoxGateForms L)
      (primeIcoBoxGateBounds lo hi c) ⊆ logPrimeBox lo hi ∩ primeAffineGateRegion L c := by
    intro t ht
    obtain ⟨hbox, hg⟩ := (mem_primeIcoBoxStrictGateRegion lo hi L c t).mp ht
    exact ⟨mem_logPrimeBox.mpr (fun i => ⟨(hbox i).1.le, (hbox i).2⟩), hg⟩
  have hhi : ∀ t ∈ logPrimeBox lo hi ∩ primeAffineGateRegion L c,
      ∀ i, primeIcoBoxGateForms L i t ≤ primeIcoBoxGateBounds lo hi c i := by
    intro t ht
    simp only [primeIcoBoxGateForms, primeIcoBoxGateBounds, Fin.forall_fin_add,
      Fin.append_left, Fin.append_right, neg_apply,
      ContinuousLinearMap.proj_apply, neg_le_neg_iff]
    exact ⟨fun i => (mem_logPrimeBox.mp ht.1 i).1,
      fun i => (mem_logPrimeBox.mp ht.1 i).2.le, fun i => (ht.2 i).le⟩
  exact tendsto_actualPrimeBoxTestSum_cube_affineSandwich ha hab
    (primeIcoBoxGateForms L) (primeIcoBoxGateBounds lo hi c) (primeIcoBoxGateForms_ne_zero L hL)
    (logPrimeBox lo hi ∩ primeAffineGateRegion L c)
    ((measurableSet_logPrimeBox lo hi).inter (measurableSet_primeAffineGateRegion L c))
    hlo hhi f hf

def sourceRegion (e : ℚ) (m : ℕ) (omega : ℝ) (j : FourthCell m) : Set (Fin 4 → ℝ) :=
  jointCell m m (prefix3 j) j ∩ jointRegion (e : ℝ) omega m (prefix3 j)

theorem sourceRegion_eq_if (e : ℚ) (m : ℕ) (omega : ℝ) (j : FourthCell m)
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m (prefix3 j) 2) :
    sourceRegion e m omega j =
      if firstStopCellCheck (e : ℝ) m j = true then
        logPrimeMeshCell 0 (19 / 96) m j ∩ primeAffineGateRegion gateForms
          (gateBounds (HistoricalThirdCoarse.initial (e : ℝ))
            (HistoricalThirdCoarse.levelExponent (e : ℝ) (HistoricalThirdCoarse.box m (prefix3 j))))
      else ∅ := by
  have hbox (R : Set (Fin 4 → ℝ)) :
      logPrimeBox (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) ∩
        (logPrimeMeshCell 0 (19 / 96) m j ∩ R) =
          logPrimeMeshCell 0 (19 / 96) m j ∩ R := by
    apply inter_eq_right.mpr
    intro t ht
    exact logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) < 19 / 96) m j ht.1
  have hh := truncatedJointRegion_eq_if (e : ℝ) omega m j 0 hwhole
  simpa only [sourceRegion, jointCell_same_mesh, truncatedJointRegion, hbox] using hh

theorem truncatedCell_eq_inter_sourceRegion (e : ℚ) (m : ℕ) (omega a : ℝ) (j : FourthCell m) :
    P1OriginalFourthIntegral.truncatedCell e m omega a j =
      logPrimeBox (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)) ∩ sourceRegion e m omega j := by
  rfl

/-- The original first-stop false branch is integrated as the empty set;
its true branch retains all six original strict cube/order forms. -/
theorem tendsto_test_original_sourceRegion
    (e : ℚ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (j : FourthCell m) (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m (prefix3 j) 2)
    (f : (Fin 4 → ℝ) → ℝ)
    (hf : ContinuousOn f (univ.pi (fun _ : Fin 4 => Icc a (19 / 96 : ℝ)))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 4 => a)
        (fun _ => (19 / 96 : ℝ)) ((sourceRegion e m omega j).indicator f)) atTop
      (𝓝 (∫ t in P1OriginalFourthIntegral.truncatedCell e m omega a j,
        f t * ∏ i, 1 / t i)) := by
  simp only [truncatedCell_eq_inter_sourceRegion, sourceRegion_eq_if e m omega j hwhole]
  by_cases hs : firstStopCellCheck (e : ℝ) m j = true
  · simp only [if_pos hs]
    exact tendsto_test_cube_IcoBox_affineGates ha haRho
      (logPrimeMeshLo 0 (19 / 96) m j) (logPrimeMeshHi 0 (19 / 96) m j)
      gateForms (gateBounds (HistoricalThirdCoarse.initial (e : ℝ))
        (HistoricalThirdCoarse.levelExponent (e : ℝ) (HistoricalThirdCoarse.box m (prefix3 j))))
      gateForms_ne_zero f hf
  · simp only [if_neg hs]
    simpa only [Set.indicator_empty, actualPrimeBoxTestSum, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, inter_empty, integral_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- The actual closed-residual supplier applies to the original coarse
Gamma, without assuming that Gamma exceeds the initial Theta. -/
theorem tendsto_original_plus_residual_error
    (e : ℚ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (j : FourthCell m) (lambda : ℝ)
    (hlevel : P1OriginalFourthIntegral.oldExponent e m j ≤ lambda)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => fourthBoxPlusResidualSumP1 N (cap N) a (19 / 96) lambda
        (sourceRegion e m omega j) -
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        ((sourceRegion e m omega j).indicator (extendedProfile lambda)))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  apply P1FourthFullCellLimit.tendsto_boxPlus_closed_error a (19 / 96) lambda ha haRho
    (sourceRegion e m omega j) ?_ cap hcap
  intro t ht
  have hh := jointRegion_strict_plus (e : ℝ) omega m (prefix3 j) t ht.2
  rw [← P1OriginalFourthIntegral.oldExponent_eq_actual] at hh
  exact hh.le.trans hlevel

theorem tendsto_original_box_plus_residual
    (e : ℚ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (j : FourthCell m) (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m (prefix3 j) 2)
    (lambda : ℝ) (hlevel : P1OriginalFourthIntegral.oldExponent e m j ≤ lambda)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => fourthBoxPlusResidualSumP1 N (cap N) a (19 / 96) lambda
        (sourceRegion e m omega j))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (∫ t in P1OriginalFourthIntegral.truncatedCell e m omega a j,
        fourthPlusProfileP1 lambda t * ∏ i, 1 / t i)) := by
  have herror := tendsto_original_plus_residual_error e m omega a ha haRho j lambda hlevel cap hcap
  have hfixed := (tendsto_test_original_sourceRegion e m omega a ha haRho j hwhole
    (extendedProfile lambda) (continuousOn_extendedProfile ha)).mono_left
      (show (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) ≤ atTop from inf_le_left)
  have heq : (∫ t in P1OriginalFourthIntegral.truncatedCell e m omega a j,
      extendedProfile lambda t * ∏ i, 1 / t i) =
      ∫ t in P1OriginalFourthIntegral.truncatedCell e m omega a j,
        fourthPlusProfileP1 lambda t * ∏ i, 1 / t i := by
    apply setIntegral_congr_fun (P1OriginalFourthIntegral.truncatedCell_measurable e m omega a j)
    intro t ht
    rw [P1OriginalFourthIntegral.rawProfile_eq_extended_on_truncated e m omega ha j hlevel ht]
  rw [heq] at hfixed
  have hh := herror.add hfixed
  simpa only [sub_add_cancel, zero_add] using hh

/-- The literal rational whole-active selection licenses its real rough
gate; this does not compare Gamma with the initial Theta. -/
theorem selected_whole_active (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4) :
    omega ≤ logPrimeMeshLo 0 (19 / 96) m (prefix3 j) 2 := by
  have hs := (mem_selectedFourthCells e chi m omega J4 j).mp hj
  have hcast : (qLogPrimeMeshLo 0 (19 / 96) m (prefix3 j) 2 : ℝ) =
      logPrimeMeshLo 0 (19 / 96) m (prefix3 j) 2 := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using
      congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m (prefix3 j)) 2
  rw [← hcast]
  exact hs.2.2

/-- The genuine admitted source in the positive cube has exactly the
same original joint-cell prime sum, for every arithmetic summand. -/
theorem positive_frontier_weighted_sum
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (f : (Fin 4 → ℕ) → ℝ) :
    (∑ p ∈ (firstExitAdmittedTuples 4
        (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
          (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then f p else 0)) =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ sourceRegion e m omega j then f p else 0) := by
  have hs := (mem_selectedFourthCells e chi m omega J4 j).mp hj
  let S := firstExitAdmittedTuples 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))
  have hfin : (S.filter (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i)).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) =
      (actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈ sourceRegion e m omega j) := by
    have hsource := truncated_admittedTuples_filter (e : ℝ) chi m omega N cap hN hcap
      j hs.2.1 (selected_whole_active e chi m omega J4 j hj) a
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
    simpa only [S, sourceRegion, jointCell_same_mesh] using hsource
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter, hfin]

def positiveCellCorrection (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (j : FourthCell m) : ℝ :=
  ∑ p ∈ (firstExitAdmittedTuples 4
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
        (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
        fourthTuplePlusResidualP1 N cap (thirdCellExponent e m j : ℝ) p -
          fourthTuplePlusResidualP1 N cap (cap4 j : ℝ) p else 0)

def smallCellRemainder (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (j : FourthCell m) : ℝ :=
  ∑ p ∈ (firstExitAdmittedTuples 4
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
        (fun p => ∃ i, actualPrimeTupleLog N p i < a),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
        fourthTuplePlusResidualP1 N cap (thirdCellExponent e m j : ℝ) p -
          fourthTuplePlusResidualP1 N cap (cap4 j : ℝ) p else 0)

def positiveCorrection (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ) (N cap : ℕ) : ℝ :=
  ∑ j ∈ selectedFourthCells e chi m omega J4,
    positiveCellCorrection e chi m omega a J4 cap4 N cap j

def smallRemainder (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ) (N cap : ℕ) : ℝ :=
  ∑ j ∈ selectedFourthCells e chi m omega J4,
    smallCellRemainder e chi m omega a J4 cap4 N cap j

/-- Every actual omitted prime tuple remains explicitly present. -/
theorem actualSaving_eq_positive_add_smallRemainder
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (hN : 1 < N) :
    actualHistoricalFourthSaving (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (level4 e chi m omega J4 cap4 (N : ℝ)) N cap ((N : ℝ) ^ (19 / 96 : ℝ)) *
        Real.log (N : ℝ) / singularSeries N =
      positiveCorrection e chi m omega a J4 cap4 N cap +
        smallRemainder e chi m omega a J4 cap4 N cap := by
  rw [P1OriginalCoarseFourthResidual.actualSaving_eq_cells]
  unfold positiveCorrection smallRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact P1OriginalCoarseFourthResidual.cellCorrection_eq_positiveTruncation_add_smallRemainder
    e chi m omega J4 cap4 N cap hN ((N : ℝ) ^ (19 / 96 : ℝ)) a j hj

theorem positiveCellCorrection_eq_box_residual_difference
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4) :
    positiveCellCorrection e chi m omega a J4 cap4 N cap j =
      fourthBoxPlusResidualSumP1 N cap a (19 / 96) (thirdCellExponent e m j : ℝ)
          (sourceRegion e m omega j) -
        fourthBoxPlusResidualSumP1 N cap a (19 / 96) (cap4 j : ℝ)
          (sourceRegion e m omega j) := by
  unfold positiveCellCorrection
  rw [positive_frontier_weighted_sum e chi m omega a J4 N cap hN hcap j hj]
  unfold fourthBoxPlusResidualSumP1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  split_ifs <;> ring

theorem tendsto_positiveCellCorrection
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => positiveCellCorrection e chi m omega a J4 cap4 N (cap N) j)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (P1OriginalFourthIntegral.cellIntegral e m omega a cap4 j)) := by
  have hwhole := selected_whole_active e chi m omega J4 j hj
  have hold := tendsto_original_box_plus_residual e m omega a ha haRho j hwhole
    (P1OriginalFourthIntegral.oldExponent e m j) le_rfl cap hcap
  have hnew := tendsto_original_box_plus_residual e m omega a ha haRho j hwhole
    (cap4 j : ℝ) (P1OriginalFourthIntegral.selected_cap_ge_old e chi m omega J4 cap4 hcheck j hj)
    cap hcap
  have hlim := hold.sub hnew
  rw [← P1OriginalFourthIntegral.cellIntegral_eq_raw_difference e chi m omega ha J4 cap4 hcheck j hj] at hlim
  apply hlim.congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  exact (positiveCellCorrection_eq_box_residual_difference e chi m omega a J4 cap4 N (cap N) hN hc j hj).symm

theorem tendsto_positiveCorrection
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => positiveCorrection e chi m omega a J4 cap4 N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (P1OriginalFourthIntegral.selectedIntegral e chi m omega a J4 cap4)) := by
  exact tendsto_finsetSum (selectedFourthCells e chi m omega J4) (fun j hj =>
    tendsto_positiveCellCorrection e chi m omega a ha haRho J4 cap4 hcheck j hj cap hcap)

/-- The original normalized actual saving minus its explicitly retained
small-prime term has the positive-cube integral limit.  No assertion that
the remainder vanishes, or that a tends to zero, is made. -/
theorem tendsto_actualSaving_sub_smallRemainder
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualHistoricalFourthSaving (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
          (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
          (level4 e chi m omega J4 cap4 (N : ℝ)) N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) *
          Real.log (N : ℝ) / singularSeries N -
        smallRemainder e chi m omega a J4 cap4 N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (P1OriginalFourthIntegral.selectedIntegral e chi m omega a J4 cap4)) := by
  apply (tendsto_positiveCorrection e chi m omega a ha haRho J4 cap4 hcheck cap hcap).congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge] with N hN
  rw [actualSaving_eq_positive_add_smallRemainder e chi m omega a J4 cap4 N (cap N) hN]
  ring

theorem tendsto_actualSaving_sub_smallRemainder_ceil
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    Tendsto (fun N : ℕ =>
      actualHistoricalFourthSaving (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
          (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
          (level4 e chi m omega J4 cap4 (N : ℝ))
          N (Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ))) ((N : ℝ) ^ (19 / 96 : ℝ)) *
          Real.log (N : ℝ) / singularSeries N -
        smallRemainder e chi m omega a J4 cap4 N (Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ))))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (P1OriginalFourthIntegral.selectedIntegral e chi m omega a J4 cap4)) := by
  exact tendsto_actualSaving_sub_smallRemainder e chi m omega a ha haRho J4 cap4 hcheck _
    (Eventually.of_forall (fun N => Nat.le_ceil ((N : ℝ) ^ (19 / 96 : ℝ))))

/-- The finite level check compares the fourth replacement with the
actual inherited coarse level on the original initial-first-stop tree. -/
theorem originalPolicySaving_eq
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) :
    firstExitRetainedPolynomial (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial
        (fourthCappedUpperPolicy (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
          (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
          (level4 e chi m omega J4 cap4 (N : ℝ)))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (level4 e chi m omega J4 cap4 (N : ℝ)) N cap z := by
  apply actualHistoricalFourthSaving_eq
  intro state hstate
  have hlen := firstExitDepthFrontier_selected_length 4 _ _ [] _ true 1 (by simp) state hstate
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 4 _
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap 0 z) state hstate
  have hpos : ∀ p ∈ state.selectedPrefix, 0 < p := by
    intro p hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))).pos
  exact frozenLevel_le_level4 e chi m omega J4 cap4 (N : ℝ) state.selectedPrefix
    hcheck (by exact_mod_cast hN) hlen hpos

theorem tendsto_originalPolicySaving_sub_smallRemainder
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      (firstExitRetainedPolynomial (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 ((N : ℝ) ^ (19 / 96 : ℝ))) -
        firstExitRetainedPolynomial
          (fourthCappedUpperPolicy (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
            (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
            (level4 e chi m omega J4 cap4 (N : ℝ)))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 ((N : ℝ) ^ (19 / 96 : ℝ)))) *
          Real.log (N : ℝ) / singularSeries N -
        smallRemainder e chi m omega a J4 cap4 N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (P1OriginalFourthIntegral.selectedIntegral e chi m omega a J4 cap4)) := by
  apply (tendsto_actualSaving_sub_smallRemainder e chi m omega a ha haRho J4 cap4 hcheck cap hcap).congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge] with N hN
  rw [originalPolicySaving_eq e chi m omega J4 cap4 hcheck N (cap N) hN]

end
end ImbalancedChen.P1OriginalFourthLimit
