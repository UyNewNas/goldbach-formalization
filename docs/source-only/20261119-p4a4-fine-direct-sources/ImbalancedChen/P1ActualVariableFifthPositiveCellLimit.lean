import ImbalancedChen.P1ActualVariableFifthProfiles

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

True fixed-positive-cut limit for the ACTUAL VARIABLE fifth maximum.
Shared actual fourth-row atoms fix only fourth eligibility; every fifth
row owned by this cell with its literal gateCheck enters a continuous
finite maximum over that atom's moving original fourth profile. The
canonical lower zero extension retains both strict own-cube indicators.

The arithmetic approximation is the proved uniform bounded-level quotient
estimate, and the prime TEST integral is proved from the original mixed
affine source supplier. No desired mean, stored cap, fixed winning row or
all15 identification is assumed. Full small-last-prime tails remain OPEN.
-/

namespace ImbalancedChen.P1ActualVariableFifthPositiveCellLimit

noncomputable section
open Filter Topology MeasureTheory Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation P1CorrectedFifthDensityDictionary
open P1OriginalVariableFourthEligibilityPartition P1ActualVariableFifthProfiles

abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

private theorem finiteMax_filter_all {ι : Type*} (rows : Finset ι)
    (eligible : ι → Prop) (f : ι → ℝ) (a : ℝ) :
    finiteMax rows eligible f a = finiteMax (rows.filter eligible) (fun _ => True) f a := by
  simp [finiteMax, finiteValues]

private theorem finiteMax_insert_all {ι : Type*} (rows : Finset ι)
    (f : ι → ℝ) (a : ℝ) (r : ι) :
    finiteMax (insert r rows) (fun _ => True) f a =
      max (f r) (finiteMax rows (fun _ => True) f a) := by
  simp [finiteMax, finiteValues, Finset.image_insert, Finset.insert_comm, Finset.max'_insert]

private theorem continuous_finiteMax_moving {ι : Type*} (rows : Finset ι)
    (f : ι → Point5 → ℝ) (a : Point5 → ℝ) (ha : Continuous a) :
    (∀ r ∈ rows, Continuous (f r)) →
      Continuous (fun t => finiteMax rows (fun _ => True) (fun r => f r t) (a t)) := by
  induction rows using Finset.induction_on with
  | empty =>
    intro _hf
    simpa [finiteMax, finiteValues] using ha
  | @insert r rows hr ih =>
    intro hf
    have hcont := (hf r (Finset.mem_insert_self _ _)).sup
      (ih (fun s hs => hf s (Finset.mem_insert_of_mem hs)))
    simpa only [finiteMax_insert_all] using hcont

def fixedNext5 (e : ℚ) (m : ℕ) (j : Label5 m)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (s : Pattern rows4) (rows5 : Finset (FifthRow m)) (t : Point5) : ℝ :=
  finiteMax rows5 (ownerEligible e m j) (fun r => candidate (e : ℝ) r.selected t)
    (P1ActualVariableFourthFifthCellTestLimit.fixedOld4 (e : ℝ)
      (P1ActualVariableFourthFifthCellTestLimit.selectedSeed e m j) rows4 licensed4 s t)

theorem continuous_fixedNext5 (e : ℚ) (m : ℕ) (j : Label5 m)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (s : Pattern rows4) (rows5 : Finset (FifthRow m)) :
    Continuous (fixedNext5 e m j rows4 licensed4 s rows5) := by
  unfold fixedNext5
  have hcont := continuous_finiteMax_moving (rows5.filter (ownerEligible e m j))
    (fun r t => candidate (e : ℝ) r.selected t)
    (P1ActualVariableFourthFifthCellTestLimit.fixedOld4 (e : ℝ)
      (P1ActualVariableFourthFifthCellTestLimit.selectedSeed e m j) rows4 licensed4 s)
    (P1ActualVariableFourthFifthCellTestLimit.continuous_fixedOld4
      (e : ℝ) (P1ActualVariableFourthFifthCellTestLimit.selectedSeed e m j) rows4 licensed4 s)
    (by
      intro r _hr
      have hsum : Continuous (fun t : Point5 => ∑ i ∈ r.selected, t i) := by fun_prop
      simpa only [candidate, envelope_eq_v] using
        (VariableEnvelope.continuous_v.comp hsum).sub continuous_const)
  simpa only [finiteMax, finiteValues, Finset.filter_true] using hcont

def actualNewTest (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) (t : Point5) : ℝ :=
  primeOwnCubeGatedProfile (actualNext5 e chi m omega j rows4 licensed4 rows5 t) t

def fixedNewTest (e : ℚ) (m : ℕ) (j : Label5 m)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (s : Pattern rows4) (rows5 : Finset (FifthRow m)) (t : Point5) : ℝ :=
  primeOwnCubeGatedProfile (fixedNext5 e m j rows4 licensed4 s rows5 t) t

theorem continuousOn_fixedNewTest
    (e : ℚ) (m : ℕ) (j : Label5 m) (a b : ℝ) (ha : 0 < a)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (s : Pattern rows4) (rows5 : Finset (FifthRow m)) :
    ContinuousOn (fixedNewTest e m j rows4 licensed4 s rows5)
      (univ.pi (fun _ : Fin 5 => Icc a b)) :=
  P1LiteralVariableFifthCompactSupplier.continuousOn_movingOwnCubeProfile a b ha _
    (continuous_fixedNext5 e m j rows4 licensed4 s rows5)

/-- The same ACTUAL fourth eligibility atom fixes the entire fifth moving
maximum, while every allowed fifth row remains in that maximum. -/
theorem actualNext5_eq_fixed_on_atom
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) (s : Pattern rows4)
    {t : Point5} (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hatom : t ∈ P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4 s) :
    actualNext5 e chi m omega j rows4 licensed4 rows5 t =
      fixedNext5 e m j rows4 licensed4 s rows5 t := by
  unfold actualNext5 fixedNext5
  rw [P1ActualVariableFourthFifthCellTestLimit.actualOld4_eq_fixed_on_atom
    e chi m omega J5 j hj rows4 licensed4 s ht hatom]

theorem actual_source_newTest_eq_sum_atoms
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) (t : Point5) :
    (P1OriginalFifthLimit.sourceRegion e chi m omega j).indicator
        (actualNewTest e chi m omega j rows4 licensed4 rows5) t =
      ∑ s : Pattern rows4,
        (P1OriginalFifthLimit.sourceRegion e chi m omega j ∩
          P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4 s).indicator
          (fixedNewTest e m j rows4 licensed4 s rows5) t := by
  rw [Finset.sum_eq_single
    (actualPattern rows4 (P1ActualVariableFourthFifthCellTestLimit.firstFour t))]
  · by_cases ht : t ∈ P1OriginalFifthLimit.sourceRegion e chi m omega j
    · have ha : t ∈ P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4
          (actualPattern rows4 (P1ActualVariableFourthFifthCellTestLimit.firstFour t)) :=
        mem_actual_wallAtom rows4 (P1ActualVariableFourthFifthCellTestLimit.firstFour t)
      simp only [indicator_of_mem ht, indicator_of_mem (show t ∈
          P1OriginalFifthLimit.sourceRegion e chi m omega j ∩
            P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4
              (actualPattern rows4 (P1ActualVariableFourthFifthCellTestLimit.firstFour t)) from ⟨ht, ha⟩),
        actualNewTest, fixedNewTest,
        actualNext5_eq_fixed_on_atom e chi m omega J5 j hj rows4 licensed4 rows5 _ ht.1 ha]
    · simp only [indicator_of_not_mem ht, indicator_of_not_mem
        (show t ∉ P1OriginalFifthLimit.sourceRegion e chi m omega j ∩
          P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4
            (actualPattern rows4 (P1ActualVariableFourthFifthCellTestLimit.firstFour t)) from
              fun h => ht h.1)]
  · intro s _hs hne
    apply indicator_of_not_mem
    intro ht
    exact hne (wallAtom_unique ht.2
      (mem_actual_wallAtom rows4 (P1ActualVariableFourthFifthCellTestLimit.firstFour t)))
  · simp

theorem actual_new_primeTest_eq_sum_atoms
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a b : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) (N : ℕ) :
    actualPrimeBoxTestSum N (fun _ : Fin 5 => a) (fun _ => b)
        ((P1OriginalFifthLimit.sourceRegion e chi m omega j).indicator
          (actualNewTest e chi m omega j rows4 licensed4 rows5)) =
      ∑ s : Pattern rows4, actualPrimeBoxTestSum N (fun _ : Fin 5 => a) (fun _ => b)
        ((P1OriginalFifthLimit.sourceRegion e chi m omega j ∩
          P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4 s).indicator
          (fixedNewTest e m j rows4 licensed4 s rows5)) := by
  unfold actualPrimeBoxTestSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [actual_source_newTest_eq_sum_atoms e chi m omega J5 j hj rows4 licensed4 rows5,
    Finset.mul_sum]

theorem integrableOn_fixedNewTest_weight
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (j : Label5 m)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (s : Pattern rows4) (rows5 : Finset (FifthRow m)) :
    IntegrableOn (fun t => fixedNewTest e m j rows4 licensed4 s rows5 t * ∏ i, 1 / t i)
      (P1OriginalFifthIntegral.truncatedCell e chi m omega a j) := by
  have hc := (continuousOn_fixedNewTest e m j a (19 / 96) ha rows4 licensed4 s rows5).mul
    (P1OriginalFifthIntegral.continuousOn_reciprocalWeight ha)
  exact (hc.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set
    (P1OriginalFifthIntegral.truncatedCell_subset_closedBox e chi m omega a j)

theorem actualNew5_integral_eq_sum_atoms
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) :
    (∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
      actualNewTest e chi m omega j rows4 licensed4 rows5 t * ∏ i, 1 / t i) =
      ∑ s : Pattern rows4,
        ∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j ∩
            P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4 s,
          fixedNewTest e m j rows4 licensed4 s rows5 t * ∏ i, 1 / t i := by
  have hint (s : Pattern rows4) : IntegrableOn
      ((P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4 s).indicator
        (fun t => fixedNewTest e m j rows4 licensed4 s rows5 t * ∏ i, 1 / t i))
      (P1OriginalFifthIntegral.truncatedCell e chi m omega a j) :=
    (integrableOn_fixedNewTest_weight e chi m omega a ha j rows4 licensed4 s rows5).indicator
      (P1ActualVariableFourthFifthCellTestLimit.measurableSet_liftedAtom rows4 s)
  calc
    _ = ∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
        ∑ s : Pattern rows4,
          (P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4 s).indicator
            (fun t => fixedNewTest e m j rows4 licensed4 s rows5 t * ∏ i, 1 / t i) t := by
      apply setIntegral_congr_fun (P1OriginalFifthIntegral.truncatedCell_measurable e chi m omega a j)
      intro t ht
      have hs : t ∈ P1OriginalFifthLimit.sourceRegion e chi m omega j := ht.2
      have h := actual_source_newTest_eq_sum_atoms e chi m omega J5 j hj rows4 licensed4 rows5 t
      simp only [indicator_of_mem hs] at h
      rw [h, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _hs
      by_cases ha : t ∈ P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4 s
      · simp only [indicator_of_mem ⟨hs, ha⟩, indicator_of_mem ha]
      · simp only [indicator_of_not_mem ha, indicator_of_not_mem
          (show t ∉ P1OriginalFifthLimit.sourceRegion e chi m omega j ∩
            P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4 s from fun hh => ha hh.2), zero_mul]
    _ = ∑ s : Pattern rows4, ∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
        (P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4 s).indicator
          (fun t => fixedNewTest e m j rows4 licensed4 s rows5 t * ∏ i, 1 / t i) t :=
      integral_finsetSum _ (fun s _hs => hint s)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [setIntegral_indicator
        (P1ActualVariableFourthFifthCellTestLimit.measurableSet_liftedAtom rows4 s)]

theorem integrableOn_actualNew5_weight
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) :
    IntegrableOn (fun t => actualNewTest e chi m omega j rows4 licensed4 rows5 t * ∏ i, 1 / t i)
      (P1OriginalFifthIntegral.truncatedCell e chi m omega a j) := by
  have hint (s : Pattern rows4) : IntegrableOn
      ((P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4 s).indicator
        (fun t => fixedNewTest e m j rows4 licensed4 s rows5 t * ∏ i, 1 / t i))
      (P1OriginalFifthIntegral.truncatedCell e chi m omega a j) :=
    (integrableOn_fixedNewTest_weight e chi m omega a ha j rows4 licensed4 s rows5).indicator
      (P1ActualVariableFourthFifthCellTestLimit.measurableSet_liftedAtom rows4 s)
  apply (integrable_finsetSum (Finset.univ : Finset (Pattern rows4)) (fun s _hs => hint s)).congr_fun
    ?_ (P1OriginalFifthIntegral.truncatedCell_measurable e chi m omega a j)
  intro t ht
  have hs : t ∈ P1OriginalFifthLimit.sourceRegion e chi m omega j := ht.2
  have h := actual_source_newTest_eq_sum_atoms e chi m omega J5 j hj rows4 licensed4 rows5 t
  simp only [indicator_of_mem hs] at h
  rw [h, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases ha : t ∈ P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4 s
  · simp only [indicator_of_mem ⟨hs, ha⟩, indicator_of_mem ha]
  · simp only [indicator_of_not_mem ha, indicator_of_not_mem
      (show t ∉ P1OriginalFifthLimit.sourceRegion e chi m omega j ∩
        P1ActualVariableFourthFifthCellTestLimit.liftedAtom rows4 s from fun hh => ha hh.2), zero_mul]

theorem tendsto_actualNew5_positiveCell_integral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (hab : a < (19 / 96 : ℝ))
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
        (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
        ((P1OriginalFifthLimit.sourceRegion e chi m omega j).indicator
          (actualNewTest e chi m omega j rows4 licensed4 rows5))) atTop
      (𝓝 (∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
        actualNewTest e chi m omega j rows4 licensed4 rows5 t * ∏ i, 1 / t i)) := by
  rw [actualNew5_integral_eq_sum_atoms e chi m omega a ha J5 j hj rows4 licensed4 rows5]
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Pattern rows4)) (fun s _hs =>
    P1ActualVariableFourthFifthCellTestLimit.tendsto_original_source_liftedAtom_test
      e chi m omega a ha hab J5 j hj rows4 s _
        (continuousOn_fixedNewTest e m j a (19 / 96) ha rows4 licensed4 s rows5))
  apply hlim.congr'
  exact Eventually.of_forall (fun N =>
    (actual_new_primeTest_eq_sum_atoms e chi m omega a (19 / 96) J5 j hj rows4 licensed4 rows5 N).symm)

def gatedDifference (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) (t : Point5) : ℝ :=
  actualNewTest e chi m omega j rows4 licensed4 rows5 t -
    P1ActualVariableFourthFifthCellTestLimit.actualOldTest e chi omega m j rows4 licensed4 t

def variableCellKernel (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) (t : Point5) : ℝ :=
  gatedDifference e chi m omega j rows4 licensed4 rows5 t * ∏ i, 1 / t i

def variableCellIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (j : Label5 m)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) : ℝ :=
  ∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
    variableCellKernel e chi m omega j rows4 licensed4 rows5 t

theorem integrableOn_actualVariable5_kernel
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) :
    IntegrableOn (variableCellKernel e chi m omega j rows4 licensed4 rows5)
      (P1OriginalFifthIntegral.truncatedCell e chi m omega a j) := by
  simpa only [variableCellKernel, gatedDifference, sub_mul] using
    (integrableOn_actualNew5_weight e chi m omega a ha J5 j hj rows4 licensed4 rows5).sub
      (P1ActualVariableFourthFifthCellTestLimit.integrableOn_actualOld4_weight
        e chi m omega a ha J5 j hj rows4 licensed4)

theorem tendsto_gatedTest_integral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (hab : a < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
        (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
        (fun t => if t ∈ P1OriginalFifthLimit.sourceRegion e chi m omega j then
          gatedDifference e chi m omega j rows4 licensed4 rows5 t else 0)) atTop
      (𝓝 (variableCellIntegral e chi m omega a j rows4 licensed4 rows5)) := by
  have hnew := tendsto_actualNew5_positiveCell_integral
    e chi m omega a ha hab J5 j hj rows4 licensed4 rows5
  have hold := P1ActualVariableFourthFifthCellTestLimit.tendsto_actualOld4_positiveCell_integral
    e chi m omega a ha hab J5 j hj rows4 licensed4
  have hIntegral : variableCellIntegral e chi m omega a j rows4 licensed4 rows5 =
      (∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
        actualNewTest e chi m omega j rows4 licensed4 rows5 t * ∏ i, 1 / t i) -
      ∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
        P1ActualVariableFourthFifthCellTestLimit.actualOldTest e chi omega m j rows4 licensed4 t *
          ∏ i, 1 / t i := by
    unfold variableCellIntegral variableCellKernel gatedDifference
    simp_rw [sub_mul]
    exact integral_sub
      (integrableOn_actualNew5_weight e chi m omega a ha J5 j hj rows4 licensed4 rows5)
      (P1ActualVariableFourthFifthCellTestLimit.integrableOn_actualOld4_weight
        e chi m omega a ha J5 j hj rows4 licensed4)
  rw [hIntegral]
  apply (hnew.sub hold).congr'
  apply Eventually.of_forall
  intro N
  symm
  exact P1CorrectedFifthCellArithmeticError.actualPrimeBoxTestSum_region_sub N
    (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
    (P1OriginalFifthLimit.sourceRegion e chi m omega j)
    (actualNewTest e chi m omega j rows4 licensed4 rows5)
    (P1ActualVariableFourthFifthCellTestLimit.actualOldTest e chi omega m j rows4 licensed4)

/-- Both actual moving levels are approximated uniformly before taking
their difference. No continuity of the global row-changing profile is used. -/
theorem tendsto_positiveCellCharge_sub_gatedTest
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (hab : a < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => positiveCellCharge e chi m omega rows4 licensed4 J5 rows5 a N (cap N) j -
      actualPrimeBoxTestSum N (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
        (fun t => if t ∈ P1OriginalFifthLimit.sourceRegion e chi m omega j then
          gatedDifference e chi m omega j rows4 licensed4 rows5 t else 0))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  let R := P1OriginalFifthLimit.sourceRegion e chi m omega j
  let old := originalVariableFourthProfile e chi omega m j rows4 licensed4
  let new := actualNext5 e chi m omega j rows4 licensed4 rows5
  let oldSum (N : ℕ) := P1VariableOwnCubeResidualUniformity.actualPrimeBoxVariableOwnCubeMinusSum
    4 N (cap N) a (19 / 96) old R
  let newSum (N : ℕ) := P1VariableOwnCubeResidualUniformity.actualPrimeBoxVariableOwnCubeMinusSum
    4 N (cap N) a (19 / 96) new R
  let oldTest (N : ℕ) := actualPrimeBoxTestSum N (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
    (fun t => if t ∈ R then primeOwnCubeGatedProfile (old t) t else 0)
  let newTest (N : ℕ) := actualPrimeBoxTestSum N (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
    (fun t => if t ∈ R then primeOwnCubeGatedProfile (new t) t else 0)
  have hnew : Tendsto (fun N : ℕ => newSum N - newTest N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) :=
    P1VariableOwnCubeResidualUniformity.tendsto_actualPrimeBoxVariableOwnCubeMinus_error
      4 a (19 / 96) (lowerLevel e chi m j) (upperLevel e chi m j) ha hab new
      (fun t _ht => actualNext5_mem_interval e chi m omega j rows4 licensed4 rows5 t) R cap hcap
  have hold : Tendsto (fun N : ℕ => oldSum N - oldTest N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) :=
    P1VariableOwnCubeResidualUniformity.tendsto_actualPrimeBoxVariableOwnCubeMinus_error
      4 a (19 / 96) (lowerLevel e chi m j) (upperLevel e chi m j) ha hab old
      (fun t _ht => actualOld4_mem_interval e chi m omega j rows4 licensed4 t) R cap hcap
  have hdiff : Tendsto (fun N : ℕ => (newSum N - newTest N) - (oldSum N - oldTest N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
    simpa only [sub_self] using hnew.sub hold
  apply hdiff.congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  rw [positiveCellCharge_eq_residualSums e chi m omega a rows4 licensed4 J5 rows5 N (cap N) hN hc j hj]
  have htest : actualPrimeBoxTestSum N (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
      (fun t => if t ∈ R then gatedDifference e chi m omega j rows4 licensed4 rows5 t else 0) =
      newTest N - oldTest N :=
    P1CorrectedFifthCellArithmeticError.actualPrimeBoxTestSum_region_sub N
      (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ)) R
        (fun t => primeOwnCubeGatedProfile (new t) t)
        (fun t => primeOwnCubeGatedProfile (old t) t)
  rw [htest]
  change (newSum N - newTest N) - (oldSum N - oldTest N) =
    (newSum N - oldSum N) - (newTest N - oldTest N)
  ring

/-- True normalized ACTUAL VARIABLE fifth positive-cell charge limit.
h45 is automatic from the inherited fourth floor; no stored-cap check or
desired density mean occurs among these premises. -/
theorem tendsto_positiveCellCharge
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (hab : a < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => positiveCellCharge e chi m omega rows4 licensed4 J5 rows5 a N (cap N) j)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (variableCellIntegral e chi m omega a j rows4 licensed4 rows5)) := by
  have htest := (tendsto_gatedTest_integral e chi m omega a ha hab rows4 licensed4 J5 rows5 j hj).mono_left
    (show (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) ≤ atTop from inf_le_left)
  have herror := tendsto_positiveCellCharge_sub_gatedTest
    e chi m omega a ha hab rows4 licensed4 J5 rows5 j hj cap hcap
  simpa only [sub_add_cancel, zero_add] using herror.add htest

end
end ImbalancedChen.P1ActualVariableFifthPositiveCellLimit
