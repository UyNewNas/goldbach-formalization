import ImbalancedChen.P1CorrectedFifthVariableResidualApproximation
import ImbalancedChen.P1OriginalVariableFourthEligibilityPartition
import ImbalancedChen.P1LiteralVariableFifthCompactSupplier
import ImbalancedChen.P1OriginalCoarseFifthCellLimit
import ImbalancedChen.P1CorrectedFifthCellArithmeticError

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The ACTUAL original variable-fourth producer on a selected fifth owner is
refined by pulling back the existing fourth eligibility atoms through the
first-four-coordinate projection. No second atom definition is introduced.
The original rough activation and selected raw-Q3 seed are proved constant
on that selected owner. Every eligible producer row and every box-face
prime atom survives the mixed affine refinement.

The genuine old own-cube LOWER test is continuous separately on each atom,
using the canonical zero extension at residual parameter two. Its actual
target-deleted prime test has the true finite sum of refined integrals as
its limit. No all15 surrogate, fixed-eligibility premise, desired mean or
arithmetic residual limit is assumed. Removing the positive cut is OPEN.
-/

namespace ImbalancedChen.P1ActualVariableFourthFifthCellTestLimit

noncomputable section
open Filter Topology MeasureTheory Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation P1OriginalVariableFourthCellTestLimit
open P1OriginalVariableFourthEligibilityPartition
open P1CorrectedFifthDensityDictionary

abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := P1OriginalCoarseFifthContinuation.Label5 m

def firstFour : Point5 →L[ℝ] Point :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (i.castLE (by decide : 4 ≤ 5)))

theorem firstFour_apply (t : Point5) :
    firstFour t = historicalPrefixProject (by decide : 4 ≤ 5) t := rfl

/-- Pullback of the shared fourth atoms, including their exact weak faces. -/
def liftedAtom (rows : Finset ProducerRow) (s : Pattern rows) : Set Point5 :=
  firstFour ⁻¹' wallAtom rows s

theorem measurableSet_liftedAtom (rows : Finset ProducerRow) (s : Pattern rows) :
    MeasurableSet (liftedAtom rows s) :=
  (measurableSet_wallAtom rows s).preimage firstFour.continuous.measurable

theorem liftedWall_ne_zero {rows : Finset ProducerRow} (k : WallKey rows) :
    (wallForm k).comp firstFour ≠ 0 := by
  intro h
  have hh := congrArg (fun F : Point5 →L[ℝ] ℝ => F (fun _ => 1)) h
  cases hs : k.2.2 <;>
    simp [ContinuousLinearMap.comp_apply, wallForm, hs, firstFour] at hh

def fixedOld4 (e seed : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (s : Pattern rows) (t : Point5) : ℝ :=
  fixedCellExponent e rows (eligibleRows rows licensed s) seed (firstFour t)

theorem continuous_fixedOld4 (e seed : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (s : Pattern rows) :
    Continuous (fixedOld4 e seed rows licensed s) :=
  (continuous_fixedCellExponent e rows (eligibleRows rows licensed s) seed).comp firstFour.continuous

def fixedOldTest (e seed : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (s : Pattern rows) (t : Point5) : ℝ :=
  primeOwnCubeGatedProfile (fixedOld4 e seed rows licensed s t) t

theorem continuousOn_fixedOldTest (e seed a b : ℝ) (ha : 0 < a)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (s : Pattern rows) :
    ContinuousOn (fixedOldTest e seed rows licensed s)
      (univ.pi (fun _ : Fin 5 => Icc a b)) :=
  P1LiteralVariableFifthCompactSupplier.continuousOn_movingOwnCubeProfile a b ha _
    (continuous_fixedOld4 e seed rows licensed s)

/-- Whole-cell activation is a consequence of the actual fifth selection.
The selected seed is Gamma-2e, including when it is below initial Theta. -/
theorem original_seed_constant_on_selected_owner
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    {t : Point5} (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    omega ≤ t 2 ∧
      HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent
          (e : ℝ) chi m omega j t =
        HistoricalThirdCoarse.levelExponent (e : ℝ)
          (HistoricalThirdCoarse.box m (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner j)) := by
  exact ⟨P1OriginalHistoricalFifthOwnCubeAffineGates.selected_cell_rough
      e chi m omega J5 j hj ht,
    P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
      e chi m omega J5 j hj ht⟩

def selectedSeed (e : ℚ) (m : ℕ) (j : Label5 m) : ℝ :=
  HistoricalThirdCoarse.levelExponent (e : ℝ)
    (HistoricalThirdCoarse.box m (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner j))

/-- Fixed eligibility is constructed by the shared atom, rather than
assumed. The old profile here is the ACTUAL producer dictionary profile. -/
theorem actualOld4_eq_fixed_on_atom
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (s : Pattern rows)
    {t : Point5} (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hatom : t ∈ liftedAtom rows s) :
    originalVariableFourthProfile e chi omega m j rows licensed t =
      fixedOld4 (e : ℝ) (selectedSeed e m j) rows licensed s t := by
  have hs := (original_seed_constant_on_selected_owner e chi m omega J5 j hj ht).2
  unfold originalVariableFourthProfile
  rw [hs]
  change producerProfile4 (e : ℝ) rows licensed (selectedSeed e m j) (firstFour t) = _
  exact producerProfile_eq_fixed_on_atom (e : ℝ) (selectedSeed e m j) rows licensed s hatom

/-- Any true original selected source admits the pulled-back row atoms.
The affine supplier pays the exact mixed weak/strict walls pointwise. -/
theorem tendsto_original_source_liftedAtom_test
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows : Finset ProducerRow) (s : Pattern rows)
    (f : Point5 → ℝ) (hf : ContinuousOn f (univ.pi (fun _ : Fin 5 => Icc a (19 / 96 : ℝ)))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
        (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
        ((P1OriginalFifthLimit.sourceRegion e chi m omega j ∩ liftedAtom rows s).indicator f)) atTop
      (𝓝 (∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j ∩ liftedAtom rows s,
        f t * ∏ i, 1 / t i)) := by
  rw [P1OriginalFifthLimit.truncatedCell_eq_inter_sourceRegion, inter_assoc]
  rw [P1OriginalFifthLimit.sourceRegion_eq_if e chi m omega J5 j hj]
  by_cases hs : P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck (e : ℝ) m j = true
  · simp only [if_pos hs]
    let lo := logPrimeMeshLo 0 (19 / 96) m j
    let hi := logPrimeMeshHi 0 (19 / 96) m j
    let L := historicalUnorderedThirdGateForms
    let c := P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e m j
    let baseL := primeIcoBoxGateForms L
    let baseC := primeIcoBoxGateBounds lo hi c
    let O : WallKey rows → Point5 →L[ℝ] ℝ :=
      fun k => if s k then (wallForm k).comp firstFour else -((wallForm k).comp firstFour)
    let d : WallKey rows → ℝ := fun k => if s k then wallBound k else -wallBound k
    apply tendsto_test_finite_mixed_gates a (19 / 96) ha haRho
      (Sum.elim baseL O) (Sum.elim baseC d) ?_
      ((logPrimeMeshCell 0 (19 / 96) m j ∩ primeAffineGateRegion L c) ∩ liftedAtom rows s)
      ?_ ?_ ?_ f hf
    · intro k
      cases k with
      | inl k => exact primeIcoBoxGateForms_ne_zero L historicalUnorderedThirdGateForms_ne_zero k
      | inr k =>
        cases hsk : s k <;> simp only [Sum.elim_inr, O, hsk, Bool.false_eq_true, if_false, if_true]
        · exact neg_ne_zero.mpr (liftedWall_ne_zero k)
        · exact liftedWall_ne_zero k
    · exact ((measurableSet_logPrimeMeshCell 0 (19 / 96) m j).inter
        (measurableSet_primeAffineGateRegion L c)).inter (measurableSet_liftedAtom rows s)
    · intro t ht
      have hb := (mem_primeIcoBoxStrictGateRegion lo hi L c t).mp (fun k => ht (Sum.inl k))
      refine ⟨⟨mem_logPrimeBox.mpr (fun i => ⟨(hb.1 i).1.le, (hb.1 i).2⟩), hb.2⟩, ?_⟩
      intro k
      have hk := ht (Sum.inr k)
      cases hsk : s k
      · simpa only [Sum.elim_inr, O, d, hsk, Bool.false_eq_true, if_false,
          neg_apply, neg_lt_neg_iff, ContinuousLinearMap.comp_apply] using hk
      · have hk' : wallForm k (firstFour t) < wallBound k := by
          simpa only [Sum.elim_inr, O, d, hsk, if_true,
            ContinuousLinearMap.comp_apply] using hk
        simpa only [hsk, if_true] using hk'.le
    · intro t ht k
      cases k with
      | inl k =>
        have hb : ∀ k, baseL k t ≤ baseC k := by
          simp only [baseL, baseC, primeIcoBoxGateForms, primeIcoBoxGateBounds,
            Fin.forall_fin_add, Fin.append_left, Fin.append_right, neg_apply,
            ContinuousLinearMap.proj_apply, neg_le_neg_iff]
          exact ⟨fun i => (mem_logPrimeBox.mp ht.1.1 i).1,
            fun i => (mem_logPrimeBox.mp ht.1.1 i).2.le, fun q => (ht.1.2 q).le⟩
        exact hb k
      | inr k =>
        have hk := ht.2 k
        cases hsk : s k
        · have hk' : wallBound k < wallForm k (firstFour t) := by
            simpa only [hsk, Bool.false_eq_true, if_false] using hk
          simpa only [Sum.elim_inr, O, d, hsk, Bool.false_eq_true, if_false,
            neg_apply, neg_le_neg_iff, ContinuousLinearMap.comp_apply] using hk'.le
        · simpa only [Sum.elim_inr, O, d, hsk, if_true,
            ContinuousLinearMap.comp_apply] using hk
  · simp only [if_neg hs, empty_inter, inter_empty, indicator_empty,
      actualPrimeBoxTestSum, Pi.zero_apply, mul_zero, Finset.sum_const_zero, integral_empty]
    exact tendsto_const_nhds

def actualOldTest (e : ℚ) (chi omega : ℝ) (m : ℕ) (j : Label5 m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (t : Point5) : ℝ :=
  primeOwnCubeGatedProfile (originalVariableFourthProfile e chi omega m j rows licensed t) t

/-- Exact finite decomposition before taking any prime limit. Faces and
losing eligible candidates are retained, and no global continuity is used. -/
theorem actual_source_test_eq_sum_atoms
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (t : Point5) :
    (P1OriginalFifthLimit.sourceRegion e chi m omega j).indicator
        (actualOldTest e chi omega m j rows licensed) t =
      ∑ s : Pattern rows,
        (P1OriginalFifthLimit.sourceRegion e chi m omega j ∩ liftedAtom rows s).indicator
          (fixedOldTest (e : ℝ) (selectedSeed e m j) rows licensed s) t := by
  rw [Finset.sum_eq_single (actualPattern rows (firstFour t))]
  · by_cases ht : t ∈ P1OriginalFifthLimit.sourceRegion e chi m omega j
    · have ha : t ∈ liftedAtom rows (actualPattern rows (firstFour t)) :=
        mem_actual_wallAtom rows (firstFour t)
      simp only [indicator_of_mem ht, indicator_of_mem (show t ∈
          P1OriginalFifthLimit.sourceRegion e chi m omega j ∩
            liftedAtom rows (actualPattern rows (firstFour t)) from ⟨ht, ha⟩),
        actualOldTest, fixedOldTest,
        actualOld4_eq_fixed_on_atom e chi m omega J5 j hj rows licensed _ ht.1 ha]
    · simp only [indicator_of_not_mem ht, indicator_of_not_mem
        (show t ∉ P1OriginalFifthLimit.sourceRegion e chi m omega j ∩
          liftedAtom rows (actualPattern rows (firstFour t)) from fun h => ht h.1)]
  · intro s _ hne
    apply indicator_of_not_mem
    intro ht
    exact hne (wallAtom_unique ht.2 (mem_actual_wallAtom rows (firstFour t)))
  · simp

theorem actual_prime_test_eq_sum_atoms
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a b : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (N : ℕ) :
    actualPrimeBoxTestSum N (fun _ : Fin 5 => a) (fun _ => b)
        ((P1OriginalFifthLimit.sourceRegion e chi m omega j).indicator
          (actualOldTest e chi omega m j rows licensed)) =
      ∑ s : Pattern rows, actualPrimeBoxTestSum N (fun _ : Fin 5 => a) (fun _ => b)
        ((P1OriginalFifthLimit.sourceRegion e chi m omega j ∩ liftedAtom rows s).indicator
          (fixedOldTest (e : ℝ) (selectedSeed e m j) rows licensed s)) := by
  unfold actualPrimeBoxTestSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [actual_source_test_eq_sum_atoms e chi m omega J5 j hj rows licensed,
    Finset.mul_sum]

/-- The actual original nonconstant OLD4 own-cube prime test has a true
positive-cell limit. Every refined integral uses the correct selected raw
Q3 seed and all producer rows eligible on its exact face-owning atom. -/
theorem tendsto_actualOld4_positiveCell_refinedIntegral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
        (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
        ((P1OriginalFifthLimit.sourceRegion e chi m omega j).indicator
          (actualOldTest e chi omega m j rows licensed))) atTop
      (𝓝 (∑ s : Pattern rows,
        ∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j ∩ liftedAtom rows s,
          fixedOldTest (e : ℝ) (selectedSeed e m j) rows licensed s t * ∏ i, 1 / t i)) := by
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Pattern rows)) (fun s _ =>
    tendsto_original_source_liftedAtom_test e chi m omega a ha haRho J5 j hj rows s _
      (continuousOn_fixedOldTest (e : ℝ) (selectedSeed e m j) a (19 / 96) ha rows licensed s))
  apply hlim.congr'
  exact Eventually.of_forall (fun N =>
    (actual_prime_test_eq_sum_atoms e chi m omega a (19 / 96) J5 j hj rows licensed N).symm)

/-- Every atom's weighted continuous extension is genuinely integrable on
the original truncated cell. No integrability of the discontinuous global
producer profile is postulated. -/
theorem integrableOn_fixedOldTest_weight
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (j : Label5 m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (s : Pattern rows) :
    IntegrableOn (fun t => fixedOldTest (e : ℝ) (selectedSeed e m j) rows licensed s t *
        ∏ i, 1 / t i) (P1OriginalFifthIntegral.truncatedCell e chi m omega a j) := by
  have hc := (continuousOn_fixedOldTest (e : ℝ) (selectedSeed e m j) a (19 / 96)
      ha rows licensed s).mul (P1OriginalFifthIntegral.continuousOn_reciprocalWeight ha)
  have hi := hc.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))
  exact hi.mono_set (P1OriginalFifthIntegral.truncatedCell_subset_closedBox e chi m omega a j)

/-- Exact integral gluing of the face-owning finite refinement. The RHS
is the literal actual producer old profile on the original truncated cell. -/
theorem actualOld4_integral_eq_sum_atoms
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    (∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
      actualOldTest e chi omega m j rows licensed t * ∏ i, 1 / t i) =
      ∑ s : Pattern rows,
        ∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j ∩ liftedAtom rows s,
          fixedOldTest (e : ℝ) (selectedSeed e m j) rows licensed s t * ∏ i, 1 / t i := by
  have hint (s : Pattern rows) : IntegrableOn
      ((liftedAtom rows s).indicator (fun t =>
        fixedOldTest (e : ℝ) (selectedSeed e m j) rows licensed s t * ∏ i, 1 / t i))
      (P1OriginalFifthIntegral.truncatedCell e chi m omega a j) :=
    (integrableOn_fixedOldTest_weight e chi m omega a ha j rows licensed s).indicator
      (measurableSet_liftedAtom rows s)
  calc
    _ = ∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
        ∑ s : Pattern rows, (liftedAtom rows s).indicator (fun t =>
          fixedOldTest (e : ℝ) (selectedSeed e m j) rows licensed s t * ∏ i, 1 / t i) t := by
      apply setIntegral_congr_fun (P1OriginalFifthIntegral.truncatedCell_measurable e chi m omega a j)
      intro t ht
      have hs : t ∈ P1OriginalFifthLimit.sourceRegion e chi m omega j := ht.2
      have h := actual_source_test_eq_sum_atoms e chi m omega J5 j hj rows licensed t
      simp only [indicator_of_mem hs] at h
      rw [h, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      by_cases ha : t ∈ liftedAtom rows s
      · simp only [indicator_of_mem ⟨hs, ha⟩, indicator_of_mem ha]
      · simp only [indicator_of_not_mem ha, indicator_of_not_mem
          (show t ∉ P1OriginalFifthLimit.sourceRegion e chi m omega j ∩ liftedAtom rows s
            from fun hh => ha hh.2), zero_mul]
    _ = ∑ s : Pattern rows, ∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
        (liftedAtom rows s).indicator (fun t =>
          fixedOldTest (e : ℝ) (selectedSeed e m j) rows licensed s t * ∏ i, 1 / t i) t :=
      integral_finsetSum _ (fun s _ => hint s)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [setIntegral_indicator (measurableSet_liftedAtom rows s)]

/-- True actual nonconstant OLD4 prime-test limit, now in one genuine
original-cell integral. No fixed-row-set hypothesis remains. -/
theorem tendsto_actualOld4_positiveCell_integral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
        (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
        ((P1OriginalFifthLimit.sourceRegion e chi m omega j).indicator
          (actualOldTest e chi omega m j rows licensed))) atTop
      (𝓝 (∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
        actualOldTest e chi omega m j rows licensed t * ∏ i, 1 / t i)) := by
  rw [actualOld4_integral_eq_sum_atoms e chi m omega a ha J5 j hj rows licensed]
  exact tendsto_actualOld4_positiveCell_refinedIntegral
    e chi m omega a ha haRho J5 j hj rows licensed

theorem integrableOn_actualOld4_weight
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    IntegrableOn (fun t => actualOldTest e chi omega m j rows licensed t * ∏ i, 1 / t i)
      (P1OriginalFifthIntegral.truncatedCell e chi m omega a j) := by
  have hint (s : Pattern rows) : IntegrableOn
      ((liftedAtom rows s).indicator (fun t =>
        fixedOldTest (e : ℝ) (selectedSeed e m j) rows licensed s t * ∏ i, 1 / t i))
      (P1OriginalFifthIntegral.truncatedCell e chi m omega a j) :=
    (integrableOn_fixedOldTest_weight e chi m omega a ha j rows licensed s).indicator
      (measurableSet_liftedAtom rows s)
  apply (integrable_finsetSum (Finset.univ : Finset (Pattern rows)) (fun s _ => hint s)).congr_fun
    ?_ (P1OriginalFifthIntegral.truncatedCell_measurable e chi m omega a j)
  intro t ht
  have hs : t ∈ P1OriginalFifthLimit.sourceRegion e chi m omega j := ht.2
  have h := actual_source_test_eq_sum_atoms e chi m omega J5 j hj rows licensed t
  simp only [indicator_of_mem hs] at h
  rw [h, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  by_cases ha : t ∈ liftedAtom rows s
  · simp only [indicator_of_mem ⟨hs, ha⟩, indicator_of_mem ha]
  · simp only [indicator_of_not_mem ha, indicator_of_not_mem
      (show t ∉ P1OriginalFifthLimit.sourceRegion e chi m omega j ∩ liftedAtom rows s
        from fun hh => ha hh.2), zero_mul]

/-- Original selected ownership, not a generic-D base identification,
closes the corrected stored NEW minus actual variable OLD prime-test limit. -/
theorem tendsto_corrected_positiveCell_gatedTest
    (D : HistoricalPrefixCapData) (e : ℚ) (chi omega a : ℝ)
    (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J5 : Finset (Label5 D.m)) (j : Label5 D.m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi D.m omega J5)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
        (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
        (fun t => if t ∈ P1CorrectedFifthCellArithmeticError.originalCellRegion e chi D.m omega j
          then P1CorrectedFifthCellArithmeticError.gatedProfileDifference
            D e chi omega j rows licensed t else 0)) atTop
      (𝓝 (correctedSelectedStoredIntegral D e chi omega a j rows licensed)) := by
  have hnew := P1OriginalFifthLimit.tendsto_test_original_sourceRegion
    e chi D.m omega a ha haRho J5 j hj (primeOwnCubeGatedProfile (D.cap5 j : ℝ))
    (P1OriginalFifthIntegral.continuousOn_gatedProfile ha (D.cap5 j : ℝ))
  have hold := tendsto_actualOld4_positiveCell_integral
    e chi D.m omega a ha haRho J5 j hj rows licensed
  have hintNew : IntegrableOn (fun t : Point5 =>
      primeOwnCubeGatedProfile (D.cap5 j : ℝ) t * ∏ i, 1 / t i)
      (P1OriginalFifthIntegral.truncatedCell e chi D.m omega a j) := by
    have hc := (P1OriginalFifthIntegral.continuousOn_gatedProfile ha (D.cap5 j : ℝ)).mul
      (P1OriginalFifthIntegral.continuousOn_reciprocalWeight ha)
    exact (hc.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set
      (P1OriginalFifthIntegral.truncatedCell_subset_closedBox e chi D.m omega a j)
  have hintOld := integrableOn_actualOld4_weight e chi D.m omega a ha J5 j hj rows licensed
  have hIntegral : correctedSelectedStoredIntegral D e chi omega a j rows licensed =
      (∫ t in P1OriginalFifthIntegral.truncatedCell e chi D.m omega a j,
        primeOwnCubeGatedProfile (D.cap5 j : ℝ) t * ∏ i, 1 / t i) -
      ∫ t in P1OriginalFifthIntegral.truncatedCell e chi D.m omega a j,
        actualOldTest e chi omega D.m j rows licensed t * ∏ i, 1 / t i := by
    change (∫ t in P1OriginalFifthIntegral.truncatedCell e chi D.m omega a j,
      (primeOwnCubeGatedProfile (D.cap5 j : ℝ) t -
        actualOldTest e chi omega D.m j rows licensed t) * ∏ i, 1 / t i) = _
    simp_rw [sub_mul]
    exact integral_sub hintNew hintOld
  rw [hIntegral]
  apply (hnew.sub hold).congr'
  apply Eventually.of_forall
  intro N
  symm
  exact P1CorrectedFifthCellArithmeticError.actualPrimeBoxTestSum_region_sub N
    (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
    (P1CorrectedFifthCellArithmeticError.originalCellRegion e chi D.m omega j)
    (primeOwnCubeGatedProfile (D.cap5 j : ℝ))
    (actualOldTest e chi omega D.m j rows licensed)

/-- A genuine positive-cell limit for the normalized finite corrected
charge on the ORIGINAL T3 carrier. Its old profile is the actual variable
producer, and its new profile is the literal selected stored cap. -/
theorem tendsto_corrected_positiveCell_actualCharge
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => P1CorrectedFifthCausalTupleDictionary.correctedCellPrimeCorrection
        D J e chi omega rows licensed a N (cap N) j)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (correctedSelectedStoredIntegral D e chi omega a j rows licensed)) := by
  have hselected : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells
      e chi D.m omega (D.cells5 ∩ J) :=
    (P1OriginalCoarseFifthContinuation.mem_selectedFifthCells
      e chi D.m omega (D.cells5 ∩ J) j).mpr
        ⟨hj, (howned.2.2 j hj).1, (howned.2.2 j hj).2⟩
  have htest := (tendsto_corrected_positiveCell_gatedTest D e chi omega a ha haRho
    (D.cells5 ∩ J) j hselected rows licensed).mono_left
      (show (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) ≤ atTop from inf_le_left)
  have herror := P1CorrectedFifthCellArithmeticError.tendsto_correctedCellPrimeCorrection_sub_gatedTest
    D J e chi omega a ha haRho rows licensed j hj cap hcap
  simpa only [sub_add_cancel, zero_add] using herror.add htest

/-- The entire fixed selected stored table has the sum of its genuine
corrected actual-parent integrals as its positive-cut limit. -/
theorem tendsto_corrected_selected_positive_actualCharge
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => ∑ j ∈ D.cells5 ∩ J,
        P1CorrectedFifthCausalTupleDictionary.correctedCellPrimeCorrection
          D J e chi omega rows licensed a N (cap N) j)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (∑ j ∈ D.cells5 ∩ J,
        correctedSelectedStoredIntegral D e chi omega a j rows licensed)) := by
  exact tendsto_finsetSum _ (fun j hj => tendsto_corrected_positiveCell_actualCharge
    D J e chi omega a ha haRho rows licensed j hj howned cap hcap)

end
end ImbalancedChen.P1ActualVariableFourthFifthCellTestLimit
