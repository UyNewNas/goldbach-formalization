import ImbalancedChen.P1OriginalFourthUntruncatedIntegral
import ImbalancedChen.P1OriginalVariableFourthBoundedSourceLimit
import ImbalancedChen.P1ActualCoarseLevelCeiling

/-!
# Integrable domination of the actual variable fourth producer

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

The rational global-initial cap is checked from the real original selected
Q3 ceiling. The all-eligible-row producer lies between its actual old seed
and that cap. Its raw saving is therefore nonnegative and dominated by the
already integrable original old-to-initial saving. Exact finite measurable
wall atoms construct measurability; no fixed-eligibility or global continuity
premise is used. No arithmetic tail theorem is asserted in this module.
-/

namespace ImbalancedChen.P1OriginalVariableFourthUntruncatedDomination
noncomputable section
open scoped Classical BigOperators
open Set MeasureTheory Filter Topology
open P1OriginalCoarseContinuation P1OriginalFourthIntegral
open P1FourthFullCellIntegral P1FourthIntegralSign
open P1OriginalFourthUntruncatedIntegral
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthProfileRegularity
open P1OriginalVariableFourthCellTestLimit
open P1OriginalVariableFourthEligibilityPartition
open P1OriginalVariableFourthBoundedSourceLimit
open P2OriginalFourthCapProducerInterface

def initialCap (e : ℚ) (m : ℕ) : FourthCell m → ℚ :=
  fun _ => 299 / 500 - 2 * e

theorem oldExponent_le_initialCap (e : ℚ) (he : 0 ≤ e)
    (chi : ℝ) (m : ℕ) (omega : ℝ) (J4 : Finset (FourthCell m))
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4) :
    oldExponent e m j ≤ (initialCap e m j : ℝ) := by
  have hcoarse := ((mem_selectedFourthCells e chi m omega J4 j).mp hj).2.1
  have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hc := (P1ActualCoarseLevelCeiling.selected_levelExponent_lt_initial
    (e : ℝ) chi heR m _ hcoarse).le
  rw [← oldExponent_eq_actual e m j, P1ThirdFallbackSupport.initial_uses_theta] at hc
  simpa only [initialCap, Rat.cast_sub, Rat.cast_div, Rat.cast_mul,
    Rat.cast_ofNat] using hc

/-- The original finite checker is derived, not supplied as a hypothesis. -/
theorem initialCap_h34Check (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J4 : Finset (FourthCell m)) :
    h34Check e chi m omega J4 (initialCap e m) = true := by
  simp only [h34Check, decide_eq_true_eq]
  intro j hj
  have h := oldExponent_le_initialCap e he chi m omega J4 j hj
  change (thirdCellExponent e m j : ℝ) ≤ (initialCap e m j : ℝ) at h
  exact_mod_cast h

/-- The actual producer's finite maximum retains every overlapping row,
its inherited raw-Q3 floor, and the true global initial ceiling. -/
theorem producerProfile_between_old_initial
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (t : Point) :
    oldExponent e m j ≤ producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) t ∧
      producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) t ≤
        (initialCap e m j : ℝ) := by
  have hp := producerProfile_mem_interval (e : ℝ) (oldExponent e m j) rows licensed t
  refine ⟨hp.1, hp.2.trans (max_le (oldExponent_le_initialCap e he chi m omega J4 j hj) ?_)⟩
  have hcap : VariableEnvelope.cap ≤ (299 / 500 : ℝ) := by norm_num [VariableEnvelope.cap]
  simpa only [initialCap, Rat.cast_sub, Rat.cast_div, Rat.cast_mul,
    Rat.cast_ofNat] using sub_le_sub_right hcap (2 * (e : ℝ))

def variableExtendedKernel (e : ℚ) (m : ℕ) (j : FourthCell m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (t : Point) : ℝ :=
  (extendedProfile (oldExponent e m j) t -
    extendedProfile (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) t) t) *
      reciprocalWeight t

def variableRawKernel (e : ℚ) (m : ℕ) (j : FourthCell m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (t : Point) : ℝ :=
  (fourthPlusProfileP1 (oldExponent e m j) t -
    fourthPlusProfileP1 (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) t) t) *
      ∏ i, 1 / t i

theorem variableExtendedKernel_nonneg_le_majorant
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    {t : Point} (ht : t ∈ fullCell e m omega j) :
    0 ≤ variableExtendedKernel e m j rows licensed t ∧
      variableExtendedKernel e m j rows licensed t ≤
        extendedKernel e m (initialCap e m) j t := by
  have hp := producerProfile_between_old_initial e he chi m omega J4 j hj rows licensed t
  have hlow := extendedProfile_antitone_level t (ht.1 _) hp.1
  have hhigh := extendedProfile_antitone_level t (ht.1 _) hp.2
  have hw : 0 ≤ reciprocalWeight t :=
    Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (ht.1 i).le)
  exact ⟨mul_nonneg (sub_nonneg.mpr hlow) hw,
    mul_le_mul_of_nonneg_right (sub_le_sub_left hhigh _) hw⟩

theorem variableRawKernel_eq_extended_on_truncated
    (e : ℚ) (m : ℕ) (omega : ℝ) {a : ℝ} (ha : 0 < a)
    (j : FourthCell m) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    {t : Point} (ht : t ∈ truncatedCell e m omega a j) :
    variableRawKernel e m j rows licensed t = variableExtendedKernel e m j rows licensed t := by
  unfold variableRawKernel variableExtendedKernel
  rw [rawProfile_eq_extended_on_truncated e m omega ha j le_rfl ht,
    rawProfile_eq_extended_on_truncated e m omega ha j
      (producerProfile4_seed_le (e : ℝ) rows licensed (oldExponent e m j) t) ht]

theorem variableRawKernel_eq_extended_on_full
    (e : ℚ) (m : ℕ) (omega : ℝ) (j : FourthCell m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    {t : Point} (ht : t ∈ fullCell e m omega j) :
    variableRawKernel e m j rows licensed t = variableExtendedKernel e m j rows licensed t := by
  obtain ⟨n, hn⟩ := (eventually_mem_truncatedCell e m omega j ht).exists
  exact variableRawKernel_eq_extended_on_truncated e m omega (cutoff_pos n) j rows licensed hn

theorem variableRawKernel_nonneg_le_majorant
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    {t : Point} (ht : t ∈ fullCell e m omega j) :
    0 ≤ variableRawKernel e m j rows licensed t ∧
      variableRawKernel e m j rows licensed t ≤ rawKernel e m (initialCap e m) j t := by
  rw [variableRawKernel_eq_extended_on_full e m omega j rows licensed ht,
    rawKernel_eq_extended_on_fullCell e chi m omega J4 (initialCap e m)
      (initialCap_h34Check e he chi m omega J4) j hj ht]
  exact variableExtendedKernel_nonneg_le_majorant e he chi m omega J4 j hj rows licensed ht

/-- Exact finite measurable atom expression for the actual weighted
producer test. Its eligibility is constructed; no hfixed is an input. -/
theorem variableExtendedKernel_eq_sum_atoms
    (e : ℚ) (m : ℕ) (j : FourthCell m) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (t : Point) :
    variableExtendedKernel e m j rows licensed t =
      ∑ s : Pattern rows, (wallAtom rows s).indicator
        (fun t => fixedCellTest (e : ℝ) rows (eligibleRows rows licensed s)
          (oldExponent e m j) t * reciprocalWeight t) t := by
  have h := source_test_eq_sum_atom_tests (e : ℝ) (oldExponent e m j) rows licensed univ t
  simp only [indicator_univ, univ_inter] at h
  unfold variableExtendedKernel
  rw [h, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : t ∈ wallAtom rows s
  · simp only [indicator_of_mem hs]
  · simp only [indicator_of_not_mem hs, zero_mul]

private theorem integrable_atom_test_on_truncated
    (e : ℚ) (m : ℕ) (omega : ℝ) {a : ℝ} (ha : 0 < a) (j : FourthCell m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (s : Pattern rows) :
    Integrable ((wallAtom rows s).indicator
      (fun t => fixedCellTest (e : ℝ) rows (eligibleRows rows licensed s)
        (oldExponent e m j) t * reciprocalWeight t))
      (volume.restrict (truncatedCell e m omega a j)) := by
  have hc := (continuousOn_fixedCellTest (e : ℝ) rows (eligibleRows rows licensed s)
    (oldExponent e m j) a (19 / 96) ha).mul (continuousOn_reciprocalWeight ha)
  have hi := (hc.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set
    (truncatedCell_subset_closedBox e m omega ha j)
  exact hi.indicator (measurableSet_wallAtom rows s)

theorem integrableOn_variableExtendedKernel_truncated
    (e : ℚ) (m : ℕ) (omega : ℝ) {a : ℝ} (ha : 0 < a) (j : FourthCell m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    IntegrableOn (variableExtendedKernel e m j rows licensed)
      (truncatedCell e m omega a j) := by
  have hi := integrable_finsetSum Finset.univ (fun s _ =>
    integrable_atom_test_on_truncated e m omega ha j rows licensed s)
  exact hi.congr (Eventually.of_forall (fun t =>
    (variableExtendedKernel_eq_sum_atoms e m j rows licensed t).symm))

/-- The finite wall partition constructs global a.e. strong measurability
on the original positive cell, without claiming continuity across faces. -/
theorem aestronglyMeasurable_variableExtendedKernel_full
    (e : ℚ) (m : ℕ) (omega : ℝ) (j : FourthCell m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    AEStronglyMeasurable (variableExtendedKernel e m j rows licensed)
      (volume.restrict (fullCell e m omega j)) := by
  apply (truncatedCell_aecover e m omega j).aestronglyMeasurable
  intro n
  rw [Measure.restrict_restrict_of_subset
    (truncatedCell_subset_fullCell e m omega (cutoff_pos n) j)]
  exact (integrableOn_variableExtendedKernel_truncated e m omega
    (cutoff_pos n) j rows licensed).aestronglyMeasurable

/-- Integrability of the ACTUAL variable producer kernel follows by
domination by the checked original constant-initial kernel. -/
theorem integrableOn_variableExtendedKernel_full
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    IntegrableOn (variableExtendedKernel e m j rows licensed) (fullCell e m omega j) := by
  have hmajor := integrableOn_original_extendedKernel_fullCell e chi m omega
    homega homegaRho J4 (initialCap e m) (initialCap_h34Check e he chi m omega J4) j hj
  apply hmajor.mono_nonneg
    (aestronglyMeasurable_variableExtendedKernel_full e m omega j rows licensed)
  · filter_upwards [ae_restrict_mem (fullCell_measurable e m omega j)] with t ht
    exact (variableExtendedKernel_nonneg_le_majorant e he chi m omega J4 j hj rows licensed ht).1
  · filter_upwards [ae_restrict_mem (fullCell_measurable e m omega j)] with t ht
    exact (variableExtendedKernel_nonneg_le_majorant e he chi m omega J4 j hj rows licensed ht).2

theorem integrableOn_variableRawKernel_full
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    IntegrableOn (variableRawKernel e m j rows licensed) (fullCell e m omega j) := by
  exact (integrableOn_variableExtendedKernel_full e he chi m omega
    homega homegaRho J4 j hj rows licensed).congr_fun
      (fun t ht => (variableRawKernel_eq_extended_on_full e m omega j rows licensed ht).symm)
        (fullCell_measurable e m omega j)

def variableFullCellIntegral (e : ℚ) (m : ℕ) (omega : ℝ) (j : FourthCell m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) : ℝ :=
  ∫ t in fullCell e m omega j, variableRawKernel e m j rows licensed t

/-- The whole positive-cutoff filter, not merely a chosen sequence,
exhausts the original full cell under its restricted volume measure. -/
theorem truncatedCell_right_aecover (e : ℚ) (m : ℕ) (omega : ℝ) (j : FourthCell m) :
    AECover (volume.restrict (fullCell e m omega j)) (𝓝[Ioi 0] (0 : ℝ))
      (fun a : ℝ => truncatedCell e m omega a j) where
  measurableSet a := truncatedCell_measurable e m omega a j
  ae_eventually_mem := by
    filter_upwards [ae_restrict_mem (fullCell_measurable e m omega j)] with t ht
    have hc : ∀ᶠ a : ℝ in 𝓝[Ioi 0] (0 : ℝ), ∀ i : Fin 4, a < t i :=
      eventually_all.2 (fun i => (Iio_mem_nhds (ht.1 i)).filter_mono nhdsWithin_le_nhds)
    filter_upwards [hc] with a ha
    exact ⟨mem_logPrimeBox.mpr (fun i =>
      ⟨(ha i).le, (mem_logPrimeBox.mp ht.2.1 i).2⟩), ht.2.2⟩

theorem tendsto_variableRaw_cutoff_fullIntegral
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    Tendsto (fun a : ℝ => ∫ t in truncatedCell e m omega a j,
      variableRawKernel e m j rows licensed t) (𝓝[Ioi 0] (0 : ℝ))
        (𝓝 (variableFullCellIntegral e m omega j rows licensed)) := by
  have h := (truncatedCell_right_aecover e m omega j).integral_tendsto_of_countably_generated
    (integrableOn_variableRawKernel_full e he chi m omega homega homegaRho J4 j hj rows licensed)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  change (∫ t, variableRawKernel e m j rows licensed t
    ∂(volume.restrict (fullCell e m omega j)).restrict (truncatedCell e m omega a j)) = _
  rw [Measure.restrict_restrict_of_subset (truncatedCell_subset_fullCell e m omega ha j)]

/-- The actual finite atom integral from the prime-test source is exactly
the same variable raw kernel on its original positive-cutoff cell. -/
theorem refinedCellIntegral_eq_rawIntegral
    (e : ℚ) (m : ℕ) (omega : ℝ) {a : ℝ} (ha : 0 < a) (j : FourthCell m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    refinedCellIntegral e m omega a j rows licensed =
      ∫ t in truncatedCell e m omega a j, variableRawKernel e m j rows licensed t := by
  have hraw : (∫ t in truncatedCell e m omega a j, variableRawKernel e m j rows licensed t) =
      ∫ t in truncatedCell e m omega a j, variableExtendedKernel e m j rows licensed t := by
    apply setIntegral_congr_fun (truncatedCell_measurable e m omega a j)
    intro t ht
    exact variableRawKernel_eq_extended_on_truncated e m omega ha j rows licensed ht
  rw [hraw]
  symm
  calc
    _ = ∫ t in truncatedCell e m omega a j, ∑ s : Pattern rows,
        (wallAtom rows s).indicator (fun t => fixedCellTest (e : ℝ) rows
          (eligibleRows rows licensed s) (oldExponent e m j) t * reciprocalWeight t) t := by
      apply integral_congr_ae
      exact Eventually.of_forall (variableExtendedKernel_eq_sum_atoms e m j rows licensed)
    _ = ∑ s : Pattern rows, ∫ t in truncatedCell e m omega a j,
        (wallAtom rows s).indicator (fun t => fixedCellTest (e : ℝ) rows
          (eligibleRows rows licensed s) (oldExponent e m j) t * reciprocalWeight t) t :=
      integral_finsetSum Finset.univ (fun s _ =>
        integrable_atom_test_on_truncated e m omega ha j rows licensed s)
    _ = refinedCellIntegral e m omega a j rows licensed := by
      apply Finset.sum_congr rfl
      intro s _
      rw [integral_indicator (measurableSet_wallAtom rows s)]
      change (∫ t, fixedCellTest (e : ℝ) rows (eligibleRows rows licensed s)
        (oldExponent e m j) t * reciprocalWeight t
          ∂(volume.restrict (truncatedCell e m omega a j)).restrict (wallAtom rows s)) = _
      rw [Measure.restrict_restrict (measurableSet_wallAtom rows s),
        inter_comm (wallAtom rows s) (truncatedCell e m omega a j)]

theorem tendsto_refinedCellIntegral_fullIntegral
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    Tendsto (fun a : ℝ => refinedCellIntegral e m omega a j rows licensed)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (variableFullCellIntegral e m omega j rows licensed)) := by
  apply (tendsto_variableRaw_cutoff_fullIntegral
    e he chi m omega homega homegaRho J4 j hj rows licensed).congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (refinedCellIntegral_eq_rawIntegral e m omega ha j rows licensed).symm

def variableFullSelectedIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) : ℝ :=
  ∑ j ∈ selectedFourthCells e chi m omega J4,
    variableFullCellIntegral e m omega j rows licensed

theorem tendsto_refinedSelectedIntegral_fullIntegral
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    Tendsto (fun a : ℝ => ∑ j ∈ selectedFourthCells e chi m omega J4,
      refinedCellIntegral e m omega a j rows licensed) (𝓝[Ioi 0] (0 : ℝ))
        (𝓝 (variableFullSelectedIntegral e chi m omega J4 rows licensed)) := by
  exact tendsto_finsetSum (selectedFourthCells e chi m omega J4) (fun j hj =>
    tendsto_refinedCellIntegral_fullIntegral
      e he chi m omega homega homegaRho J4 j hj rows licensed)

end
end ImbalancedChen.P1OriginalVariableFourthUntruncatedDomination
