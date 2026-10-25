import ImbalancedChen.P1OriginalVariableFourthUntruncatedDomination
import ImbalancedChen.P1OriginalVariableFourthActiveMeshCover

/-!
# Full active original fourth branches, including rough-cutoff crossings

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

The branch's actual third coordinate, rather than its whole mesh box,
decides activation. Under the explicit mesh-width condition an active
adopted branch embeds into the original selected cell at omega/2 with the
SAME Gamma and firstStop. The preceding genuine integrable majorant then
applies. The width condition is retained; no assertion covers coarse meshes
for which it fails. Empty branches are handled without a witness premise.
-/

namespace ImbalancedChen.P1OriginalVariableFourthFullActiveIntegral
noncomputable section
open scoped Classical BigOperators
open Set MeasureTheory Filter Topology
open P1OriginalCoarseContinuation P1OriginalFourthIntegral
open P1FourthFullCellIntegral
open P1OriginalFourthUntruncatedIntegral
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthProfileRegularity
open P1OriginalVariableFourthCellTestLimit
open P1OriginalVariableFourthEligibilityPartition
open P1OriginalVariableFourthUntruncatedDomination
open P1OriginalVariableFourthFullSourceActivation
open P1OriginalVariableFourthActiveOnly
open P1OriginalVariableFourthActiveMeshCover
open P2OriginalFourthCapProducerInterface

def positiveActiveCell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (label : Label m) : Set Point :=
  {t | ∀ i, 0 < t i} ∩ sourceBranch (e : ℝ) chi m omega label

def cutoffActiveCell (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (label : Label m) : Set Point :=
  logPrimeBox (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)) ∩
    sourceBranch (e : ℝ) chi m omega label

def branchRawKernel (e : ℚ) (chi : ℝ) (m : ℕ) (label : Label m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (t : Point) : ℝ :=
  (fourthPlusProfileP1 (branchSeed (e : ℝ) chi m label) t -
    fourthPlusProfileP1
      (producerProfile4 (e : ℝ) rows licensed (branchSeed (e : ℝ) chi m label) t) t) *
        ∏ i, 1 / t i

theorem branchSeed_eq_oldExponent (e : ℚ) (chi : ℝ) (m : ℕ) (label : Label m)
    (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m) :
    branchSeed (e : ℝ) chi m label = oldExponent e m label.1 := by
  have h := (mem_activeAdoptedLabels (e : ℝ) chi m label).mp hl
  rw [branchSeed, if_pos h, oldExponent_eq_actual]

theorem branchRawKernel_eq_variableRawKernel
    (e : ℚ) (chi : ℝ) (m : ℕ) (label : Label m)
    (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (t : Point) :
    branchRawKernel e chi m label rows licensed t =
      variableRawKernel e m label.1 rows licensed t := by
  simp only [branchRawKernel, variableRawKernel, branchSeed_eq_oldExponent e chi m label hl]

theorem positiveActiveCell_measurable (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (label : Label m) : MeasurableSet (positiveActiveCell e chi m omega label) := by
  have hp : MeasurableSet {t : Point | ∀ i, 0 < t i} := by
    have heq : {t : Point | ∀ i, 0 < t i} = ⋂ i : Fin 4, {t : Point | 0 < t i} := by
      ext t
      simp only [mem_iInter, mem_setOf_eq]
    rw [heq]
    exact MeasurableSet.iInter (fun i => measurableSet_lt measurable_const (measurable_pi_apply i))
  exact hp.inter (measurableSet_sourceBranch (e : ℝ) chi m omega label)

theorem cutoffActiveCell_measurable (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (label : Label m) : MeasurableSet (cutoffActiveCell e chi m omega a label) :=
  (measurableSet_logPrimeBox _ _).inter (measurableSet_sourceBranch (e : ℝ) chi m omega label)

theorem positiveActiveCell_subset_half_fullCell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (homega : 0 ≤ omega)
    (label : Label m) (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m) :
    positiveActiveCell e chi m omega label ⊆ fullCell e m (omega / 2) label.1 := by
  intro t ht
  have hbox := logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) < 19 / 96)
    m label.1 ht.2.1.1
  exact ⟨ht.1, hbox,
    active_source_branch_subset_half_sourceRegion e chi m omega homega label hl ht.2⟩

/-- The raw active branch has the original constant-initial majorant at
omega/2, even when its box crosses the literal activation cutoff omega. -/
theorem branchRawKernel_nonneg_le_initial_majorant
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ) (homega : 0 ≤ omega)
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2)
    (label : Label m) (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    {t : Point} (ht : t ∈ positiveActiveCell e chi m omega label) :
    0 ≤ branchRawKernel e chi m label rows licensed t ∧
      branchRawKernel e chi m label rows licensed t ≤
        rawKernel e m (initialCap e m) label.1 t := by
  have hs := active_source_label_selected_half e chi m omega hmesh label hl ht.2
  have ht' := positiveActiveCell_subset_half_fullCell e chi m omega homega label hl ht
  rw [branchRawKernel_eq_variableRawKernel e chi m label hl rows licensed t]
  exact variableRawKernel_nonneg_le_majorant e he chi m (omega / 2) Finset.univ label.1 hs
    rows licensed ht'

/-- Integrability of every full active adopted branch. No assumption that
its original mesh lower endpoint is above omega appears. -/
theorem integrableOn_branchRawKernel_full_active
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2)
    (label : Label m) (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    IntegrableOn (branchRawKernel e chi m label rows licensed)
      (positiveActiveCell e chi m omega label) := by
  by_cases hne : (positiveActiveCell e chi m omega label).Nonempty
  · obtain ⟨t, ht⟩ := hne
    have hs := active_source_label_selected_half e chi m omega hmesh label hl ht.2
    have hi := (integrableOn_variableRawKernel_full e he chi m (omega / 2)
      (by positivity) (by linarith) Finset.univ label.1 hs rows licensed).mono_set
        (positiveActiveCell_subset_half_fullCell e chi m omega homega.le label hl)
    exact hi.congr_fun (fun t _ =>
      (branchRawKernel_eq_variableRawKernel e chi m label hl rows licensed t).symm)
        (positiveActiveCell_measurable e chi m omega label)
  · have hempty : positiveActiveCell e chi m omega label = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    exact integrableOn_empty

theorem cutoffActiveCell_subset_positive (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (label : Label m) :
    cutoffActiveCell e chi m omega a label ⊆ positiveActiveCell e chi m omega label := by
  intro t ht
  exact ⟨fun i => ha.trans_le (mem_logPrimeBox.mp ht.1 i).1, ht.2⟩

theorem cutoffActiveCell_right_aecover (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (label : Label m) :
    AECover (volume.restrict (positiveActiveCell e chi m omega label))
      (𝓝[Ioi 0] (0 : ℝ)) (fun a : ℝ => cutoffActiveCell e chi m omega a label) where
  measurableSet a := cutoffActiveCell_measurable e chi m omega a label
  ae_eventually_mem := by
    filter_upwards [ae_restrict_mem (positiveActiveCell_measurable e chi m omega label)] with t ht
    have hbox := logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) < 19 / 96)
      m label.1 ht.2.1.1
    have hc : ∀ᶠ a : ℝ in 𝓝[Ioi 0] (0 : ℝ), ∀ i : Fin 4, a < t i :=
      eventually_all.2 (fun i => (Iio_mem_nhds (ht.1 i)).filter_mono nhdsWithin_le_nhds)
    filter_upwards [hc] with a ha
    exact ⟨mem_logPrimeBox.mpr (fun i => ⟨(ha i).le, (mem_logPrimeBox.mp hbox i).2⟩), ht.2⟩

def fullActiveBranchIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (label : Label m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) : ℝ :=
  ∫ t in positiveActiveCell e chi m omega label, branchRawKernel e chi m label rows licensed t

def activeCutoffIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (label : Label m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) : ℝ :=
  ∫ t in cutoffActiveCell e chi m omega a label, branchRawKernel e chi m label rows licensed t

theorem tendsto_activeCutoffIntegral_full
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2)
    (label : Label m) (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    Tendsto (fun a : ℝ => activeCutoffIntegral e chi m omega a label rows licensed)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (fullActiveBranchIntegral e chi m omega label rows licensed)) := by
  have h := (cutoffActiveCell_right_aecover e chi m omega label).integral_tendsto_of_countably_generated
    (integrableOn_branchRawKernel_full_active
      e he chi m omega homega homegaRho hmesh label hl rows licensed)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  change (∫ t, branchRawKernel e chi m label rows licensed t
    ∂(volume.restrict (positiveActiveCell e chi m omega label)).restrict
      (cutoffActiveCell e chi m omega a label)) = _
  rw [Measure.restrict_restrict_of_subset
    (cutoffActiveCell_subset_positive e chi m omega ha label)]

private theorem integrable_branch_atom_test
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) {a : ℝ} (ha : 0 < a)
    (label : Label m) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (s : Pattern rows) :
    Integrable ((wallAtom rows s).indicator (fun t =>
      fixedCellTest (e : ℝ) rows (eligibleRows rows licensed s)
        (branchSeed (e : ℝ) chi m label) t * reciprocalWeight t))
      (volume.restrict (cutoffActiveCell e chi m omega a label)) := by
  have hc := (continuousOn_fixedCellTest (e : ℝ) rows (eligibleRows rows licensed s)
    (branchSeed (e : ℝ) chi m label) a (19 / 96) ha).mul (continuousOn_reciprocalWeight ha)
  have hi := (hc.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set
    (show cutoffActiveCell e chi m omega a label ⊆
      univ.pi (fun _ : Fin 4 => Icc a (19 / 96 : ℝ)) from by
        intro t ht i _
        exact ⟨(mem_logPrimeBox.mp ht.1 i).1, (mem_logPrimeBox.mp ht.1 i).2.le⟩)
  exact hi.indicator (measurableSet_wallAtom rows s)

/-- Exact attachment to the full active branch's finite refined prime-test
integral; this expression is the positive-limit worker's refinedBranchIntegral. -/
theorem active_refined_integral_eq_raw
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (homega : 0 ≤ omega)
    {a : ℝ} (ha : 0 < a)
    (label : Label m) (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    (∑ s : Pattern rows, ∫ t in
      logPrimeBox (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)) ∩
        (sourceBranch (e : ℝ) chi m omega label ∩ wallAtom rows s),
      fixedCellTest (e : ℝ) rows (eligibleRows rows licensed s)
        (branchSeed (e : ℝ) chi m label) t * ∏ i, 1 / t i) =
      activeCutoffIntegral e chi m omega a label rows licensed := by
  have hraw : ∀ t ∈ cutoffActiveCell e chi m omega a label,
      branchRawKernel e chi m label rows licensed t =
        variableExtendedKernel e m label.1 rows licensed t := by
    intro t ht
    rw [branchRawKernel_eq_variableRawKernel e chi m label hl rows licensed t]
    have hreg := active_source_branch_subset_half_sourceRegion e chi m omega
      homega label hl ht.2
    have htr : t ∈ truncatedCell e m (omega / 2) a label.1 := ⟨ht.1, hreg⟩
    exact variableRawKernel_eq_extended_on_truncated e m (omega / 2) ha label.1 rows licensed htr
  unfold activeCutoffIntegral
  rw [setIntegral_congr_fun (cutoffActiveCell_measurable e chi m omega a label) hraw]
  symm
  calc
    _ = ∫ t in cutoffActiveCell e chi m omega a label, ∑ s : Pattern rows,
        (wallAtom rows s).indicator (fun t => fixedCellTest (e : ℝ) rows
          (eligibleRows rows licensed s) (oldExponent e m label.1) t * reciprocalWeight t) t := by
      apply integral_congr_ae
      exact Eventually.of_forall (variableExtendedKernel_eq_sum_atoms e m label.1 rows licensed)
    _ = ∑ s : Pattern rows, ∫ t in cutoffActiveCell e chi m omega a label,
        (wallAtom rows s).indicator (fun t => fixedCellTest (e : ℝ) rows
          (eligibleRows rows licensed s) (oldExponent e m label.1) t * reciprocalWeight t) t := by
      apply integral_finsetSum Finset.univ
      intro s _
      simpa only [branchSeed_eq_oldExponent e chi m label hl] using
        integrable_branch_atom_test e chi m omega ha label rows licensed s
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [integral_indicator (measurableSet_wallAtom rows s)]
      rw [Measure.restrict_restrict (measurableSet_wallAtom rows s)]
      simp only [cutoffActiveCell, inter_comm (wallAtom rows s), inter_assoc,
        branchSeed_eq_oldExponent e chi m label hl, reciprocalWeight]

def fullActiveIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) : ℝ :=
  ∑ label ∈ activeAdoptedLabels (e : ℝ) chi m,
    fullActiveBranchIntegral e chi m omega label rows licensed

theorem tendsto_activeCutoffSum_fullActiveIntegral
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    Tendsto (fun a : ℝ => ∑ label ∈ activeAdoptedLabels (e : ℝ) chi m,
      activeCutoffIntegral e chi m omega a label rows licensed) (𝓝[Ioi 0] (0 : ℝ))
        (𝓝 (fullActiveIntegral e chi m omega rows licensed)) := by
  exact tendsto_finsetSum (activeAdoptedLabels (e : ℝ) chi m) (fun label hl =>
    tendsto_activeCutoffIntegral_full e he chi m omega homega homegaRho hmesh label hl rows licensed)

theorem tendsto_activeRefinedSum_fullActiveIntegral
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    Tendsto (fun a : ℝ => ∑ label ∈ activeAdoptedLabels (e : ℝ) chi m,
      ∑ s : Pattern rows, ∫ t in
        logPrimeBox (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)) ∩
          (sourceBranch (e : ℝ) chi m omega label ∩ wallAtom rows s),
        fixedCellTest (e : ℝ) rows (eligibleRows rows licensed s)
          (branchSeed (e : ℝ) chi m label) t * ∏ i, 1 / t i)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (fullActiveIntegral e chi m omega rows licensed)) := by
  apply (tendsto_activeCutoffSum_fullActiveIntegral
    e he chi m omega homega homegaRho hmesh rows licensed).congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  apply Finset.sum_congr rfl
  intro label hl
  exact (active_refined_integral_eq_raw e chi m omega homega.le ha label hl rows licensed).symm

end
end ImbalancedChen.P1OriginalVariableFourthFullActiveIntegral
