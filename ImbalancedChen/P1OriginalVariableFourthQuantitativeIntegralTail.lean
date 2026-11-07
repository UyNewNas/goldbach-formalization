import ImbalancedChen.P1OriginalVariableFourthFullActiveIntegral
import ImbalancedChen.P1OriginalVariableFourthFullActivePositiveLimit

/-!
Quantitative omitted continuous mass for the original full active VARIABLE
fourth source. SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

The original arithmetic cutoff-increment bound and the genuinely proved
full-integral identification imply a linear bound for omitted fixed-cap
integrals. Nonnegative actual variable kernels are dominated on measurable
subsets by the constant-initial original kernel at omega/2. The resulting
constant precedes every row family, licensing predicate and small cutoff.
No desired continuous error or global mean is assumed as a premise.
-/

namespace ImbalancedChen.P1OriginalVariableFourthQuantitativeIntegralTail
noncomputable section
open scoped Classical BigOperators
open Set Filter Topology MeasureTheory
open P1OriginalCoarseContinuation P1OriginalFourthIntegral
open P1OriginalFourthCutoffOrder P1OriginalFourthZeroCutoffLimit
open P1OriginalFourthUntruncatedIntegral
open P1OriginalVariableFourthUntruncatedDomination
open P1OriginalVariableFourthFullActiveIntegral
open P1OriginalVariableFourthFullSourceActivation
open P1OriginalVariableFourthActiveOnly
open P1OriginalVariableFourthActiveMeshCover
open P1OriginalVariableFourthFullActivePositiveLimit
open P2OriginalFourthCapProducerInterface

def originalCellTail (e : ℚ) (m : ℕ) (omega a : ℝ)
    (cap4 : FourthCell m → ℚ) (j : FourthCell m) : ℝ :=
  ∫ t in fullCell e m omega j \ truncatedCell e m omega a j, rawKernel e m cap4 j t

theorem originalCellTail_nonneg
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4) :
    0 ≤ originalCellTail e m omega a cap4 j := by
  apply setIntegral_nonneg ((fullCell_measurable e m omega j).diff
    (truncatedCell_measurable e m omega a j))
  intro t ht
  rw [rawKernel_eq_extended_on_fullCell e chi m omega J4 cap4 hcheck j hj ht.1]
  exact extendedKernel_nonneg_on_fullCell e chi m omega J4 cap4 hcheck j hj ht.1

theorem originalCellTail_eq_difference
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    {a : ℝ} (ha : 0 < a) (J4 : Finset (FourthCell m))
    (cap4 : FourthCell m → ℚ) (hcheck : h34Check e chi m omega J4 cap4 = true)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4) :
    originalCellTail e m omega a cap4 j =
      fullCellIntegral e m omega cap4 j - cellIntegral e m omega a cap4 j := by
  unfold originalCellTail fullCellIntegral
  rw [setIntegral_sdiff (truncatedCell_measurable e m omega a j)
    (integrableOn_original_rawKernel_fullCell e chi m omega homega homegaRho J4 cap4 hcheck j hj)
      (truncatedCell_subset_fullCell e m omega ha j),
    cellIntegral_eq_raw e chi m omega ha J4 cap4 hcheck j hj]

theorem originalTailSum_eq_difference
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    {a : ℝ} (ha : 0 < a) (J4 : Finset (FourthCell m))
    (cap4 : FourthCell m → ℚ) (hcheck : h34Check e chi m omega J4 cap4 = true) :
    (∑ j ∈ selectedFourthCells e chi m omega J4, originalCellTail e m omega a cap4 j) =
      fullSelectedIntegral e chi m omega J4 cap4 - selectedIntegral e chi m omega a J4 cap4 := by
  unfold fullSelectedIntegral selectedIntegral
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j hj =>
    originalCellTail_eq_difference e chi m omega homega homegaRho ha J4 cap4 hcheck j hj)

/-- The linear continuous tail is derived from the actual arithmetic
remainder-increment theorem and the constructed full Lebesgue limit. -/
theorem exists_original_tailSum_le_linear
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    ∃ D : ℝ, 0 < D ∧ ∀ a : ℝ, 0 < a → 2 * a ≤ omega →
      (∑ j ∈ selectedFourthCells e chi m omega J4,
        originalCellTail e m omega a cap4 j) ≤ D * a := by
  obtain ⟨D, hD, hdiff⟩ := exists_original_cutoff_difference_le
    e chi m omega homega homegaRho J4 cap4 hcheck
  have hI := tendsto_selectedIntegral_fullSelectedIntegral
    e chi m omega homega homegaRho J4 cap4 hcheck
  refine ⟨D, hD, ?_⟩
  intro a ha haomega
  have hb0 : Tendsto (fun b : ℝ => b) (𝓝[Ioi 0] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun b : ℝ => D * (a + b)) (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (D * a)) := by
    simpa only [add_zero] using (hb0.const_add a).const_mul D
  have hbound : ∀ᶠ b : ℝ in 𝓝[Ioi 0] (0 : ℝ),
      |selectedIntegral e chi m omega a J4 cap4 - selectedIntegral e chi m omega b J4 cap4| ≤
        D * (a + b) := by
    filter_upwards [self_mem_nhdsWithin,
      (Iio_mem_nhds (half_pos homega)).filter_mono nhdsWithin_le_nhds] with b hb hbsmall
    exact hdiff a b ha haomega hb (by linarith)
  have hleft' : Tendsto (fun b : ℝ =>
      |selectedIntegral e chi m omega a J4 cap4 - selectedIntegral e chi m omega b J4 cap4|)
      (𝓝[Ioi 0] (0 : ℝ))
      (𝓝 |selectedIntegral e chi m omega a J4 cap4 - fullSelectedIntegral e chi m omega J4 cap4|) :=
    (tendsto_const_nhds.sub hI).abs
  have habs := le_of_tendsto_of_tendsto hleft' hright hbound
  rw [originalTailSum_eq_difference e chi m omega homega homegaRho ha J4 cap4 hcheck]
  exact (le_abs_self _).trans (by simpa only [abs_sub_comm] using habs)

private theorem active_omitted_subset_original_omitted
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (homega : 0 ≤ omega)
    (label : Label m) (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m) :
    positiveActiveCell e chi m omega label \ cutoffActiveCell e chi m omega a label ⊆
      fullCell e m (omega / 2) label.1 \ truncatedCell e m (omega / 2) a label.1 := by
  intro t ht
  refine ⟨positiveActiveCell_subset_half_fullCell e chi m omega homega label hl ht.1, ?_⟩
  intro htr
  exact ht.2 ⟨htr.1, ht.1.2⟩

/-- A measurable omitted active-branch integral is dominated by the SAME
original fixed-initial omitted cell integral at omega/2. -/
theorem active_branch_tail_le_original_cellTail
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2)
    {a : ℝ} (ha : 0 < a) (label : Label m)
    (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m)
    (hs : label.1 ∈ selectedFourthCells e chi m (omega / 2) Finset.univ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    0 ≤ fullActiveBranchIntegral e chi m omega label rows licensed -
        activeCutoffIntegral e chi m omega a label rows licensed ∧
      fullActiveBranchIntegral e chi m omega label rows licensed -
        activeCutoffIntegral e chi m omega a label rows licensed ≤
      originalCellTail e m (omega / 2) a (initialCap e m) label.1 := by
  let A := positiveActiveCell e chi m omega label \ cutoffActiveCell e chi m omega a label
  let T := fullCell e m (omega / 2) label.1 \ truncatedCell e m (omega / 2) a label.1
  have hA : MeasurableSet A := (positiveActiveCell_measurable e chi m omega label).diff
    (cutoffActiveCell_measurable e chi m omega a label)
  have hT : MeasurableSet T := (fullCell_measurable e m (omega / 2) label.1).diff
    (truncatedCell_measurable e m (omega / 2) a label.1)
  have hsub : A ⊆ T := active_omitted_subset_original_omitted e chi m omega a homega.le label hl
  have hv := integrableOn_branchRawKernel_full_active
    e he chi m omega homega homegaRho hmesh label hl rows licensed
  have hm := integrableOn_original_rawKernel_fullCell e chi m (omega / 2)
    (by positivity) (by linarith) Finset.univ (initialCap e m)
      (initialCap_h34Check e he chi m (omega / 2) Finset.univ) label.1 hs
  have heq : (∫ t in A, branchRawKernel e chi m label rows licensed t) =
      fullActiveBranchIntegral e chi m omega label rows licensed -
        activeCutoffIntegral e chi m omega a label rows licensed :=
    setIntegral_sdiff (cutoffActiveCell_measurable e chi m omega a label) hv
      (cutoffActiveCell_subset_positive e chi m omega ha label)
  rw [← heq]
  constructor
  · exact setIntegral_nonneg hA (fun t ht =>
      (branchRawKernel_nonneg_le_initial_majorant
        e he chi m omega homega.le hmesh label hl rows licensed ht.1).1)
  · have hvA := hv.mono_set (show A ⊆ positiveActiveCell e chi m omega label from sdiff_subset)
    have hmT := hm.mono_set (show T ⊆ fullCell e m (omega / 2) label.1 from sdiff_subset)
    have hmA := hmT.mono_set hsub
    have hfirst := setIntegral_mono_on hvA hmA hA (fun t ht =>
      (branchRawKernel_nonneg_le_initial_majorant
        e he chi m omega homega.le hmesh label hl rows licensed ht.1).2)
    apply hfirst.trans
    apply setIntegral_mono_set hmT
    · filter_upwards [ae_restrict_mem hT] with t ht
      rw [rawKernel_eq_extended_on_fullCell e chi m (omega / 2) Finset.univ (initialCap e m)
        (initialCap_h34Check e he chi m (omega / 2) Finset.univ) label.1 hs ht.1]
      exact extendedKernel_nonneg_on_fullCell e chi m (omega / 2) Finset.univ (initialCap e m)
        (initialCap_h34Check e he chi m (omega / 2) Finset.univ) label.1 hs ht.1
    · exact Eventually.of_forall hsub

/-- One constant controls every active label and every actual producer row
family/licence predicate. The cutoff condition is a<=omega/4. -/
theorem exists_active_branch_integral_tail_le_linear
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ rows : Finset ProducerRow, ∀ licensed : ProducerRow → Prop,
      ∀ a : ℝ, 0 < a → 4 * a ≤ omega → ∀ label ∈ activeAdoptedLabels (e : ℝ) chi m,
        0 ≤ fullActiveBranchIntegral e chi m omega label rows licensed -
          refinedBranchIntegral (e : ℝ) chi m omega a rows licensed label ∧
        fullActiveBranchIntegral e chi m omega label rows licensed -
          refinedBranchIntegral (e : ℝ) chi m omega a rows licensed label ≤ D * a := by
  obtain ⟨D, hD, htail⟩ := exists_original_tailSum_le_linear e chi m (omega / 2)
    (by positivity) (by linarith) Finset.univ (initialCap e m)
      (initialCap_h34Check e he chi m (omega / 2) Finset.univ)
  refine ⟨D, hD, ?_⟩
  intro rows licensed a ha haomega label hl
  have heq : refinedBranchIntegral (e : ℝ) chi m omega a rows licensed label =
      activeCutoffIntegral e chi m omega a label rows licensed :=
    active_refined_integral_eq_raw e chi m omega homega.le ha label hl rows licensed
  rw [heq]
  by_cases hne : (positiveActiveCell e chi m omega label).Nonempty
  · obtain ⟨t, ht⟩ := hne
    have hs := active_source_label_selected_half e chi m omega hmesh label hl ht.2
    have hb := active_branch_tail_le_original_cellTail
      e he chi m omega homega homegaRho hmesh ha label hl hs rows licensed
    refine ⟨hb.1, (hb.2.trans ?_).trans (htail a ha (by linarith))⟩
    exact Finset.single_le_sum (fun j hj => originalCellTail_nonneg e chi m (omega / 2) a
      Finset.univ (initialCap e m) (initialCap_h34Check e he chi m (omega / 2) Finset.univ) j hj) hs
  · have hempty : positiveActiveCell e chi m omega label = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hcut : cutoffActiveCell e chi m omega a label = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro t ht
      have h := cutoffActiveCell_subset_positive e chi m omega ha label ht
      simpa only [hempty, mem_empty_iff_false] using h
    simp only [fullActiveBranchIntegral, activeCutoffIntegral, hempty, hcut, integral_empty,
      sub_self, le_refl, true_and]
    positivity

/-- Quantitative full active error, with its constant chosen before all
producer data. This is a true continuous source estimate, not a premise. -/
theorem exists_fullActiveIntegral_tail_le_linear
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ rows : Finset ProducerRow, ∀ licensed : ProducerRow → Prop,
      ∀ a : ℝ, 0 < a → 4 * a ≤ omega →
        0 ≤ fullActiveIntegral e chi m omega rows licensed -
          ∑ label ∈ activeAdoptedLabels (e : ℝ) chi m,
            refinedBranchIntegral (e : ℝ) chi m omega a rows licensed label ∧
        fullActiveIntegral e chi m omega rows licensed -
          ∑ label ∈ activeAdoptedLabels (e : ℝ) chi m,
            refinedBranchIntegral (e : ℝ) chi m omega a rows licensed label ≤ D * a := by
  obtain ⟨D, hD, hb⟩ := exists_active_branch_integral_tail_le_linear
    e he chi m omega homega homegaRho hmesh
  let q : ℝ := (activeAdoptedLabels (e : ℝ) chi m).card
  refine ⟨(q + 1) * D, by dsimp [q]; positivity, ?_⟩
  intro rows licensed a ha haomega
  unfold fullActiveIntegral
  rw [← Finset.sum_sub_distrib]
  refine ⟨Finset.sum_nonneg (fun label hl => (hb rows licensed a ha haomega label hl).1), ?_⟩
  calc
    _ ≤ ∑ _label ∈ activeAdoptedLabels (e : ℝ) chi m, D * a :=
      Finset.sum_le_sum (fun label hl => (hb rows licensed a ha haomega label hl).2)
    _ = q * (D * a) := by simp only [Finset.sum_const, nsmul_eq_mul, q]
    _ ≤ ((q + 1) * D) * a := by
      have hpos : 0 ≤ D * a := by positivity
      nlinarith

end
end ImbalancedChen.P1OriginalVariableFourthQuantitativeIntegralTail
