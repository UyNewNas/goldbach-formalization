import ImbalancedChen.P1CorrectedFifthZeroCutoffLimit
import ImbalancedChen.P1OriginalRestoredSlabIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Actual corrected fifth untruncated original integral

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

The full positive original fifth cell keeps the actual firstStop/raw-Q3
candidate source. The old cap is the actual fourth all-row producer, the
new cap is the checked stored fifth cap, and both strict own-cube gates
remain. Bounded cutoff integrals are DERIVED from the genuine corrected
arithmetic zero-cutoff theorem. AECover then proves full integrability and
identifies the constructed value with this exact full Lebesgue integral.
No generic-D old5, coarse remainder, or literal-all15 profile is substituted.
-/

namespace ImbalancedChen.P1CorrectedFifthUntruncatedIntegral
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Filter Topology
open P2OriginalFourthCapProducerInterface
open P1CorrectedFifthDensityDictionary P1CorrectedFifthStoredH45Check
open P1CorrectedFifthGlobalSourceAssembly P1CorrectedFifthZeroCutoffLimit
open P1ActualVariableFourthFifthCellTestLimit P1OriginalRestoredSlabIntegral

def fullCorrectedCell (e : ℚ) (chi omega : ℝ) (m : ℕ) (j : Label5 m) : Set Point5 :=
  {t | ∀ i, 0 < t i} ∩
    (logPrimeBox (fun _ : Fin 5 => 0) (fun _ => (19 / 96 : ℝ)) ∩
      (logPrimeMeshCell 0 (19 / 96) m j ∩
        HistoricalThirdCoarse.P1OriginalCoarseFifth.jointRegion (e : ℝ) chi m omega j))

/-- Exact corrected old ACTUAL producer/new stored cap kernel, with its
separate strict own-cube gates already present in correctedCellKernel. -/
def fullKernel (D : HistoricalPrefixCapData) (e : ℚ) (chi omega : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (j : Label5 D.m) : Point5 → ℝ :=
  correctedCellKernel (originalVariableFourthProfile e chi omega D.m j rows licensed) (D.cap5 j : ℝ)

def fullCellIntegral (D : HistoricalPrefixCapData) (e : ℚ) (chi omega : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (j : Label5 D.m) : ℝ :=
  ∫ t in fullCorrectedCell e chi omega D.m j, fullKernel D e chi omega rows licensed j t

def fullSelectedIntegral (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega : ℝ) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) : ℝ :=
  ∑ j ∈ D.cells5 ∩ J, fullCellIntegral D e chi omega rows licensed j

def cutoff (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem cutoff_pos (n : ℕ) : 0 < cutoff n := by unfold cutoff; positivity

theorem cutoff_tendsto_zero : Tendsto cutoff atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem cutoff_tendsto_right : Tendsto cutoff atTop (𝓝[Ioi 0] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.2 ⟨cutoff_tendsto_zero, Eventually.of_forall cutoff_pos⟩

theorem fullCorrectedCell_measurable (e : ℚ) (chi omega : ℝ) (m : ℕ) (j : Label5 m) :
    MeasurableSet (fullCorrectedCell e chi omega m j) := by
  have hp : MeasurableSet {t : Point5 | ∀ i, 0 < t i} := by
    have heq : {t : Point5 | ∀ i, 0 < t i} = ⋂ i : Fin 5, {t : Point5 | 0 < t i} := by
      ext t
      simp only [mem_iInter, mem_setOf_eq]
    rw [heq]
    exact MeasurableSet.iInter (fun i => measurableSet_lt measurable_const (measurable_pi_apply i))
  exact hp.inter ((measurableSet_logPrimeBox _ _).inter
    ((measurableSet_logPrimeMeshCell _ _ _ _).inter
      (HistoricalThirdCoarse.P1OriginalCoarseFifth.measurableSet_jointRegion _ _ _ _ _)))

theorem correctedOriginalCell_subset_full
    (e : ℚ) (chi omega : ℝ) {a : ℝ} (ha : 0 < a) (m : ℕ) (j : Label5 m) :
    correctedOriginalCell e chi omega a m j ⊆ fullCorrectedCell e chi omega m j := by
  intro t ht
  exact ⟨fun i => ha.trans_le (mem_logPrimeBox.mp ht.1 i).1,
    mem_logPrimeBox.mpr (fun i =>
      ⟨(ha.trans_le (mem_logPrimeBox.mp ht.1 i).1).le, (mem_logPrimeBox.mp ht.1 i).2⟩), ht.2⟩

theorem eventually_mem_correctedOriginalCell
    (e : ℚ) (chi omega : ℝ) (m : ℕ) (j : Label5 m) {t : Point5}
    (ht : t ∈ fullCorrectedCell e chi omega m j) :
    ∀ᶠ n : ℕ in atTop, t ∈ correctedOriginalCell e chi omega (cutoff n) m j := by
  have hc : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 5, cutoff n < t i :=
    eventually_all.2 (fun i => cutoff_tendsto_zero.eventually (gt_mem_nhds (ht.1 i)))
  filter_upwards [hc] with n hn
  exact ⟨mem_logPrimeBox.mpr (fun i => ⟨(hn i).le, (mem_logPrimeBox.mp ht.2.1 i).2⟩), ht.2.2⟩

theorem fullCorrectedCell_eq_iUnion (e : ℚ) (chi omega : ℝ) (m : ℕ) (j : Label5 m) :
    fullCorrectedCell e chi omega m j =
      ⋃ n : ℕ, correctedOriginalCell e chi omega (cutoff n) m j := by
  ext t
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := (eventually_mem_correctedOriginalCell e chi omega m j ht).exists
    exact mem_iUnion.2 ⟨n, hn⟩
  · intro ht
    obtain ⟨n, hn⟩ := mem_iUnion.1 ht
    exact correctedOriginalCell_subset_full e chi omega (cutoff_pos n) m j hn

theorem correctedOriginalCell_aecover (e : ℚ) (chi omega : ℝ) (m : ℕ) (j : Label5 m) :
    AECover (volume.restrict (fullCorrectedCell e chi omega m j)) atTop
      (fun n : ℕ => correctedOriginalCell e chi omega (cutoff n) m j) where
  measurableSet n := P1OriginalFifthIntegral.truncatedCell_measurable e chi m omega (cutoff n) j
  ae_eventually_mem := by
    filter_upwards [ae_restrict_mem (fullCorrectedCell_measurable e chi omega m j)] with t ht
    exact eventually_mem_correctedOriginalCell e chi omega m j ht

section Selected
variable (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
  (e : ℚ) (chi omega : ℝ) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
  (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
  (hcheck : storedH45Check D J e rows = true)

theorem selected_owner (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J) :
    j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi D.m omega (D.cells5 ∩ J) :=
  (P1OriginalCoarseFifthContinuation.mem_selectedFifthCells e chi D.m omega (D.cells5 ∩ J) j).mpr
    ⟨hj, (howned.2.2 j hj).1, (howned.2.2 j hj).2⟩

theorem fullKernel_nonneg (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J)
    {t : Point5} (ht : t ∈ fullCorrectedCell e chi omega D.m j) :
    0 ≤ fullKernel D e chi omega rows licensed j t := by
  apply correctedCellKernel_nonneg _ _ t ht.1
  exact originalVariableFourthProfile_le_storedCap D J e chi omega rows licensed
    howned hcheck j hj t ht.2.2.1

theorem integrableOn_fullKernel_cutoff {a : ℝ} (ha : 0 < a)
    (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J) :
    IntegrableOn (fullKernel D e chi omega rows licensed j)
      (correctedOriginalCell e chi omega a D.m j) := by
  have hn := P1OriginalFifthIntegral.integrableOn_gatedWeightedProfile
    e chi D.m omega ha j (D.cap5 j : ℝ)
  have ho := integrableOn_actualOld4_weight e chi D.m omega a ha (D.cells5 ∩ J) j
    (selected_owner D J e chi omega howned j hj) rows licensed
  simpa only [fullKernel, correctedCellKernel, actualOldTest,
    P1OriginalFifthIntegral.reciprocalWeight, sub_mul] using hn.sub ho

/-- Full original old-cube gate measurability follows from the shared
finite fourth atoms on the genuine positive cutoff exhaustion. -/
theorem measurable_full_common_oldGate
    (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J) :
    MeasurableSet (commonRegion (fullCorrectedCell e chi omega D.m j)
      (originalVariableFourthProfile e chi omega D.m j rows licensed)) := by
  have heq : commonRegion (fullCorrectedCell e chi omega D.m j)
      (originalVariableFourthProfile e chi omega D.m j rows licensed) =
      ⋃ n : ℕ, commonRegion (correctedOriginalCell e chi omega (cutoff n) D.m j)
        (originalVariableFourthProfile e chi omega D.m j rows licensed) := by
    ext t
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := (eventually_mem_correctedOriginalCell e chi omega D.m j ht.1).exists
      exact mem_iUnion.2 ⟨n, hn, ht.2⟩
    · intro ht
      obtain ⟨n, hn⟩ := mem_iUnion.1 ht
      exact ⟨correctedOriginalCell_subset_full e chi omega (cutoff_pos n) D.m j hn.1, hn.2⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun n => measurable_common_actual_old4 e chi D.m omega (cutoff n)
    (D.cells5 ∩ J) j (selected_owner D J e chi omega howned j hj) rows licensed)

/-- Integrability is inferred from the derived bounded selected cutoff
integrals, not inserted as a target or borrowed from a different parent. -/
theorem integrableOn_fullKernel (homega : 0 < omega)
    (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J) :
    IntegrableOn (fullKernel D e chi omega rows licensed j)
      (fullCorrectedCell e chi omega D.m j) := by
  obtain ⟨V, hV⟩ := exists_corrected_selectedIntegral_zero_cutoff_limit
    D J e chi omega homega rows licensed howned hcheck
  obtain ⟨B, hB⟩ := (hV.comp cutoff_tendsto_right).isBoundedUnder_le
  have hfi : ∀ n : ℕ, IntegrableOn (fullKernel D e chi omega rows licensed j)
      (correctedOriginalCell e chi omega (cutoff n) D.m j)
      (volume.restrict (fullCorrectedCell e chi omega D.m j)) := by
    intro n
    change Integrable _ ((volume.restrict _).restrict _)
    rw [Measure.restrict_restrict_of_subset
      (correctedOriginalCell_subset_full e chi omega (cutoff_pos n) D.m j)]
    exact integrableOn_fullKernel_cutoff D J e chi omega rows licensed howned (cutoff_pos n) j hj
  have hnn : ∀ᵐ t ∂volume.restrict (fullCorrectedCell e chi omega D.m j),
      0 ≤ fullKernel D e chi omega rows licensed j t := by
    filter_upwards [ae_restrict_mem (fullCorrectedCell_measurable e chi omega D.m j)] with t ht
    exact fullKernel_nonneg D J e chi omega rows licensed howned hcheck j hj ht
  apply (correctedOriginalCell_aecover e chi omega D.m j).integrable_of_integral_bounded_of_nonneg_ae
    B hfi hnn
  filter_upwards [hB] with n hn
  change (∫ t, fullKernel D e chi omega rows licensed j t
    ∂(volume.restrict (fullCorrectedCell e chi omega D.m j)).restrict
      (correctedOriginalCell e chi omega (cutoff n) D.m j)) ≤ B
  rw [Measure.restrict_restrict_of_subset
    (correctedOriginalCell_subset_full e chi omega (cutoff_pos n) D.m j)]
  change correctedSelectedStoredIntegral D e chi omega (cutoff n) j rows licensed ≤ B
  apply le_trans ?_ hn
  exact Finset.single_le_sum (fun k hk =>
    setIntegral_nonneg (P1OriginalFifthIntegral.truncatedCell_measurable e chi D.m omega (cutoff n) k)
      (fun t ht => fullKernel_nonneg D J e chi omega rows licensed howned hcheck k hk
        (correctedOriginalCell_subset_full e chi omega (cutoff_pos n) D.m k ht))) hj

theorem tendsto_cellIntegral_full (homega : 0 < omega)
    (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J) :
    Tendsto (fun n : ℕ => correctedSelectedStoredIntegral D e chi omega (cutoff n) j rows licensed)
      atTop (𝓝 (fullCellIntegral D e chi omega rows licensed j)) := by
  have h := (correctedOriginalCell_aecover e chi omega D.m j).integral_tendsto_of_countably_generated
    (integrableOn_fullKernel D J e chi omega rows licensed howned hcheck homega j hj)
  have heq : ∀ n : ℕ, (∫ t, fullKernel D e chi omega rows licensed j t
      ∂(volume.restrict (fullCorrectedCell e chi omega D.m j)).restrict
        (correctedOriginalCell e chi omega (cutoff n) D.m j)) =
      correctedSelectedStoredIntegral D e chi omega (cutoff n) j rows licensed := by
    intro n
    rw [Measure.restrict_restrict_of_subset
      (correctedOriginalCell_subset_full e chi omega (cutoff_pos n) D.m j)]
  simpa only [heq] using h

theorem tendsto_selectedIntegral_full_sequence (homega : 0 < omega) :
    Tendsto (fun n : ℕ => selectedIntegral D J e chi omega rows licensed (cutoff n))
      atTop (𝓝 (fullSelectedIntegral D J e chi omega rows licensed)) := by
  exact tendsto_finsetSum (D.cells5 ∩ J) (fun j hj =>
    tendsto_cellIntegral_full D J e chi omega rows licensed howned hcheck homega j hj)

theorem tendsto_selectedIntegral_full (homega : 0 < omega) :
    Tendsto (fun a : ℝ => selectedIntegral D J e chi omega rows licensed a)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (fullSelectedIntegral D J e chi omega rows licensed)) := by
  obtain ⟨V, hV⟩ := exists_corrected_selectedIntegral_zero_cutoff_limit
    D J e chi omega homega rows licensed howned hcheck
  have heq : V = fullSelectedIntegral D J e chi omega rows licensed :=
    tendsto_nhds_unique (hV.comp cutoff_tendsto_right)
      (tendsto_selectedIntegral_full_sequence D J e chi omega rows licensed howned hcheck homega)
  rwa [heq] at hV

/-- The true full corrected cell retains its exact common/restored split;
the entire old-own-cube equality wall remains in the restored component. -/
theorem fullCellIntegral_common_add_restored (homega : 0 < omega)
    (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J) :
    fullCellIntegral D e chi omega rows licensed j =
      (∫ t in commonRegion (fullCorrectedCell e chi omega D.m j)
        (originalVariableFourthProfile e chi omega D.m j rows licensed),
        commonKernel (originalVariableFourthProfile e chi omega D.m j rows licensed) (D.cap5 j : ℝ) t) +
      ∫ t in restoredRegion (fullCorrectedCell e chi omega D.m j)
        (originalVariableFourthProfile e chi omega D.m j rows licensed) (D.cap5 j : ℝ),
        restoredKernel (D.cap5 j : ℝ) t := by
  apply integral_partition _ _ _ (fullCorrectedCell_measurable e chi omega D.m j)
    (measurable_full_common_oldGate D J e chi omega rows licensed howned j hj)
      (integrableOn_fullKernel D J e chi omega rows licensed howned hcheck homega j hj)
  intro t ht
  exact originalVariableFourthProfile_le_storedCap D J e chi omega rows licensed howned hcheck j hj t ht.2.2.1

theorem tendsto_corrected_normalizedCharge_fullIntegral (homega : 0 < omega)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => normalizedCharge D J e chi omega rows licensed N (cap N))
      P1OriginalFifthMovingScaleLimit.evenTargets
      (𝓝 (fullSelectedIntegral D J e chi omega rows licensed)) := by
  obtain ⟨V, _hV, hI, hmean⟩ := exists_corrected_full_charge_and_zero_cutoff_limit
    D J e chi omega homega rows licensed howned hcheck
  have heq : V = fullSelectedIntegral D J e chi omega rows licensed :=
    tendsto_nhds_unique hI (tendsto_selectedIntegral_full D J e chi omega rows licensed howned hcheck homega)
  simpa only [heq] using hmean cap hcap

/-- Literal original fourth-minus-corrected-fifth retained density, with
d=1 and empty initial history, has this exact untruncated integral limit. -/
theorem tendsto_corrected_normalizedRetainedDifference_fullIntegral (homega : 0 < omega)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => normalizedRetainedDifference D J e chi omega rows licensed N (cap N))
      P1OriginalFifthMovingScaleLimit.evenTargets
      (𝓝 (fullSelectedIntegral D J e chi omega rows licensed)) := by
  obtain ⟨V, _hV, hI, hmean⟩ := exists_corrected_policy_and_zero_cutoff_limit
    D J e chi omega homega rows licensed howned hcheck
  have heq : V = fullSelectedIntegral D J e chi omega rows licensed :=
    tendsto_nhds_unique hI (tendsto_selectedIntegral_full D J e chi omega rows licensed howned hcheck homega)
  simpa only [heq] using hmean cap hcap

end Selected
end
end ImbalancedChen.P1CorrectedFifthUntruncatedIntegral
