import ImbalancedChen.P5CanonicalOwnerFilterStrips
import ImbalancedChen.P5HistoricalRejectedCoreReserve

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual canonical owner-filter and extra-gate support losses share a true
linear buffer payment. Both genuine history-invalid and fifth support-
invalid regions remain visible; neither is silently changed into a wall.
-/
namespace ImbalancedChen.P5HistoricalCanonicalFilterReserve
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthQuantitativeGateRefinement P1OriginalFifthGrid400RefinedFullBoxCover
open P1FifthUnitBoxGainDecomposition P1OriginalFifthAdoptedOwnerBank
open P1OriginalFifthLiteralKernelModulus
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthIndexedBankError
open P5HistoricalIndexedTrimGeometry P5ActualFifthGateStripLocalization
open P5CanonicalOwnerFilterStrips P5HistoricalRejectedCoreReserve

def canonicalHistoryCost (i : ArchiveIndex) (q : ℕ) (chi omega : ℝ) : ℝ :=
  rowMassBound (archiveRow i) * (volume (canonicalInvalidHistory (archiveRow i) q chi omega)).toReal

def canonicalFilterCost (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  rowMassBound (archiveRow i) * (volume (canonicalFilterRejection (archiveRow i) e q chi omega)).toReal

theorem omittedVolumeCost_exact_canonical_split (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    omittedVolumeCost (archiveRow i) e q chi omega =
      canonicalHistoryCost i q chi omega + canonicalFilterCost i e q chi omega := by
  have hparent : fixedParent (archiveRow i) ⊆ unitCube := by
    intro t ht k _
    have hk := mem_logPrimeBox.mp ht.2 k
    exact ⟨hk.1, by linarith [hk.2]⟩
  have hunit : volume unitCube = 1 := by simp [unitCube, volume_pi_pi, Real.volume_Icc]
  have hfinite : volume (fixedParent (archiveRow i)) < ∞ :=
    (measure_mono hparent).trans_lt (by rw [hunit]; simp)
  have hh : volume (canonicalInvalidHistory (archiveRow i) q chi omega) ≠ ∞ :=
    ((measure_mono sdiff_subset).trans_lt hfinite).ne
  have hf : volume (canonicalFilterRejection (archiveRow i) e q chi omega) ≠ ∞ :=
    ((measure_mono (fun _ ht => unfilteredZeroDomain_subset_parent (archiveRow i) q chi omega ht.1)).trans_lt hfinite).ne
  have hfilterMeas : MeasurableSet (canonicalFilterRejection (archiveRow i) e q chi omega) :=
    (ownerUnion_measurable _ _ _ _ _ _).diff (adoptedDomain_measurable (archiveRow i) e q chi omega 0)
  unfold omittedVolumeCost canonicalHistoryCost canonicalFilterCost
  rw [canonical_omitted_exact_history_filter_partition,
    measure_union (canonical_history_filter_disjoint (archiveRow i) e q chi omega) hfilterMeas,
    ENNReal.toReal_add hh hf, mul_add]

theorem canonicalFilterCost_le_actual_strip_rate (i : ArchiveIndex) (hi : i ∈ licensedIndices)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw0 : 0 ≤ omega) (hw : omega ≤ 1 / 800)
    (hh : (meshStepQ (refinedMesh q) : ℝ) ≤ 1 / 800)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) :
    canonicalFilterCost i e q chi omega ≤ rowMassBound (archiveRow i) *
      (12 * (4 * (e : ℝ) + 2 * (meshStepQ (refinedMesh q) : ℝ))) := by
  have hg := licensedIndex_geometry i hi
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hhR : (0 : ℝ) < (meshStepQ (refinedMesh q) : ℝ) := by exact_mod_cast meshStepQ_pos (refinedMesh q)
  have hd : 0 ≤ 12 * (4 * (e : ℝ) + 2 * (meshStepQ (refinedMesh q) : ℝ)) := by positivity
  have hv := ENNReal.toReal_mono (by simp : ENNReal.ofReal
      (12 * (4 * (e : ℝ) + 2 * (meshStepQ (refinedMesh q) : ℝ))) ≠ ∞)
    (canonicalFilterRejection_volume (archiveRow i) hg.1 (hg.2.2.1 2)
      e he q chi omega hw0 hw hh hstep)
  rw [ENNReal.toReal_ofReal hd] at hv
  exact mul_le_mul_of_nonneg_left hv (by linarith [one_le_rowMassBound (archiveRow i)])

def canonicalHistoryBankCost (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ i ∈ licensedIndices, canonicalHistoryCost i q chi omega

def canonicalFilterBankCost (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ i ∈ licensedIndices, canonicalFilterCost i e q chi omega

/-- These are FOUR independently defined actual regions, each at the
same source index. This does not require index-value deduplication. -/
theorem actual_licensedTrimCost_exact_four_regions (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    licensedTrimCost e q chi omega = canonicalHistoryBankCost q chi omega +
      canonicalFilterBankCost e q chi omega + supportCoreBankCost licensedIndices e q chi omega +
        invalidCoreBankCost licensedIndices e q chi omega := by
  have hrow (i : ArchiveIndex) (hi : i ∈ licensedIndices) :
      indexedTrimCost i e q chi omega = canonicalHistoryCost i q chi omega +
        canonicalFilterCost i e q chi omega + supportCoreCost i e q chi omega + invalidCoreCost i e q chi omega := by
    rw [indexedTrimCost_eq_canonical_add_gate i hi,
      omittedVolumeCost_exact_canonical_split, gateRejectedCost_exact_core_split]
    ring
  unfold licensedTrimCost canonicalHistoryBankCost canonicalFilterBankCost supportCoreBankCost invalidCoreBankCost
  simp_rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hrow

theorem canonicalFilterBankCost_le_linear_buffer
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw0 : 0 ≤ omega) (hw : omega ≤ 1 / 800)
    (hh : (meshStepQ (refinedMesh q) : ℝ) ≤ 1 / 800)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi)
    (hstepE : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20) :
    canonicalFilterBankCost e q chi omega ≤ 64 * sourceMassSum licensedIndices * (e : ℝ) := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hsmall : (meshStepQ (refinedMesh q) : ℝ) ≤ (e : ℝ) / 20 := by simpa only [cast_meshStepQ] using hstepE
  have hrate : 12 * (4 * (e : ℝ) + 2 * (meshStepQ (refinedMesh q) : ℝ)) ≤ 64 * (e : ℝ) := by linarith
  calc
    _ ≤ ∑ i ∈ licensedIndices, rowMassBound (archiveRow i) * (64 * (e : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (canonicalFilterCost_le_actual_strip_rate i hi e he q chi omega hw0 hw hh hstep).trans
        (mul_le_mul_of_nonneg_left hrate (by linarith [one_le_rowMassBound (archiveRow i)]))
    _ = _ := by rw [← Finset.sum_mul]; unfold sourceMassSum; ring

/-- The two PROVED thin parts now have a prescribed linear buffer rate.
Only true history-invalid and true fifth-support-invalid cores are unpaid.
Nothing here bounds changed-parent gain by an old-source B13 estimate. -/
theorem actual_licensedTrimCost_le_invalid_regions_add_buffer_rate
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw0 : 0 ≤ omega) (hw : omega ≤ 1 / 800)
    (hh : (meshStepQ (refinedMesh q) : ℝ) ≤ 1 / 800)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi)
    (hstepE : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20) :
    licensedTrimCost e q chi omega ≤ canonicalHistoryBankCost q chi omega +
      invalidCoreBankCost licensedIndices e q chi omega + 416 * sourceMassSum licensedIndices * (e : ℝ) := by
  rw [actual_licensedTrimCost_exact_four_regions]
  have hc := canonicalFilterBankCost_le_linear_buffer e he q chi omega hw0 hw hh hstep hstepE
  have hg := supportCoreBankCost_le_linear_buffer licensedIndices e he q chi omega hstepE
  linarith

end
end ImbalancedChen.P5HistoricalCanonicalFilterReserve
