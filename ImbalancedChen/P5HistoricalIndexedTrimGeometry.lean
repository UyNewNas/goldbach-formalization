import ImbalancedChen.P5OriginalLicensedTrimResidual
import ImbalancedChen.P1HistoricalFifthIndexedBankError

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The independent full literal archive supplies the source INDEX and row.
All source multiplicities remain in the sums. Canonical owner omission and
the additional true fifth-gate rejection are distinct disjoint regions.
Neither residual is assumed empty or small; the B13 payment retains both.
-/
namespace ImbalancedChen.P5HistoricalIndexedTrimGeometry
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1FifthUnitBoxGainDecomposition
open P1OriginalFifthLiteralKernelModulus P1OriginalFifthActualB13IntegralError
open P1OriginalFifthAdoptedOwnerBank P1OriginalFifthJointMeshSchedule
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthIndexedBankError
open P5OriginalLicensedTrimResidual

/-- Actual points lost ONLY by the extra zero/buffer fifth-gate filters. -/
def gateRejectedDomain (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) : Set (Fin 5 → ℝ) :=
  adoptedDomain (archiveRow i) e q chi omega 0 \ indexedDomain i e q chi omega 0

def gateRejectedCost (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  rowMassBound (archiveRow i) * (volume (gateRejectedDomain i e q chi omega)).toReal

theorem indexedDomain_subset_canonical (i : ArchiveIndex) (e : ℚ) (q : ℕ)
    (chi omega : ℝ) (z : ℚ) :
    indexedDomain i e q chi omega z ⊆ adoptedDomain (archiveRow i) e q chi omega z := by
  intro t ht
  obtain ⟨j, hj, htj⟩ := mem_iUnion₂.mp ht
  exact mem_iUnion₂.mpr ⟨j, licensedOwner_adopted i e q chi omega j hj, htj⟩

theorem gateRejected_measurable (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    MeasurableSet (gateRejectedDomain i e q chi omega) :=
  (adoptedDomain_measurable (archiveRow i) e q chi omega 0).diff
    (ownerUnion_measurable _ _ _ _ _ _)

theorem gateRejected_subset_parent (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    gateRejectedDomain i e q chi omega ⊆ fixedParent (archiveRow i) :=
  fun _ ht => adoptedDomain_subset_fixedParent (archiveRow i) e q chi omega 0 ht.1

/-- An exact region decomposition. In particular a partially rejected
owner cell is not replaced by a boolean count of missing labels. -/
theorem indexedOmitted_eq_canonical_union_gate (i : ArchiveIndex) (e : ℚ) (q : ℕ)
    (chi omega : ℝ) :
    indexedOmitted i e q chi omega =
      omittedParent (archiveRow i) e q chi omega ∪ gateRejectedDomain i e q chi omega := by
  ext t
  constructor
  · intro ht
    by_cases ha : t ∈ adoptedDomain (archiveRow i) e q chi omega 0
    · exact Or.inr ⟨ha, ht.2⟩
    · exact Or.inl ⟨ht.1, ha⟩
  · rintro (ht | ht)
    · exact ⟨ht.1, fun hi => ht.2 (indexedDomain_subset_canonical i e q chi omega 0 hi)⟩
    · exact ⟨gateRejected_subset_parent i e q chi omega ht, ht.2⟩

theorem canonical_omitted_disjoint_gate (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Disjoint (omittedParent (archiveRow i) e q chi omega) (gateRejectedDomain i e q chi omega) := by
  exact Set.disjoint_left.mpr (fun _ hcanonical hgate => hcanonical.2 hgate.1)

theorem indexedTrimCost_eq_canonical_add_gate (i : ArchiveIndex) (hi : i ∈ licensedIndices)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    indexedTrimCost i e q chi omega =
      omittedVolumeCost (archiveRow i) e q chi omega + gateRejectedCost i e q chi omega := by
  have hg := licensedIndex_geometry i hi
  have hparent : volume (fixedParent (archiveRow i)) < ∞ :=
    (measure_mono inter_subset_left).trans_lt
      (by rw [rawBox_volume _ hg.1]; exact ENNReal.ofReal_lt_top)
  have hc : volume (omittedParent (archiveRow i) e q chi omega) ≠ ∞ :=
    ((measure_mono sdiff_subset).trans_lt hparent).ne
  have hgate : volume (gateRejectedDomain i e q chi omega) ≠ ∞ :=
    ((measure_mono (gateRejected_subset_parent i e q chi omega)).trans_lt hparent).ne
  unfold indexedTrimCost omittedVolumeCost gateRejectedCost
  rw [indexedOmitted_eq_canonical_union_gate,
    measure_union (canonical_omitted_disjoint_gate i e q chi omega)
      (gateRejected_measurable i e q chi omega), ENNReal.toReal_add hc hgate, mul_add]

/-- The original margin licence implies the independently constructed
archive bank's BASE geometry, without interpreting any saved statistic. -/
theorem originalLicence_baseGeometry (i : ArchiveIndex)
    (hc : ownerLicenseCheck (archiveRow i) = true) : baseGeometry (archiveRow i) :=
  licensed_primitive_key_bounds (archiveRow i) hc

/-- All 292633 source positions remain here, including repeated rows. -/
def canonicalResidualIndices : Finset ArchiveIndex :=
  Finset.univ.filter (fun i => ownerLicenseCheck (archiveRow i) = false)

def marginResidualIndices : Finset ArchiveIndex :=
  licensedIndices.filter (fun i => ownerLicenseCheck (archiveRow i) = false)

theorem canonicalResidual_iff (i : ArchiveIndex) :
    i ∈ canonicalResidualIndices ↔
      P1FifthMask5RawOwnerLicence.mask5WholeRawCheck (archiveRow i) = false ∧
      P1FifthMask6RawOwnerLicence.mask6WholeRawCheck (archiveRow i) = false := by
  simp [canonicalResidualIndices, ownerLicenseCheck]

/-- This full-archive equality does NOT assert that any residual index
passes baseGeometry or that it has finite original kernel mass. -/
theorem full_archive_canonical_trim_eq_explicit_residual
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10) (q : ℕ) (hq : 0 < q)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) (hw : omega ≤ 1 / 400) :
    (∑ i : ArchiveIndex, omittedVolumeCost (archiveRow i) e q chi omega) =
      ∑ i ∈ canonicalResidualIndices, omittedVolumeCost (archiveRow i) e q chi omega := by
  unfold canonicalResidualIndices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hc : ownerLicenseCheck (archiveRow i) = true
  · have hz := licensed_omittedVolumeCost_zero (archiveRow i) hc
      e he hemax chi omega hchi q hq hstep hw
    simp [hc, hz]
  · have hf : ownerLicenseCheck (archiveRow i) = false := Bool.eq_false_iff.mpr hc
    simp only [hf, if_true]

def residualCanonicalTrim (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ i ∈ marginResidualIndices, omittedVolumeCost (archiveRow i) e q chi omega

def residualParentCost : ℝ :=
  ∑ i ∈ marginResidualIndices,
    rowMassBound (archiveRow i) * (volume (fixedParent (archiveRow i))).toReal

def gateRejectedBankCost (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ i ∈ licensedIndices, gateRejectedCost i e q chi omega

/-- True extra fifth-gate rejection is paid even on a raw parent whose
third-owner geometry has zero canonical omission. -/
theorem actual_licensedTrimCost_eq_two_geometric_residuals
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10) (q : ℕ) (hq : 0 < q)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) (hw : omega ≤ 1 / 400) :
    licensedTrimCost e q chi omega =
      residualCanonicalTrim e q chi omega + gateRejectedBankCost e q chi omega := by
  have hsum : (∑ i ∈ licensedIndices, omittedVolumeCost (archiveRow i) e q chi omega) =
      residualCanonicalTrim e q chi omega := by
    unfold residualCanonicalTrim marginResidualIndices
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hc : ownerLicenseCheck (archiveRow i) = true
    · have hz := licensed_omittedVolumeCost_zero (archiveRow i) hc
        e he hemax chi omega hchi q hq hstep hw
      simp [hc, hz]
    · have hf : ownerLicenseCheck (archiveRow i) = false := Bool.eq_false_iff.mpr hc
      simp only [hf, if_true]
  unfold licensedTrimCost gateRejectedBankCost
  rw [show (∑ i ∈ licensedIndices, indexedTrimCost i e q chi omega) =
      ∑ i ∈ licensedIndices, (omittedVolumeCost (archiveRow i) e q chi omega +
        gateRejectedCost i e q chi omega) from
      Finset.sum_congr rfl (fun i hi => indexedTrimCost_eq_canonical_add_gate i hi e q chi omega)]
  rw [Finset.sum_add_distrib, hsum]

theorem residualCanonicalTrim_le_actual_parent_cost (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    residualCanonicalTrim e q chi omega ≤ residualParentCost := by
  apply Finset.sum_le_sum
  intro i hi
  have hg := licensedIndex_geometry i (Finset.mem_filter.mp hi).1
  have hfinite : volume (fixedParent (archiveRow i)) < ∞ :=
    (measure_mono inter_subset_left).trans_lt
      (by rw [rawBox_volume _ hg.1]; exact ENNReal.ofReal_lt_top)
  exact mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hfinite.ne (measure_mono sdiff_subset))
    (by linarith [one_le_rowMassBound (archiveRow i)])

/-- Original B13 on the source-index bank now has a concrete geometric
remainder: residual whole parents once, plus actual rejected gate regions.
The separately defined residualIndices outside BASE geometry remain open.
No target-smallness premise is introduced. -/
theorem exists_actual_indexed_schedule_with_geometric_remainder
    (eta omega : ℝ) (heta : 0 < eta) (hwpos : 0 < omega) (hw : omega ≤ 1 / 400) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      |licensedBankError e q ((e : ℝ) / 20) omega| <
        eta / 2 + residualParentCost + gateRejectedBankCost e q ((e : ℝ) / 20) omega := by
  obtain ⟨e, q, he, hecap, hq, hstep, hmesh, herr, _⟩ :=
    exists_actual_indexed_error_schedule eta omega heta hwpos
  have heQ : (0 : ℚ) < e := by exact_mod_cast he
  have hemaxQ : e ≤ (3 / 51200 : ℚ) := by exact_mod_cast hecap.le
  have hchi : (e : ℝ) / 20 < (e : ℝ) / 10 := by linarith
  rw [actual_licensedTrimCost_eq_two_geometric_residuals e heQ hemaxQ
    ((e : ℝ) / 20) omega hchi q hq hstep hw] at herr
  have hres := residualCanonicalTrim_le_actual_parent_cost e q ((e : ℝ) / 20) omega
  exact ⟨e, q, he, hecap, hq, hstep, hmesh, by linarith⟩

end
end ImbalancedChen.P5HistoricalIndexedTrimGeometry
