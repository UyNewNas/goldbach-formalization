import ImbalancedChen.P5FullStoredParentSameOwnerBinding
import ImbalancedChen.P5OriginalFifthArchiveActualMean

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_CREDIT.
The independently defined original fullSelectedIntegral consumes the full
indexed owner ledger. Source uniqueness is used BEFORE summing gains.
No full decoded-family gate assumption or deduplication of source rows is
needed. This module adds no finite decisions or literal archive data.
-/
namespace ImbalancedChen.P5FullArchiveOwnerIntegralAssembly
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthRawBoxSelectorEquivalence
open P1ActualVariableFifthProfiles P1ActualVariableFifthUntruncatedDomination
open P1FifthUnitBoxGainDecomposition
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthTypedKeyPartition
open P5HistoricalMask56FullSourceChildren P5FullStoredParentSameOwnerBinding
open P5OriginalFifthArchiveActualMean

/-- Even the last half-open mesh cell has a point. This prevents an empty
cell from being used as a spurious common owner of two source positions. -/
theorem mesh_lower_mem (m : ℕ) (j : Label5 m) :
    logPrimeMeshLo 0 (19 / 96) m j ∈ logPrimeMeshCell 0 (19 / 96) m j := by
  apply mem_logPrimeMeshCell.mpr
  intro k
  exact ⟨le_rfl, (logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 19 / 96) m j k).2.1⟩

theorem licensed_owner_index_unique (i k : ArchiveIndex) (e : ℚ) (q : ℕ)
    (chi omega : ℝ) (j : Label5 (refinedMesh q))
    (hi : j ∈ licensedOwners i e q chi omega)
    (hk : j ∈ licensedOwners k e q chi omega) : i = k := by
  let t := logPrimeMeshLo 0 (19 / 96) (refinedMesh q) j
  have ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j := mesh_lower_mem _ _
  exact common_raw_point_index_unique i k t
    (decodeFifthRows_source_geometry (archiveRow i) (refinedMesh q)
      (sourceOwnerRow i q j) (licensedOwner_decoded i e q chi omega j hi) t ht).2.2.2
    (decodeFifthRows_source_geometry (archiveRow k) (refinedMesh q)
      (sourceOwnerRow k q j) (licensedOwner_decoded k e q chi omega j hk) t ht).2.2.2

theorem licensed_owner_sets_pairwise_disjoint (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Set.PairwiseDisjoint (licensedIndices : Set ArchiveIndex)
      (fun i => licensedOwners i e q chi omega) := by
  intro i _hi k _hk hne
  exact Finset.disjoint_left.mpr (fun j hji hjk =>
    hne (licensed_owner_index_unique i k e q chi omega j hji hjk))

/-- Every point of the actual fullCell is already in its decoded source
box. Raw clipping is therefore exact on retained owners, not a loss. -/
theorem licensed_rawOwnerDomain_eq_fullCell (i : ArchiveIndex) (e : ℚ) (q : ℕ)
    (chi omega : ℝ) (j : Label5 (refinedMesh q))
    (hj : j ∈ licensedOwners i e q chi omega) :
    rawOwnerDomain (archiveRow i) e chi (refinedMesh q) omega j =
      P1OriginalFifthUntruncatedIntegral.fullCell e chi (refinedMesh q) omega j := by
  apply Set.inter_eq_right.mpr
  intro t ht
  exact (decodeFifthRows_source_geometry (archiveRow i) (refinedMesh q)
    (sourceOwnerRow i q j) (licensedOwner_decoded i e q chi omega j hj)
    t ht.2.2.1).2.2.2

/-- The original full licensed bank, with its independently defined old
fourth seed, has exactly this source candidate at its unique owner label. -/
theorem full_bank_actualNext5_eq_source (i : ArchiveIndex) (hi : i ∈ licensedIndices)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (j : Label5 (refinedMesh q))
    (hj : j ∈ licensedOwners i e q chi omega)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop) (t : Fin 5 → ℝ) :
    actualNext5 e chi (refinedMesh q) omega j rows4 licensed4
      (licensedRows e q chi omega) t =
      max (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4 t)
        (rawCandidate (e : ℝ) (archiveRow i) t) := by
  unfold actualNext5
  apply le_antisymm
  · apply finiteMax_le _ _ _ _ _ (le_max_left _ _)
    intro r hr hel
    obtain ⟨k, _hk, hkj, _hr, hdec⟩ := licensedRows_source_index e q chi omega r hr
    have hkj' : j ∈ licensedOwners k e q chi omega := hel.1 ▸ hkj
    have hki : k = i := licensed_owner_index_unique k i e q chi omega j hkj' hj
    subst k
    rw [decodeFifthRows_selected_eq (archiveRow i) (refinedMesh q) r hdec,
      ← rawCandidate_eq_candidate (e : ℝ) (archiveRow i) t]
    exact le_max_right _ _
  · apply max_le (finiteMax_seed_le _ _ _ _)
    have hr : sourceOwnerRow i q j ∈ licensedRows e q chi omega :=
      Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
    have hel : ownerEligible e (refinedMesh q) j (sourceOwnerRow i q j) :=
      ⟨rfl, licensedOwner_gate_buffer i e q chi omega j hj⟩
    simpa only [sourceOwnerRow, ← rawCandidate_eq_candidate (e : ℝ) (archiveRow i) t] using
      finiteMax_row_le (licensedRows e q chi omega) (ownerEligible e (refinedMesh q) j)
        (fun r => candidate (e : ℝ) r.selected t)
        (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4 t)
        (sourceOwnerRow i q j) hr hel

theorem full_bank_actualKernel_eq_source (i : ArchiveIndex) (hi : i ∈ licensedIndices)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (j : Label5 (refinedMesh q))
    (hj : j ∈ licensedOwners i e q chi omega)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop) (t : Fin 5 → ℝ) :
    actualKernel e chi (refinedMesh q) omega j rows4 licensed4 (licensedRows e q chi omega) t =
      rawOwnerKernel e chi (refinedMesh q) omega j rows4 licensed4 (archiveRow i) t := by
  change (_ - _) * (∏ k, 1 / t k) = (_ - _) * (∏ k, 1 / t k)
  rw [full_bank_actualNext5_eq_source i hi e q chi omega j hj rows4 licensed4 t]

theorem rawOwnerIntegral_eq_full_bank_cell (i : ArchiveIndex) (hi : i ∈ licensedIndices)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (j : Label5 (refinedMesh q))
    (hj : j ∈ licensedOwners i e q chi omega)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop) :
    rawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j rows4 licensed4 =
      fullCellIntegral e chi (refinedMesh q) omega rows4 licensed4 (licensedRows e q chi omega) j := by
  unfold rawOwnerIntegral fullCellIntegral
  rw [licensed_rawOwnerDomain_eq_fullCell i e q chi omega j hj]
  apply setIntegral_congr_fun (P1OriginalFifthUntruncatedIntegral.fullCell_measurable _ _ _ _ _)
  intro t _ht
  exact (full_bank_actualKernel_eq_source i hi e q chi omega j hj rows4 licensed4 t).symm

theorem selected_globalOwners_eq (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega
      (globalOwners e q chi omega) = globalOwners e q chi omega := by
  ext j
  constructor
  · intro hj
    exact ((P1OriginalCoarseFifthContinuation.mem_selectedFifthCells _ _ _ _ _ _).mp hj).1
  · exact globalOwner_selected_buffer e q chi omega j

/-- Exact reassembly of the independently defined analytic target. No
factor64, repeated source owner, or new profile is introduced. -/
theorem archiveFifthIntegral_eq_indexed_owner_sum
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    archiveFifthIntegral rows4 licensed4 e q chi omega =
      ∑ i ∈ licensedIndices, ∑ j ∈ licensedOwners i e q chi omega,
        rawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j rows4 licensed4 := by
  unfold archiveFifthIntegral fullSelectedIntegral
  rw [selected_globalOwners_eq, globalOwners,
    Finset.sum_biUnion (licensed_owner_sets_pairwise_disjoint e q chi omega)]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_congr rfl (fun j hj =>
    (rawOwnerIntegral_eq_full_bank_cell i hi e q chi omega j hj rows4 licensed4).symm)

theorem rawOwnerIntegral_nonneg (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (j : Label5 (refinedMesh q)) (rows4 : Finset ProducerRow)
    (licensed4 : ProducerRow → Prop) :
    0 ≤ rawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j rows4 licensed4 := by
  apply setIntegral_nonneg (rawOwnerDomain_measurable _ _ _ _ _ _)
  intro t ht
  exact rawGainKernel_nonneg (e : ℝ)
    (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4)
    (archiveRow i) t ht.2.1

/-- The original mask5/mask6 licensed saving is paid by ONE actual full
bank integral. Other source positions remain nonnegative contributions. -/
theorem mask56_owner_sum_le_archiveFifthIntegral
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    (∑ i ∈ mask56Indices, ∑ j ∈ licensedOwners i e q chi omega,
      rawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j rows4 licensed4) ≤
      archiveFifthIntegral rows4 licensed4 e q chi omega := by
  rw [archiveFifthIntegral_eq_indexed_owner_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => mask56Index_is_base i hi)
  intro i _hi _hnot
  exact Finset.sum_nonneg (fun j _hj => rawOwnerIntegral_nonneg i e q chi omega j rows4 licensed4)

/-- Actual stored replacement minus its explicit OLD branch defect and
strict clipping reserve enters the original full integral unchanged. -/
theorem full_stored_minus_defects_le_archiveFifthIntegral
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry) :
    (∑ i ∈ mask56Indices, (storedNewQ i : ℝ)) -
      (∑ i ∈ mask56Indices, (oldBranchDefectQ i : ℝ)) -
      (∑ i ∈ mask56Indices, indexedActualReserve64 i e q chi omega) ≤
      archiveFifthIntegral rows4 licensed4 e q chi omega :=
  (full_licensed_stored_sum_minus_defects e he q chi omega hw hwr rows4 licensed4 hgeometry).trans
    (mask56_owner_sum_le_archiveFifthIntegral rows4 licensed4 e q chi omega)

end
end ImbalancedChen.P5FullArchiveOwnerIntegralAssembly
