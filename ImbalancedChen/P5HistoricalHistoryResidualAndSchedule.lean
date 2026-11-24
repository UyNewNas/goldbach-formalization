import ImbalancedChen.P5HistoricalBelowMuCommonParent
import ImbalancedChen.P5HistoricalGatePaidReserveSchedule

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
An exact source-side description of the remaining history obstruction,
and the same H schedule with the actual changed-parent term eliminated.
The history region is NOT assumed small or replaced by a proper wall.
-/
namespace ImbalancedChen.P5HistoricalHistoryResidualAndSchedule
noncomputable section
open Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open HistoricalThirdCoarse HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthAdoptedOwnerBank
open P1FifthUnitBoxGainDecomposition P1OriginalFifthMovingMeshFubiniBridge
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthIndexedBankError
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthCommonAncestorExcess
open P5CanonicalOwnerFilterStrips P5HistoricalCanonicalFilterReserve
open P5HistoricalIndexedTrimGeometry P5HistoricalUniformExtraGatePayment
open P5HistoricalGatePaidReserveSchedule P5HistoricalBelowMuCommonParent

/-- Membership of the true unfiltered source is decided by this very
decoded cell's causal history. Uniqueness prevents switching to another
owner when its history fails. -/
theorem mem_unfiltered_iff_same_decoded_history
    (i : ArchiveIndex) (q : ℕ) (chi omega : ℝ)
    (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell) :
    t ∈ unfilteredZeroDomain (archiveRow i) q chi omega ↔
      t ∈ jointRegion 0 chi (refinedMesh q) omega r.cell := by
  constructor
  · intro hu
    obtain ⟨j, _hj, htj⟩ := mem_iUnion₂.mp hu
    have heq := logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96)
      htj.2.2.2.1 ht
    simpa only [heq] using htj.2.2.2.2
  · intro hjoint
    have hraw := (decodeFifthRows_source_geometry
      (archiveRow i) (refinedMesh q) r hr t ht).2.2.2
    have hambient := logPrimeMeshCell_subset_box
      (by norm_num : (0 : ℝ) < 19 / 96) (refinedMesh q) r.cell ht
    have hpos : ∀ k, 0 < t k := by
      intro k
      have hkey : (1 : ℝ) ≤ ((archiveRow i).lo k : ℝ) := by
        exact_mod_cast (archiveRow_baseGeometry i).2.2.1 k
      have hlo := (hraw k).1
      simp only [FifthWireRow.lower, archiveRow_grid] at hlo
      push_cast at hlo
      linarith
    exact mem_iUnion₂.mpr ⟨r.cell, Finset.mem_image.mpr ⟨r, hr, rfl⟩,
      hraw, hpos, hambient, ht, hjoint⟩

/-- FirstStop and the initial first cube already hold throughout each
decoded original raw cell at zero buffer; they are not residual costs. -/
theorem decoded_zero_first_history
    (i : ArchiveIndex) (q : ℕ) (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell) :
    t ∈ firstLabelRegion 0 (refinedMesh q) ∧ 3 * t 0 < initial 0 := by
  have hraw := (decodeFifthRows_source_geometry
    (archiveRow i) (refinedMesh q) r hr t ht).2.2.2
  have hfirst := archive_first_coordinate_lt_mu i t hraw
  have hcontained : fifthCellContained (archiveRow i) (refinedMesh q) r.cell := by
    obtain ⟨_hg, _hm, j, hj, heq⟩ :=
      (mem_decodeFifthRows_iff (archiveRow i) (refinedMesh q) r).mp hr
    cases heq
    exact hj
  have hkey : ((archiveRow i).lo 0 : ℝ) ≤ 77 := by
    exact_mod_cast (archiveRow_baseGeometry i).2.2.2
  have hupper : ((archiveRow i).upper 0 : ℝ) ≤ 39 / 200 := by
    simp only [FifthWireRow.upper, archiveRow_grid]
    push_cast
    linarith
  have hendpoint : (qLogPrimeMeshHi 0 (19 / 96) (refinedMesh q) r.cell 0 : ℝ) ≤
      ((archiveRow i).upper 0 : ℝ) := by
    exact_mod_cast (hcontained 0).2
  constructor
  · apply (P1OriginalHistoricalFifthOwnCubeAffineGates.firstLabelRegion_on_cell
      0 (refinedMesh q) r.cell t ht).mpr
    rw [← congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) (refinedMesh q) r.cell) 0]
    dsimp only [VariableEnvelope.extendedFirstStop]
    linarith
  · dsimp only [VariableEnvelope.mu] at hfirst
    dsimp only [initial, VariableEnvelope.extendedDistributionCap]
    linarith

/-- Exact unpaid tests, not a conjectured thin-strip enclosure. The
CURRENT third exponent retains its genuine cell/rough/fallback dispatch. -/
theorem mem_canonicalInvalidHistory_iff_actual_failures
    (i : ArchiveIndex) (q : ℕ) (chi omega : ℝ)
    (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell) :
    t ∈ canonicalInvalidHistory (archiveRow i) q chi omega ↔
      ¬ StrictAnti t ∨
        currentExponent 0 chi (refinedMesh q) omega r.cell t ≤ 3 * t 0 ∨
        currentExponent 0 chi (refinedMesh q) omega r.cell t ≤ t 0 + t 1 + 3 * t 2 := by
  have hraw := (decodeFifthRows_source_geometry
    (archiveRow i) (refinedMesh q) r hr t ht).2.2.2
  have hparent : t ∈ fixedParent (archiveRow i) :=
    ⟨hraw, logPrimeMeshCell_subset_box
      (by norm_num : (0 : ℝ) < 19 / 96) (refinedMesh q) r.cell ht⟩
  obtain ⟨hstop, hroot⟩ := decoded_zero_first_history i q r hr t ht
  rw [canonicalInvalidHistory, mem_diff,
    mem_unfiltered_iff_same_decoded_history i q chi omega r hr t ht,
    mem_jointRegion]
  simp only [hparent, true_and, hstop, hroot, not_and_or, not_lt]

/-- Retain H's witnesses, rather than choosing an unrelated second mesh.
The entire extra-gate cost and the changed-parent term on every original
source prefix vanish on that very schedule. The original history cost
still appears unchanged in the original B13 estimate. -/
theorem exists_same_schedule_with_unchanged_archive_parents
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (eta omega : ℝ) (heta : 0 < eta) (homega : 0 < omega) (hw : omega ≤ 1 / 800) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧
      e ≤ archiveGateMargin / 4 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      (∀ i : ArchiveIndex, gateRejectedDomain i e q ((e : ℝ) / 20) omega = ∅) ∧
      gateRejectedBankCost e q ((e : ℝ) / 20) omega = 0 ∧
      (∀ (N : ℝ) (pre : List ℕ), pre.length = 5 →
        ∀ i : ArchiveIndex,
        primeHistoryLogCoordinates N 5 pre ∈ (archiveRow i).originalBox →
        parentExcess rows4 licensed4 e q ((e : ℝ) / 20) omega N pre = 0) ∧
      |∑ i : ArchiveIndex,
        (indexedIntegral i e q ((e : ℝ) / 20) omega e - parentIntegral (archiveRow i))| <
        eta / 2 + canonicalHistoryBankCost q ((e : ℝ) / 20) omega := by
  obtain ⟨e, q, he, hemax, hem, hq, hstep, hrough, hempty, hzero, herr⟩ :=
    exists_full_archive_gate_paid_schedule eta omega heta homega hw
  exact ⟨e, q, he, hemax, hem, hq, hstep, hrough, hempty, hzero,
    fun N pre hlen i ht => archive_parentExcess_zero rows4 licensed4
      e q ((e : ℝ) / 20) omega N pre hlen i ht, herr⟩

end
end ImbalancedChen.P5HistoricalHistoryResidualAndSchedule
