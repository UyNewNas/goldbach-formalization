import ImbalancedChen.P5OriginalHistoryCorePayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original integer third admission gives a strict 133/2048000 margin in
the ACTUAL currentExponent on J's existing e/20 schedule. The same
decoded owner supplies Q3 and the selected positional Q4 consumer.

Unconditionally on the full original archive, the actual history cost
and old-literal integral are bounded by the explicit source-core payment
plus J's proved transport term. No smallness of that fixed source sum is
assumed or concluded. I's parentExcess=0 is reused at the SAME witnesses.
-/
namespace ImbalancedChen.P5OriginalHistorySourceConsumers
noncomputable section
open Set
open scoped Classical BigOperators
open VariableEnvelope HistoricalThirdCoarse HistoricalThirdCoarse.P1OriginalCoarseFifth
open P2OriginalFourthCapProducerInterface P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthAdoptedOwnerBank P1OriginalFifthLiteralKernelModulus
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthIndexedBankError
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthCommonAncestorExcess
open P5CanonicalOwnerFilterStrips P5HistoricalCanonicalFilterReserve
open P5HistoricalIndexedTrimGeometry P5HistoricalUniformExtraGatePayment
open P5HistoricalGatePaidReserveSchedule P5HistoricalHistoryResidualAndSchedule
open P5HistoricalBelowMuCommonParent P5HistoricalActualThirdHistoryTransport
open P5HistoricalThirdTransportStripPayment P5HistoricalHistoryTransportConsumers
open P1CorrectedFifthDensityDictionary OriginalFifthInheritedParentGeometry20261026b
open P5OriginalHistoryGapCorner P5OriginalHistoryCorePayment

/-- One original integer unit is larger than the entire permitted J
rectangular transport loss. No new refinement or source-dependent mesh. -/
theorem archive_current_third_margin_of_producer_gap
    (i : ArchiveIndex) (hp : 0 < producerThirdGap400 (archiveRow i))
    (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3/51200) (q : ℕ) (omega : ℝ)
    (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19/96) (refinedMesh q) r.cell) :
    thirdCube t + (133/2048000 : ℝ) <
      currentExponent 0 ((e : ℝ)/20) (refinedMesh q) omega r.cell t := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hemaxR : (e : ℝ) ≤ 3/51200 := by exact_mod_cast hemax
  have hraw := (decodeFifthRows_source_geometry
    (archiveRow i) (refinedMesh q) r hr t ht).2.2.2
  have hgap := producerThirdGap400_uniform_margin
    (archiveRow i) (archiveRow_grid i) hp t hraw
  have htransport := archive_current_third_lower i q ((e : ℝ)/20) omega
    (by positivity) (by linarith) r hr t ht
  linarith

/-- Both original first cubes, strict order, firstStop, and the genuine
third cube hold for THIS decoded owner. Fifth support/cube and selection
conditions are separate and are not inferred from these history tests. -/
theorem archive_jointRegion_of_producer_admission
    (i : ArchiveIndex) (ho : rawKeyOrdered (archiveRow i))
    (hp : 0 < producerThirdGap400 (archiveRow i))
    (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3/51200) (q : ℕ) (omega : ℝ)
    (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19/96) (refinedMesh q) r.cell) :
    t ∈ jointRegion 0 ((e : ℝ)/20) (refinedMesh q) omega r.cell := by
  have hraw := (decodeFifthRows_source_geometry
    (archiveRow i) (refinedMesh q) r hr t ht).2.2.2
  have horder := rawKeyOrdered_strictAnti (archiveRow i)
    (by rw [archiveRow_grid]; norm_num) ho t hraw
  obtain ⟨hstop, hroot⟩ := decoded_zero_first_history i q r hr t ht
  have hfirst := archive_current_first_cube_margin i q ((e : ℝ)/20) omega r hr t ht
  have hthird := archive_current_third_margin_of_producer_gap
    i hp e he hemax q omega r hr t ht
  apply (mem_jointRegion 0 ((e : ℝ)/20) (refinedMesh q) omega r.cell t).mpr
  refine ⟨hstop, horder, hroot, ?_, ?_⟩
  · linarith
  · dsimp only [thirdCube] at hthird
    linarith

theorem canonicalInvalidHistory_empty_of_producer_admission
    (i : ArchiveIndex) (ho : rawKeyOrdered (archiveRow i))
    (hp : 0 < producerThirdGap400 (archiveRow i))
    (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3/51200)
    (q : ℕ) (hq : 0 < q) (omega : ℝ) :
    canonicalInvalidHistory (archiveRow i) q ((e : ℝ)/20) omega = ∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  intro t ht
  have hcover := refined_originalBox_inter_ambient_eq_decode_union q hq
    (archiveRow i) (archiveRow_grid i) (archiveRow_mask_nonnegative i)
  have htcover : t ∈ ⋃ r ∈ decodeFifthRows (archiveRow i) (refinedMesh q),
      logPrimeMeshCell 0 (19/96) (refinedMesh q) r.cell := by
    rw [← hcover]
    exact ht.1
  obtain ⟨r, hr, htr⟩ := mem_iUnion₂.mp htcover
  have hjoint := archive_jointRegion_of_producer_admission
    i ho hp e he hemax q omega r hr t htr
  exact ht.2 ((mem_unfiltered_iff_same_decoded_history
    i q ((e : ℝ)/20) omega r hr t htr).mpr hjoint)

theorem archive_originalQ3_third_cube_margin
    (i : ArchiveIndex) (hp : 0 < producerThirdGap400 (archiveRow i))
    (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3/51200) (q : ℕ) (omega : ℝ)
    (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hpos : ∀ k, 0 < p k)
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell 0 (19/96) (refinedMesh q) r.cell) :
    (N : ℝ) ^ (thirdCube (actualPrimeTupleLog N p) + (133/2048000 : ℝ)) ≤
      originalQ3 0 ((e : ℝ)/20) (refinedMesh q) omega N (thirdHistory p) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  change (N : ℝ) ^ (thirdCube (actualPrimeTupleLog N p) + (133/2048000 : ℝ)) ≤
    rawLevel 0 ((e : ℝ)/20) (refinedMesh q) omega N (thirdHistory p)
  rw [rawLevel_on_fifth_cell 0 ((e : ℝ)/20) (refinedMesh q) omega N hN p hpos r.cell ht]
  exact (Real.rpow_le_rpow_left_iff hNr).mpr
    (archive_current_third_margin_of_producer_gap
      i hp e he hemax q omega r hr _ ht).le

/-- The original Q4 maximum inherits this same Q3 seed at the SAME
selected positional owner. No entire fourth bank licence is presumed. -/
theorem archive_dynamic_parent_third_cube_margin
    (records4 : List FourthWireRow) (licensed4 : ProducerRow → Prop)
    (i : ArchiveIndex) (hp : 0 < producerThirdGap400 (archiveRow i))
    (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3/51200) (q : ℕ) (omega : ℝ)
    (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (J5 : Finset (Fin 5 → Fin (refinedMesh q + 1)))
    (hj : r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells
      0 ((e : ℝ)/20) (refinedMesh q) omega J5)
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19/96) (refinedMesh q) r.cell)
    (k : OriginalFullFourthPriorityOwnership20261026a.BankPosition records4)
    (hk : parentOwner records4 0 (refinedMesh q) r.cell licensed4 t = k) :
    thirdCube t + (133/2048000 : ℝ) <
      parentValue records4 0 (refinedMesh q) r.cell k t := by
  have hseed := originalVariableFourthProfile_inherits_rawQ3
    0 ((e : ℝ)/20) omega (refinedMesh q) r.cell
    (P1OriginalFullTableActualProducerAdapter.fourthFamily records4) licensed4 t
  have hparent := actualOld4_eq_parentValue records4 0 ((e : ℝ)/20)
    (refinedMesh q) omega J5 r.cell hj licensed4 t ht k hk
  exact ((archive_current_third_margin_of_producer_gap
    i hp e he hemax q omega r hr t ht).trans_le hseed).trans_eq hparent

/-- Full original source, no admission/cost premise and no dropped
positive-mass core. Its fixed payment is now explicit in the raw keys. -/
theorem canonicalHistoryBankCost_le_explicit_source_payment
    (q : ℕ) (hq : 0 < q) (chi omega : ℝ)
    (hchi : 0 ≤ chi) (hfine : 7*chi ≤ 3/256) :
    canonicalHistoryBankCost q chi omega ≤
      sourceCoreBankCost + 198 * sourceMassSum licensedIndices * chi := by
  exact (canonicalHistoryBankCost_le_ideal_add_transport q hq chi omega hchi hfine).trans
    (add_le_add_right idealHistoryBankCost_le_sourceCoreBankCost _)

/-- Preserve J's one e, one aligned q and I's already-paid parent debt.
The source-key sum is an explicit output term, never a smallness premise. -/
theorem exists_same_schedule_explicit_source_payment
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (eta omega : ℝ) (heta : 0 < eta) (homega : 0 < omega) (hw : omega ≤ 1/800) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3/51200 ∧
      e ≤ archiveGateMargin/4 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19/96) (refinedMesh q) ≤ (e : ℝ)/20 ∧
      logPrimeMeshStep 0 (19/96) (refinedMesh q) ≤ omega/2 ∧
      (∀ i : ArchiveIndex, gateRejectedDomain i e q ((e : ℝ)/20) omega = ∅) ∧
      gateRejectedBankCost e q ((e : ℝ)/20) omega = 0 ∧
      (∀ (N : ℝ) (pre : List ℕ), pre.length = 5 → ∀ i : ArchiveIndex,
        primeHistoryLogCoordinates N 5 pre ∈ (archiveRow i).originalBox →
        parentExcess rows4 licensed4 e q ((e : ℝ)/20) omega N pre = 0) ∧
      |∑ i : ArchiveIndex,
        (indexedIntegral i e q ((e : ℝ)/20) omega e - parentIntegral (archiveRow i))| <
          eta/2 + sourceCoreBankCost := by
  obtain ⟨e, q, he, hemax, hem, hq, hstep, hrough, hempty, hzero, herr⟩ :=
    exists_full_archive_history_transport_paid_schedule eta omega heta homega hw
  exact ⟨e, q, he, hemax, hem, hq, hstep, hrough, hempty, hzero,
    fun N pre hlen i ht => archive_parentExcess_zero rows4 licensed4
      e q ((e : ℝ)/20) omega N pre hlen i ht,
    herr.trans_le (add_le_add_left idealHistoryBankCost_le_sourceCoreBankCost _)⟩

open P4AAll22OriginalKLedger20261024zSourceOnly

theorem exists_original_reserve_explicit_source_payment
    (omega : ℝ) (homega : 0 < omega) (hw : omega ≤ 1/800) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3/51200 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19/96) (refinedMesh q) ≤ (e : ℝ)/20 ∧
      logPrimeMeshStep 0 (19/96) (refinedMesh q) ≤ omega/2 ∧
      (∀ i : ArchiveIndex, gateRejectedDomain i e q ((e : ℝ)/20) omega = ∅) ∧
      gateRejectedBankCost e q ((e : ℝ)/20) omega < compilerReserve/8 ∧
      |∑ i : ArchiveIndex,
        (indexedIntegral i e q ((e : ℝ)/20) omega e - parentIntegral (archiveRow i))| <
          densityReserve/8 + sourceCoreBankCost := by
  obtain ⟨e, q, he, hemax, hq, hstep, hrough, hempty, hgate, herr⟩ :=
    exists_original_reserve_history_transport_payment omega homega hw
  exact ⟨e, q, he, hemax, hq, hstep, hrough, hempty, hgate,
    herr.trans_le (add_le_add_left idealHistoryBankCost_le_sourceCoreBankCost _)⟩

end
end ImbalancedChen.P5OriginalHistorySourceConsumers
