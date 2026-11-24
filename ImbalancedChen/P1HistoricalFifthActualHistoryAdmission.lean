import ImbalancedChen.P1HistoricalFifthTypedHistoryAdmission
import ImbalancedChen.P5OriginalHistorySourceConsumers

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Instantiate the already proved K corner/current-Gamma deductions at the
actual 143-block source. The new finite admission bodies are UNEVALUATED
dependencies. No row geometry, desired history-cost bound, parent equality
or integral estimate is supplied by a caller.

The same e/q schedule is the existing H schedule. All original source
positions, masks, half-open owners and dynamic ancestors are retained.
The final error concerns the existing old-literal indexed integral only;
it does not pay G's stored old Jensen/Taylor branch defect or identify
that literal kernel with an arbitrary changed common physical density.
-/
namespace ImbalancedChen.P1HistoricalFifthActualHistoryAdmission
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open HistoricalThirdCoarse HistoricalThirdCoarse.P1OriginalCoarseFifth
open P2OriginalFourthCapProducerInterface P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthAdoptedOwnerBank P1HistoricalFifthIndexedOwnerArchive
open P1HistoricalFifthIndexedBankError P1HistoricalFifthTypedBaseGeometry
open P1HistoricalFifthCommonAncestorExcess P1CorrectedFifthDensityDictionary
open P5CanonicalOwnerFilterStrips P5HistoricalCanonicalFilterReserve
open P5HistoricalIndexedTrimGeometry P5HistoricalUniformExtraGatePayment
open P5HistoricalGatePaidReserveSchedule P5HistoricalBelowMuCommonParent
open P5HistoricalThirdTransportStripPayment
open P5OriginalHistoryGapCorner P5OriginalHistoryCorePayment
open OriginalFifthInheritedParentGeometry20261026b
open P1HistoricalFifthTypedHistoryAdmission

/-- The real current Gamma dispatch, with its activation/fallback cases,
is used at the same decoded owner. There is no selected-status premise. -/
theorem archive_current_third_margin
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (q : ℕ) (omega : ℝ) (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell) :
    thirdCube t + (133 / 2048000 : ℝ) <
      currentExponent 0 ((e : ℝ) / 20) (refinedMesh q) omega r.cell t :=
  P5OriginalHistorySourceConsumers.archive_current_third_margin_of_producer_gap
    i (archiveRow_original_third_gap i) e he hemax q omega r hr t ht

theorem archive_jointRegion
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (q : ℕ) (omega : ℝ) (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell) :
    t ∈ jointRegion 0 ((e : ℝ) / 20) (refinedMesh q) omega r.cell :=
  P5OriginalHistorySourceConsumers.archive_jointRegion_of_producer_admission
    i (archiveRow_original_order i) (archiveRow_original_third_gap i)
    e he hemax q omega r hr t ht

/-- All source positions, not a licensed history subfamily. The only
restriction on q is the original positive aligned-refinement index. -/
theorem archive_canonicalHistory_empty
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (q : ℕ) (hq : 0 < q) (omega : ℝ) :
    canonicalInvalidHistory (archiveRow i) q ((e : ℝ) / 20) omega = ∅ :=
  P5OriginalHistorySourceConsumers.canonicalInvalidHistory_empty_of_producer_admission
    i (archiveRow_original_order i) (archiveRow_original_third_gap i)
    e he hemax q hq omega

theorem archive_canonicalHistoryCost_zero
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (q : ℕ) (hq : 0 < q) (omega : ℝ) :
    canonicalHistoryCost i q ((e : ℝ) / 20) omega = 0 := by
  simp only [canonicalHistoryCost,
    archive_canonicalHistory_empty i e he hemax q hq omega,
    measure_empty, ENNReal.toReal_zero, mul_zero]

theorem archive_canonicalHistoryBankCost_zero
    (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (q : ℕ) (hq : 0 < q) (omega : ℝ) :
    canonicalHistoryBankCost q ((e : ℝ) / 20) omega = 0 := by
  unfold canonicalHistoryBankCost
  exact Finset.sum_eq_zero (fun i _hi =>
    archive_canonicalHistoryCost_zero i e he hemax q hq omega)

/-- The fixed K source-core charge also vanishes at the same actual
indices. No quantitative core estimate is assumed. -/
theorem archive_sourceCoreCost_zero (i : ArchiveIndex) : sourceCoreCost i = 0 :=
  sourceCoreCost_zero_of_producer_admission i
    (archiveRow_original_order i) (archiveRow_original_third_gap i)

theorem archive_sourceCoreBankCost_zero : sourceCoreBankCost = 0 := by
  unfold sourceCoreBankCost
  exact Finset.sum_eq_zero (fun i _hi => archive_sourceCoreCost_zero i)

/-- Q3 is the original rawLevel on the actual prime ancestor, including
the original activation and initial firstStop conventions. -/
theorem archive_originalQ3_margin
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (q : ℕ) (omega : ℝ) (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hpos : ∀ k, 0 < p k)
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell) :
    (N : ℝ) ^ (thirdCube (actualPrimeTupleLog N p) + (133 / 2048000 : ℝ)) ≤
      originalQ3 0 ((e : ℝ) / 20) (refinedMesh q) omega N (thirdHistory p) :=
  P5OriginalHistorySourceConsumers.archive_originalQ3_third_cube_margin
    i (archiveRow_original_third_gap i) e he hemax q omega r hr N hN p hpos ht

/-- The owner in the conclusion IS the independently defined dynamic
parentOwner. Its equality and selected-row licence are not input fields.
The actual original fourth records/licences remain arbitrary parameters;
this theorem does not instantiate the complete fourth archive. -/
theorem archive_zero_buffer_dynamic_parent_margin
    (records4 : List FourthWireRow) (licensed4 : ProducerRow → Prop)
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (q : ℕ) (omega : ℝ) (j : Label5 (refinedMesh q))
    (hj : j ∈ licensedOwners i e q ((e : ℝ) / 20) omega)
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j) :
    thirdCube t + (133 / 2048000 : ℝ) <
      parentValue records4 0 (refinedMesh q) j
        (parentOwner records4 0 (refinedMesh q) j licensed4 t) t := by
  exact P5OriginalHistorySourceConsumers.archive_dynamic_parent_third_cube_margin
    records4 licensed4 i (archiveRow_original_third_gap i) e he hemax q omega
    (sourceOwnerRow i q j)
    (licensedOwner_decoded i e q ((e : ℝ) / 20) omega j hj)
    (licensedOwners i e q ((e : ℝ) / 20) omega)
    (licensedOwner_selected_zero i e q ((e : ℝ) / 20) omega j hj)
    t ht (parentOwner records4 0 (refinedMesh q) j licensed4 t) rfl

/-- One original aligned q simultaneously covers every full raw box,
preserves its selected mask, passes both endpoint gates, and removes the
actual history cost. Existing I supplies the actual common-parent equality
at these same witnesses. H's literal integral error now has no unpaid
history term; the remaining floor/physical obligations are not hidden. -/
theorem exists_same_q_complete_history_paid
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (eta omega : ℝ) (heta : 0 < eta) (homega : 0 < omega) (hw : omega ≤ 1 / 800) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧
      e ≤ archiveGateMargin / 4 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      (∀ i : ArchiveIndex,
        (archiveRow i).originalBox ∩
            logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) =
          ⋃ r ∈ decodeFifthRows (archiveRow i) (refinedMesh q),
            logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell) ∧
      (∀ (i : ArchiveIndex) (r : FifthRow (refinedMesh q)),
        r ∈ decodeFifthRows (archiveRow i) (refinedMesh q) →
          r.selected = maskSlots 5 (archiveRow i).mask.toNat ∧
          gateCheck 0 (refinedMesh q) r = true ∧ gateCheck e (refinedMesh q) r = true) ∧
      (∀ i : ArchiveIndex,
        licensedOwners i e q ((e : ℝ) / 20) omega =
          adoptedOwners (archiveRow i) e q ((e : ℝ) / 20) omega) ∧
      (∀ i : ArchiveIndex,
        canonicalInvalidHistory (archiveRow i) q ((e : ℝ) / 20) omega = ∅) ∧
      canonicalHistoryBankCost q ((e : ℝ) / 20) omega = 0 ∧
      (∀ (N : ℝ) (pre : List ℕ), pre.length = 5 → ∀ i : ArchiveIndex,
        primeHistoryLogCoordinates N 5 pre ∈ (archiveRow i).originalBox →
        parentExcess rows4 licensed4 e q ((e : ℝ) / 20) omega N pre = 0) ∧
      |∑ i : ArchiveIndex,
        (indexedIntegral i e q ((e : ℝ) / 20) omega e - parentIntegral (archiveRow i))| <
          eta / 2 := by
  obtain ⟨e, q, he, hemax, hem, hq, hstep, hrough, _hempty, _hzero, herr⟩ :=
    exists_full_archive_gate_paid_schedule eta omega heta homega hw
  have heQ : (0 : ℚ) ≤ e := by exact_mod_cast he.le
  have hemaxQ : e ≤ (3 / 51200 : ℚ) := by exact_mod_cast hemax.le
  have hhistory := archive_canonicalHistoryBankCost_zero e heQ hemaxQ q hq omega
  rw [hhistory, add_zero] at herr
  refine ⟨e, q, he, hemax, hem, hq, hstep, hrough, ?_, ?_, ?_, ?_, hhistory, ?_, herr⟩
  · intro i
    exact refined_originalBox_inter_ambient_eq_decode_union q hq (archiveRow i)
      (archiveRow_grid i) (archiveRow_mask_nonnegative i)
  · intro i r hr
    exact ⟨decodeFifthRows_selected_eq (archiveRow i) (refinedMesh q) r hr,
      archive_all_decoded_gates_on_schedule e 0 heQ hem q hstep i r hr,
      archive_all_decoded_gates_on_schedule e e le_rfl hem q hstep i r hr⟩
  · exact licensedOwners_eq_adoptedOwners e heQ hem q ((e : ℝ) / 20) omega hstep
  · exact fun i => archive_canonicalHistory_empty i e heQ hemaxQ q hq omega
  · exact fun N pre hlen i ht =>
      archive_parentExcess_zero rows4 licensed4 e q ((e : ℝ) / 20) omega N pre hlen i ht

end
end ImbalancedChen.P1HistoricalFifthActualHistoryAdmission
