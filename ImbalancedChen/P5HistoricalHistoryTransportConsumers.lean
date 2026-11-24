import ImbalancedChen.P5HistoricalThirdTransportStripPayment
import ImbalancedChen.OriginalFifthInheritedParentGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
One common original buffer/mesh pays the newly proved coarse-history
transport, the existing support-gate payment and the literal kernel error.
The exact original ideal source failure remains independent of that mesh.
Actual raw-Q3 and positional dynamic-Q4 consumers are retained.
-/
namespace ImbalancedChen.P5HistoricalHistoryTransportConsumers
noncomputable section
open Set
open scoped Classical BigOperators
open VariableEnvelope HistoricalThirdCoarse HistoricalThirdCoarse.P1OriginalCoarseFifth
open P2OriginalFourthCapProducerInterface P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthAdoptedOwnerBank P1HistoricalFifthIndexedOwnerArchive
open P1HistoricalFifthIndexedBankError P1HistoricalFifthTypedBaseGeometry
open P1OriginalFifthJointMeshSchedule P5HistoricalIndexedTrimGeometry
open P5HistoricalRejectedCoreReserve P5HistoricalCanonicalFilterReserve
open P5HistoricalUniformExtraGatePayment P5HistoricalGatePaidReserveSchedule
open P5HistoricalActualThirdHistoryTransport P5HistoricalThirdTransportStripPayment
open P1CorrectedFifthDensityDictionary
open OriginalFifthInheritedParentGeometry20261026b

/-- Raw-Q3 is the original level on this actual fifth owner, not a fresh
constant cap reconstructed from the stored Jensen statistics. -/
theorem archive_originalQ3_lower (i : ArchiveIndex) (q : ℕ)
    (chi omega : ℝ) (hchi : 0 ≤ chi) (hfine : 7 * chi ≤ 3 / 256)
    (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hp : ∀ k, 0 < p k)
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell) :
    (N : ℝ) ^ (six (actualPrimeTupleLog N p 0) (actualPrimeTupleLog N p 1)
      (actualPrimeTupleLog N p 2) - (9 / 2 : ℝ) * chi) ≤
        originalQ3 0 chi (refinedMesh q) omega N (thirdHistory p) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  change (N : ℝ) ^ (six (actualPrimeTupleLog N p 0) (actualPrimeTupleLog N p 1)
    (actualPrimeTupleLog N p 2) - (9 / 2 : ℝ) * chi) ≤
      rawLevel 0 chi (refinedMesh q) omega N (thirdHistory p)
  rw [rawLevel_on_fifth_cell 0 chi (refinedMesh q) omega N hN p hp r.cell ht]
  exact (Real.rpow_le_rpow_left_iff hNr).mpr
    (archive_current_third_lower i q chi omega hchi hfine r hr _ ht)

/-- Transfer to the SAME selected positional Q4 owner, including its
slot-zero raw-Q3 branch and every eligible original fourth record. No
historical parent identifier is inferred from a fifth saved statistic. -/
theorem archive_dynamic_parentValue_lower
    (records4 : List FourthWireRow) (licensed4 : ProducerRow → Prop)
    (i : ArchiveIndex) (q : ℕ) (chi omega : ℝ)
    (hchi : 0 ≤ chi) (hfine : 7 * chi ≤ 3 / 256)
    (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (J5 : Finset (Fin 5 → Fin (refinedMesh q + 1)))
    (hj : r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells
      0 chi (refinedMesh q) omega J5)
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell)
    (k : OriginalFullFourthPriorityOwnership20261026a.BankPosition records4)
    (hk : parentOwner records4 0 (refinedMesh q) r.cell licensed4 t = k) :
    six (t 0) (t 1) (t 2) - (9 / 2 : ℝ) * chi ≤
      parentValue records4 0 (refinedMesh q) r.cell k t := by
  have hseed := originalVariableFourthProfile_inherits_rawQ3
    0 chi omega (refinedMesh q) r.cell
    (P1OriginalFullTableActualProducerAdapter.fourthFamily records4) licensed4 t
  have hparent := actualOld4_eq_parentValue records4 0 chi (refinedMesh q) omega
    J5 r.cell hj licensed4 t ht k hk
  exact ((archive_current_third_lower i q chi omega hchi hfine r hr t ht).trans
    hseed).trans_eq hparent

/-- Only the newly proved 198 chi history transport is added. The
original ideal-order/third-gap cost is NOT part of this vanishing envelope. -/
def historyTransportEnvelope (e : ℝ) : ℝ :=
  gatePaidEnvelope e + 198 * sourceMassSum Finset.univ * (e / 20)

theorem historyTransportEnvelope_continuousAt_zero :
    ContinuousAt historyTransportEnvelope 0 := by
  exact gatePaidEnvelope_continuousAt_zero.add
    (by fun_prop : ContinuousAt
      (fun e : ℝ => 198 * sourceMassSum Finset.univ * (e / 20)) 0)

theorem historyTransportEnvelope_zero : historyTransportEnvelope 0 = 0 := by
  simp only [historyTransportEnvelope, gatePaidEnvelope_zero, zero_div, mul_zero, add_zero]

theorem exists_history_transport_buffer (eta : ℝ) (heta : 0 < eta) :
    ∃ e : ℚ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧
      e ≤ archiveGateMargin / 4 ∧ historyTransportEnvelope e < eta := by
  obtain ⟨delta, hd, hnear⟩ :=
    Metric.continuousAt_iff.mp historyTransportEnvelope_continuousAt_zero eta heta
  have hm : (0 : ℝ) < (archiveGateMargin : ℝ) / 4 := by
    have hp : (0 : ℝ) < (archiveGateMargin : ℝ) := by exact_mod_cast archiveGateMargin_pos
    positivity
  obtain ⟨e, he, her⟩ := exists_rat_btwn
    (lt_min (by norm_num : (0 : ℝ) < 3 / 51200) (lt_min hd hm))
  have hemax : (e : ℝ) < 3 / 51200 := her.trans_le (min_le_left _ _)
  have heinner : (e : ℝ) < min delta ((archiveGateMargin : ℝ) / 4) :=
    her.trans_le (min_le_right _ _)
  have hem : e ≤ archiveGateMargin / 4 := by
    exact_mod_cast (heinner.trans_le (min_le_right _ _)).le
  have hdist : dist (e : ℝ) 0 < delta := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos he] using
      heinner.trans_le (min_le_left _ _)
  have hbudget := hnear hdist
  rw [Real.dist_eq, historyTransportEnvelope_zero, sub_zero] at hbudget
  exact ⟨e, he, hemax, hem, (abs_lt.mp hbudget).2⟩

theorem full_indexed_error_le_history_transport_envelope
    (e : ℚ) (he : 0 ≤ e) (hecap : e ≤ archiveGateMargin / 4)
    (hemax : e ≤ 3 / 51200) (q : ℕ) (hq : 0 < q)
    (omega : ℝ) (hw0 : 0 ≤ omega) (hw : omega ≤ 1 / 800)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20)
    (hstepOmega : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2) :
    |∑ i : ArchiveIndex,
      (indexedIntegral i e q ((e : ℝ) / 20) omega e - parentIntegral (archiveRow i))| ≤
        historyTransportEnvelope e + idealHistoryBankCost := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hemaxR : (e : ℝ) ≤ 3 / 51200 := by exact_mod_cast hemax
  have herr := full_indexed_error_le_gate_paid_envelope_history e he hecap hemax
    q hq omega hw0 hw hstep hstepOmega
  have hhistory := canonicalHistoryBankCost_le_ideal_add_transport
    q hq ((e : ℝ) / 20) omega (by positivity) (by linarith)
  rw [licensedIndices_eq_univ] at hhistory
  unfold historyTransportEnvelope
  linarith

/-- ONE e and ONE q, chosen before N, pay actual coarse-history transport
and all previously paid gate/filter/kernel terms. The only history debt
left in this old-literal estimate is the independently fixed original
order/true-third-gap source core; its nullness is not a premise. -/
theorem exists_full_archive_history_transport_paid_schedule
    (eta omega : ℝ) (heta : 0 < eta) (homega : 0 < omega) (hw : omega ≤ 1 / 800) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧
      e ≤ archiveGateMargin / 4 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      (∀ i : ArchiveIndex, gateRejectedDomain i e q ((e : ℝ) / 20) omega = ∅) ∧
      gateRejectedBankCost e q ((e : ℝ) / 20) omega = 0 ∧
      |∑ i : ArchiveIndex,
        (indexedIntegral i e q ((e : ℝ) / 20) omega e - parentIntegral (archiveRow i))| <
          eta / 2 + idealHistoryBankCost := by
  obtain ⟨e, he, hemax, hem, hbudget⟩ :=
    exists_history_transport_buffer (eta / 2) (by positivity)
  have heQ : (0 : ℚ) < e := by exact_mod_cast he
  have hemaxQ : e ≤ (3 / 51200 : ℚ) := by exact_mod_cast hemax.le
  obtain ⟨q, hq, hsmall, _hcover⟩ :=
    exists_small_step_complete_cover (min ((e : ℝ) / 10) omega)
      (lt_min (by positivity) homega)
  have hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 := by
    have hm := min_le_left ((e : ℝ) / 10) omega
    linarith
  have hstepOmega : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 := by
    have hm := min_le_right ((e : ℝ) / 10) omega
    linarith
  have herr := full_indexed_error_le_history_transport_envelope e heQ.le hem
    hemaxQ q hq omega homega.le hw hstep hstepOmega
  exact ⟨e, q, he, hemax, hem, hq, hstep, hstepOmega,
    gateRejectedDomain_empty e heQ.le hem q ((e : ℝ) / 20) omega hstep,
    gateRejectedBankCost_zero e heQ.le hem q ((e : ℝ) / 20) omega hstep,
    by linarith⟩

open P4AAll22OriginalKLedger20261024zSourceOnly

/-- The original density/compilation reserve names remain distinct.
Only the identified ideal source admission is still charged as history. -/
theorem exists_original_reserve_history_transport_payment
    (omega : ℝ) (homega : 0 < omega) (hw : omega ≤ 1 / 800) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      (∀ i : ArchiveIndex, gateRejectedDomain i e q ((e : ℝ) / 20) omega = ∅) ∧
      gateRejectedBankCost e q ((e : ℝ) / 20) omega < compilerReserve / 8 ∧
      |∑ i : ArchiveIndex,
        (indexedIntegral i e q ((e : ℝ) / 20) omega e - parentIntegral (archiveRow i))| <
          densityReserve / 8 + idealHistoryBankCost := by
  obtain ⟨e, q, he, hemax, _hem, hq, hstep, hrough, hempty, hzero, herr⟩ :=
    exists_full_archive_history_transport_paid_schedule (densityReserve / 4) omega
      (div_pos densityReserve_pos (by norm_num)) homega hw
  refine ⟨e, q, he, hemax, hq, hstep, hrough, hempty, ?_, ?_⟩
  · rw [hzero]
    exact div_pos compilerReserve_pos (by norm_num)
  · convert herr using 1 <;> ring

end
end ImbalancedChen.P5HistoricalHistoryTransportConsumers
