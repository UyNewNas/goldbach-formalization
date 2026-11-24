import ImbalancedChen.P5HistoricalUniformExtraGatePayment
import ImbalancedChen.P1HistoricalFifthFullBankStripSchedule
import ImbalancedChen.P4AAll22OriginalKLedger

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Choose ONE positive rational buffer below the actual archive gate margin
and the actual finite-bank continuity radius, THEN choose ONE common mesh.
The extra gate cost is zero; the existing three proper owner-filter walls
cost only 64*sum(M_i)*e. The actual history-invalid region remains explicit.
The final specialization uses the original two reserves, but pays only
this geometric subproblem, not the full physical compiler/density ledger.
-/
namespace ImbalancedChen.P5HistoricalGatePaidReserveSchedule
noncomputable section
open Set
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthJointMeshSchedule
open P1OriginalFifthLiteralKernelModulus P1OriginalFifthQuantitativeGateRefinement
open P1OriginalFifthAdoptedOwnerBank P1HistoricalFifthIndexedOwnerArchive
open P1HistoricalFifthIndexedBankError P1HistoricalFifthTypedBaseGeometry
open P1HistoricalFifthFullBankStripSchedule P5HistoricalIndexedTrimGeometry
open P5HistoricalRejectedCoreReserve P5HistoricalCanonicalFilterReserve
open P5HistoricalUniformExtraGatePayment

/-- Bind the payment to the independently defined common policy input.
The original full source indices and their original selected masks are
preserved. This is a bank identity, not a new/old density equality. -/
theorem common_rows5_eq_full_adopted_bank
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (e : ℚ) (he : 0 ≤ e) (hecap : e ≤ archiveGateMargin / 4)
    (q : ℕ) (chi omega : ℝ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20) :
    (P1HistoricalFifthCommonPolicyInputs.sourceData rows4 licensed4 e q chi omega).rows5 =
      Finset.univ.biUnion (fun i : ArchiveIndex =>
        (adoptedOwners (archiveRow i) e q chi omega).image (sourceOwnerRow i q)) := by
  rw [common_rows5_eq_full_index_bank]
  simp_rw [licensedOwners_eq_adoptedOwners e he hecap q chi omega hstep]

/-- Only the already-proved canonical-filter strip payment is added to
the actual literal kernel modulus. The former 352*M*e extra-gate term is
absent because the actual extra-gate domain has been proved empty. -/
def gatePaidEnvelope (e : ℝ) : ℝ :=
  bankEnvelope (Finset.univ : Finset ArchiveIndex)
      (fun i => rowModulus (archiveRow i)) (fun i => rowMassBound (archiveRow i)) e +
    64 * sourceMassSum Finset.univ * e

theorem gatePaidEnvelope_continuousAt_zero : ContinuousAt gatePaidEnvelope 0 := by
  have hc := bankEnvelope_continuousAt_zero (Finset.univ : Finset ArchiveIndex)
    (fun i => rowModulus (archiveRow i)) (fun i => rowMassBound (archiveRow i))
    (fun i _ => (rowModulus_continuous (archiveRow i)).continuousAt)
  exact hc.add (by fun_prop : ContinuousAt (fun e : ℝ => 64 * sourceMassSum Finset.univ * e) 0)

theorem gatePaidEnvelope_zero : gatePaidEnvelope 0 = 0 := by
  unfold gatePaidEnvelope
  rw [bankEnvelope_zero (Finset.univ : Finset ArchiveIndex)
    (fun i => rowModulus (archiveRow i)) (fun i => rowMassBound (archiveRow i))
    (fun i _ => rowModulus_zero (archiveRow i))]
  simp only [mul_zero, add_zero]

/-- The strict source margin and analytic radius are intersected before
the rational choice; refining q later never changes either fixed bank. -/
theorem exists_gate_paid_buffer (eta : ℝ) (heta : 0 < eta) :
    ∃ e : ℚ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧
      e ≤ archiveGateMargin / 4 ∧ gatePaidEnvelope e < eta := by
  obtain ⟨delta, hd, hnear⟩ :=
    Metric.continuousAt_iff.mp gatePaidEnvelope_continuousAt_zero eta heta
  have hm : (0 : ℝ) < (archiveGateMargin : ℝ) / 4 := by
    have hp : (0 : ℝ) < (archiveGateMargin : ℝ) := by exact_mod_cast archiveGateMargin_pos
    positivity
  have hr : (0 : ℝ) < min (3 / 51200 : ℝ) (min delta ((archiveGateMargin : ℝ) / 4)) :=
    lt_min (by norm_num) (lt_min hd hm)
  obtain ⟨e, he, her⟩ := exists_rat_btwn hr
  have hecap : (e : ℝ) < 3 / 51200 := her.trans_le (min_le_left _ _)
  have heinner : (e : ℝ) < min delta ((archiveGateMargin : ℝ) / 4) :=
    her.trans_le (min_le_right _ _)
  have hem : e ≤ archiveGateMargin / 4 := by
    have hh : (e : ℝ) ≤ (archiveGateMargin : ℝ) / 4 :=
      (heinner.trans_le (min_le_right _ _)).le
    exact_mod_cast hh
  have hdist : dist (e : ℝ) 0 < delta := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos he] using
      heinner.trans_le (min_le_left _ _)
  have hbudget := hnear hdist
  rw [Real.dist_eq, gatePaidEnvelope_zero, sub_zero] at hbudget
  exact ⟨e, he, hecap, hem, (abs_lt.mp hbudget).2⟩

theorem full_indexed_error_le_gate_paid_envelope_history
    (e : ℚ) (he : 0 ≤ e) (hecap : e ≤ archiveGateMargin / 4)
    (hemax : e ≤ 3 / 51200) (q : ℕ) (hq : 0 < q)
    (omega : ℝ) (hw0 : 0 ≤ omega) (hw : omega ≤ 1 / 800)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20)
    (hstepOmega : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2) :
    |∑ i : ArchiveIndex,
      (indexedIntegral i e q ((e : ℝ) / 20) omega e - parentIntegral (archiveRow i))| ≤
        gatePaidEnvelope e + canonicalHistoryBankCost q ((e : ℝ) / 20) omega := by
  have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have herr := full_indexed_error_le_actual_envelope_trim q hq e he hemax
    ((e : ℝ) / 20) omega (by linarith) hstep
  rw [licensedTrimCost_eq_history_add_filter e he hecap q ((e : ℝ) / 20) omega hstep] at herr
  have hh : (meshStepQ (refinedMesh q) : ℝ) ≤ 1 / 800 := by
    rw [cast_meshStepQ]
    linarith
  have hf := canonicalFilterBankCost_le_linear_buffer e he q ((e : ℝ) / 20) omega
    hw0 hw hh hstep hstep
  rw [licensedIndices_eq_univ] at hf
  unfold gatePaidEnvelope
  linarith

/-- Actual full-source reserve payment with the genuine unchanged
history remainder. Every one of the 292633 source indices has empty
extra-gate rejection on this single common schedule. -/
theorem exists_full_archive_gate_paid_schedule
    (eta omega : ℝ) (heta : 0 < eta) (homega : 0 < omega) (hw : omega ≤ 1 / 800) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧
      e ≤ archiveGateMargin / 4 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      (∀ i : ArchiveIndex, gateRejectedDomain i e q ((e : ℝ) / 20) omega = ∅) ∧
      gateRejectedBankCost e q ((e : ℝ) / 20) omega = 0 ∧
      |∑ i : ArchiveIndex,
        (indexedIntegral i e q ((e : ℝ) / 20) omega e - parentIntegral (archiveRow i))| <
          eta / 2 + canonicalHistoryBankCost q ((e : ℝ) / 20) omega := by
  obtain ⟨e, he, hemax, hem, hbudget⟩ := exists_gate_paid_buffer (eta / 2) (by positivity)
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
  have herr := full_indexed_error_le_gate_paid_envelope_history e heQ.le hem hemaxQ
    q hq omega homega.le hw hstep hstepOmega
  exact ⟨e, q, he, hemax, hem, hq, hstep, hstepOmega,
    gateRejectedDomain_empty e heQ.le hem q ((e : ℝ) / 20) omega hstep,
    gateRejectedBankCost_zero e heQ.le hem q ((e : ℝ) / 20) omega hstep,
    by linarith⟩

open P4AAll22OriginalKLedger20261024zSourceOnly

/-- Original reserve constants, with different density and compilation
slots. The extra-gate subpayment is zero in either slot. The displayed
old-literal approximation spends less than u_d/8 PLUS its unpaid history
region. This is deliberately not a full density or compiler theorem. -/
theorem exists_original_reserve_extra_gate_payment
    (omega : ℝ) (homega : 0 < omega) (hw : omega ≤ 1 / 800) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      (∀ i : ArchiveIndex, gateRejectedDomain i e q ((e : ℝ) / 20) omega = ∅) ∧
      gateRejectedBankCost e q ((e : ℝ) / 20) omega < compilerReserve / 8 ∧
      |∑ i : ArchiveIndex,
        (indexedIntegral i e q ((e : ℝ) / 20) omega e - parentIntegral (archiveRow i))| <
          densityReserve / 8 + canonicalHistoryBankCost q ((e : ℝ) / 20) omega := by
  obtain ⟨e, q, he, hemax, _hem, hq, hstep, hrough, hempty, hzero, herr⟩ :=
    exists_full_archive_gate_paid_schedule (densityReserve / 4) omega
      (div_pos densityReserve_pos (by norm_num)) homega hw
  refine ⟨e, q, he, hemax, hq, hstep, hrough, hempty, ?_, ?_⟩
  · rw [hzero]
    exact div_pos compilerReserve_pos (by norm_num)
  · convert herr using 1 <;> ring

end
end ImbalancedChen.P5HistoricalGatePaidReserveSchedule
