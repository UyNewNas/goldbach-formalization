import ImbalancedChen.P5HistoricalActualReserve64Budget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Choose H's rational buffer below its genuine finite-bank continuity
radius and the actual143-block gate margin, then one complete aligned q.
The SAME e/q/chi=e/20/omega and licensed owners pay the complete original
indexedActualReserve64 and preserve Q's empty history. There is no
assumed reserve bound, no sum evaluation, and no re-created data bank.

The original density reserve is specialized only for this local analytic
loss. The distinct compiler reserve and the remainder of the full policy
are not supplied. The old Jensen/Taylor branch debt is a separate task.
-/
namespace ImbalancedChen.P5HistoricalActualReserve64Schedule
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthJointMeshSchedule
open P1OriginalFifthAdoptedOwnerBank P1HistoricalFifthIndexedOwnerArchive
open P1HistoricalFifthIndexedBankError P1HistoricalFifthTypedBaseGeometry
open P5HistoricalMask56FullSourceChildren P5HistoricalIndexedTrimGeometry
open P5HistoricalCanonicalFilterReserve P5HistoricalUniformExtraGatePayment
open P5HistoricalGatePaidReserveSchedule P1HistoricalFifthActualHistoryAdmission
open P5HistoricalActualReserve64Budget

/-- A positive rational buffer is chosen before q and before N. For
these actual witnesses BOTH the complete child-specific reserve and
the old-literal approximation error fit eta. These are two bounds,
not an assertion that their sum spends only eta. -/
theorem exists_full_actual_reserve64_paid_schedule
    (eta omega : ℝ) (heta : 0 < eta) (homega : 0 < omega) (hw : omega ≤ 1 / 800) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧
      e ≤ archiveGateMargin / 4 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      gatePaidEnvelope e < eta ∧
      (∀ i : ArchiveIndex,
        canonicalInvalidHistory (archiveRow i) q ((e : ℝ) / 20) omega = ∅) ∧
      canonicalHistoryBankCost q ((e : ℝ) / 20) omega = 0 ∧
      gateRejectedBankCost e q ((e : ℝ) / 20) omega = 0 ∧
      (∀ i : ArchiveIndex,
        licensedOwners i e q ((e : ℝ) / 20) omega =
          adoptedOwners (archiveRow i) e q ((e : ℝ) / 20) omega) ∧
      (∑ i : ArchiveIndex, indexedActualReserve64 i e q ((e : ℝ) / 20) omega) < eta ∧
      |∑ i : ArchiveIndex,
        (indexedIntegral i e q ((e : ℝ) / 20) omega e - parentIntegral (archiveRow i))| < eta := by
  obtain ⟨e, he, hemax, hem, hbudget⟩ := exists_gate_paid_buffer eta heta
  have heQ : (0 : ℚ) ≤ e := by exact_mod_cast he.le
  have hemaxQ : e ≤ (3 / 51200 : ℚ) := by exact_mod_cast hemax.le
  obtain ⟨q, hq, hsmall, _hcover⟩ :=
    exists_small_step_complete_cover (min ((e : ℝ) / 10) omega)
      (lt_min (by positivity) homega)
  have hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 := by
    have hm := min_le_left ((e : ℝ) / 10) omega
    linarith
  have hrough : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 := by
    have hm := min_le_right ((e : ℝ) / 10) omega
    linarith
  have hhistory := archive_canonicalHistoryBankCost_zero e heQ hemaxQ q hq omega
  have hreserve := full_actual_reserve64_le_gatePaidEnvelope
    e heQ hemaxQ hem q hq omega homega.le hw hstep hrough
  have hliteral := full_indexed_error_le_gate_paid_envelope_history
    e heQ hem hemaxQ q hq omega homega.le hw hstep hrough
  rw [hhistory, add_zero] at hliteral
  exact ⟨e, q, he, hemax, hem, hq, hstep, hrough, hbudget,
    (fun i => archive_canonicalHistory_empty i e heQ hemaxQ q hq omega), hhistory,
    gateRejectedBankCost_zero e heQ hem q ((e : ℝ) / 20) omega hstep,
    licensedOwners_eq_adoptedOwners e heQ hem q ((e : ℝ) / 20) omega hstep,
    hreserve.trans_lt hbudget, hliteral.trans_lt hbudget⟩

open P4AAll22OriginalKLedger20261024zSourceOnly

/-- The original u_d is used with its literal normalization. This pays
only the fifth complete-child analytic loss. No compiler expenditure is
identified with it, and the previously spent third-density u_d/4 remains
in the ledger. Arbitrary eta above permits a smaller joint allocation. -/
theorem exists_original_density_reserve64_payment
    (omega : ℝ) (homega : 0 < omega) (hw : omega ≤ 1 / 800) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧
      e ≤ archiveGateMargin / 4 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      canonicalHistoryBankCost q ((e : ℝ) / 20) omega = 0 ∧
      gateRejectedBankCost e q ((e : ℝ) / 20) omega = 0 ∧
      (∑ i : ArchiveIndex, indexedActualReserve64 i e q ((e : ℝ) / 20) omega) <
        densityReserve / 8 := by
  obtain ⟨e, q, he, hemax, hem, hq, hstep, hrough, _hbudget, _hempty,
      hhistory, hgate, _howners, hreserve, _hliteral⟩ :=
    exists_full_actual_reserve64_paid_schedule (densityReserve / 8) omega
      (div_pos densityReserve_pos (by norm_num)) homega hw
  exact ⟨e, q, he, hemax, hem, hq, hstep, hrough, hhistory, hgate, hreserve⟩

/-- Keep the original exact subdivision endpoint and safe10051/10^6
rounding. The same schedule lies below both its strict margin and u_d/8.
The old-branch defect and the stored endpoint sum are separate suppliers.
The closed rational positivity body below remains UNEVALUATED. -/
theorem exists_original_safe_fifth_margin_payment
    (omega : ℝ) (homega : 0 < omega) (hw : omega ≤ 1 / 800) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧
      e ≤ archiveGateMargin / 4 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      canonicalHistoryBankCost q ((e : ℝ) / 20) omega = 0 ∧
      gateRejectedBankCost e q ((e : ℝ) / 20) omega = 0 ∧
      (∑ i : ArchiveIndex, indexedActualReserve64 i e q ((e : ℝ) / 20) omega) <
        densityReserve / 8 ∧
      (∑ i : ArchiveIndex, indexedActualReserve64 i e q ((e : ℝ) / 20) omega) <
        (3037921066812732539869 / 302231454903657293676544 : ℝ) -
          10051 / 1000000 := by
  have hmargin : (0 : ℝ) <
      (3037921066812732539869 / 302231454903657293676544 : ℝ) -
        10051 / 1000000 := by
    norm_num
  obtain ⟨e, q, he, hemax, hem, hq, hstep, hrough, _hbudget, _hempty,
      hhistory, hgate, _howners, hreserve, _hliteral⟩ :=
    exists_full_actual_reserve64_paid_schedule
      (min (densityReserve / 8)
        ((3037921066812732539869 / 302231454903657293676544 : ℝ) -
          10051 / 1000000)) omega
      (lt_min (div_pos densityReserve_pos (by norm_num)) hmargin) homega hw
  exact ⟨e, q, he, hemax, hem, hq, hstep, hrough, hhistory, hgate,
    hreserve.trans_le (min_le_left _ _), hreserve.trans_le (min_le_right _ _)⟩

end
end ImbalancedChen.P5HistoricalActualReserve64Schedule
