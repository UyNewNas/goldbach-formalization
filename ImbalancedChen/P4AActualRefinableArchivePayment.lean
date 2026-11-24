import ImbalancedChen.P5HistoricalActualReserve64Schedule

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

The actual fifth-bank payment is made stable under the two choices needed
by the other density suppliers: a smaller positive rational buffer and a
later common aligned mesh. The radius is for H's actual gatePaidEnvelope;
the paid reserve is R05's complete indexedActualReserve64, not a caller's
error function. Original archive history and extra-gate costs remain zero.

This supplies compatible witnesses. It does not identify the full87
physical coefficient, bound the complete density ledger, or spend u_c.
-/

namespace ImbalancedChen.P4AActualRefinableArchivePayment

noncomputable section
open Set
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthJointMeshSchedule
open P1OriginalFifthAdoptedOwnerBank P1HistoricalFifthIndexedOwnerArchive
open P1HistoricalFifthIndexedBankError P1HistoricalFifthTypedBaseGeometry
open P5HistoricalMask56FullSourceChildren P5HistoricalIndexedTrimGeometry
open P5HistoricalCanonicalFilterReserve P5HistoricalUniformExtraGatePayment
open P5HistoricalGatePaidReserveSchedule P1HistoricalFifthActualHistoryAdmission
open P5HistoricalActualReserve64Budget

/-- One radius works for every later positive rational e. No monotonicity
of the bank modulus is required: continuity at its actual zero is used. -/
theorem exists_actual_gate_paid_radius (eta : ℝ) (heta : 0 < eta) :
    ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 3 / 51200 ∧
      ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < e0 →
        e ≤ archiveGateMargin / 4 ∧ gatePaidEnvelope e < eta := by
  obtain ⟨delta, hd, hnear⟩ :=
    Metric.continuousAt_iff.mp gatePaidEnvelope_continuousAt_zero eta heta
  have hm : (0 : ℝ) < (archiveGateMargin : ℝ) / 4 := by
    have hp : (0 : ℝ) < (archiveGateMargin : ℝ) := by
      exact_mod_cast archiveGateMargin_pos
    positivity
  let e0 : ℝ := min (3 / 51200) (min delta ((archiveGateMargin : ℝ) / 4))
  have he0 : 0 < e0 := lt_min (by norm_num) (lt_min hd hm)
  refine ⟨e0, he0, min_le_left _ _, ?_⟩
  intro e he hee
  have heinner : (e : ℝ) < min delta ((archiveGateMargin : ℝ) / 4) :=
    hee.trans_le (min_le_right _ _)
  have hem : e ≤ archiveGateMargin / 4 := by
    have hh : (e : ℝ) ≤ (archiveGateMargin : ℝ) / 4 :=
      (heinner.trans_le (min_le_right _ _)).le
    exact_mod_cast hh
  have hdist : dist (e : ℝ) 0 < delta := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos he] using
      heinner.trans_le (min_le_left _ _)
  have hbudget := hnear hdist
  rw [Real.dist_eq, gatePaidEnvelope_zero, sub_zero] at hbudget
  exact ⟨hem, (abs_lt.mp hbudget).2⟩

theorem actual_refined_mesh_mono {q q' : ℕ} (hqq : q ≤ q') :
    refinedMesh q ≤ refinedMesh q' := by
  unfold refinedMesh
  omega

theorem actual_refined_step_antitone {q q' : ℕ}
    (hq : 0 < q) (hqq : q ≤ q') :
    logPrimeMeshStep 0 (19 / 96) (refinedMesh q') ≤
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) := by
  have hq' : 0 < q' := hq.trans_le hqq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqR' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hqqR : (q : ℝ) ≤ q' := by exact_mod_cast hqq
  rw [refined_step q' hq', refined_step q hq]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2400 * (q' : ℝ))
    (by positivity : (0 : ℝ) < 2400 * (q : ℝ))).2
  nlinarith only [hqqR]

/-- Every later refinement retains the complete original grid400 cover
and can meet any previously fixed lower resolution. The original q is
chosen before N, and no owner-count factor enters any estimate. -/
theorem exists_actual_refinement_threshold
    (radius : ℝ) (hradius : 0 < radius) (qMin mMin : ℕ) :
    ∃ q0 : ℕ, 0 < q0 ∧ qMin ≤ q0 ∧
      ∀ q : ℕ, q0 ≤ q →
        mMin ≤ refinedMesh q ∧
        logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ radius := by
  obtain ⟨qs, hqs, hstep⟩ :=
    exists_refinement_step_le_half (2 * radius) (by positivity)
  let q0 : ℕ := max qs (max qMin (mMin + 1))
  have hqs0 : qs ≤ q0 := le_max_left _ _
  have hqMin : qMin ≤ q0 := (le_max_left _ _).trans (le_max_right _ _)
  have hm0 : mMin + 1 ≤ q0 := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨q0, hqs.trans_le hqs0, hqMin, ?_⟩
  intro q hq
  have hqm : mMin + 1 ≤ q := hm0.trans hq
  refine ⟨?_, ?_⟩
  · unfold refinedMesh
    omega
  · have hs := (actual_refined_step_antitone hqs (hqs0.trans hq)).trans hstep
    linarith only [hs]

/-- Actual all-index payment, uniform in every later admissible e and q.
The two final inequalities are distinct estimates. They are not added or
both debited to a single eta merely because they share the same envelope. -/
theorem exists_refinable_actual_archive_payment
    (eta : ℝ) (heta : 0 < eta) :
    ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 3 / 51200 ∧
      ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < e0 →
      ∀ omega : ℝ, 0 < omega → omega ≤ 1 / 800 →
      ∀ qMin mMin : ℕ,
      ∃ q0 : ℕ, 0 < q0 ∧ qMin ≤ q0 ∧
        e ≤ archiveGateMargin / 4 ∧ gatePaidEnvelope e < eta ∧
        ∀ q : ℕ, q0 ≤ q →
          mMin ≤ refinedMesh q ∧
          logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
          logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
          (∀ i : ArchiveIndex,
            canonicalInvalidHistory (archiveRow i) q ((e : ℝ) / 20) omega = ∅) ∧
          canonicalHistoryBankCost q ((e : ℝ) / 20) omega = 0 ∧
          gateRejectedBankCost e q ((e : ℝ) / 20) omega = 0 ∧
          (∀ i : ArchiveIndex,
            licensedOwners i e q ((e : ℝ) / 20) omega =
              adoptedOwners (archiveRow i) e q ((e : ℝ) / 20) omega) ∧
          (∑ i : ArchiveIndex,
            indexedActualReserve64 i e q ((e : ℝ) / 20) omega) < eta ∧
          |∑ i : ArchiveIndex,
            (indexedIntegral i e q ((e : ℝ) / 20) omega e -
              parentIntegral (archiveRow i))| < eta := by
  obtain ⟨e0, he0, he0max, hradius⟩ := exists_actual_gate_paid_radius eta heta
  refine ⟨e0, he0, he0max, ?_⟩
  intro e he hee omega homega hw qMin mMin
  obtain ⟨hem, hbudget⟩ := hradius e he hee
  have heQ : (0 : ℚ) ≤ e := by exact_mod_cast he.le
  have hemaxQ : e ≤ (3 / 51200 : ℚ) := by
    exact_mod_cast (hee.trans_le he0max).le
  obtain ⟨q0, hq0, hqMin, hthreshold⟩ :=
    exists_actual_refinement_threshold (min ((e : ℝ) / 20) (omega / 2))
      (lt_min (by positivity) (half_pos homega)) qMin mMin
  refine ⟨q0, hq0, hqMin, hem, hbudget, ?_⟩
  intro q hq
  have hqpos : 0 < q := hq0.trans_le hq
  obtain ⟨hm, hs⟩ := hthreshold q hq
  have hstep := hs.trans (min_le_left _ _)
  have hrough := hs.trans (min_le_right _ _)
  have hhistory := archive_canonicalHistoryBankCost_zero e heQ hemaxQ q hqpos omega
  have hreserve := full_actual_reserve64_le_gatePaidEnvelope
    e heQ hemaxQ hem q hqpos omega homega.le hw hstep hrough
  have hliteral := full_indexed_error_le_gate_paid_envelope_history
    e heQ hem hemaxQ q hqpos omega homega.le hw hstep hrough
  rw [hhistory, add_zero] at hliteral
  exact ⟨hm, hstep, hrough,
    (fun i => archive_canonicalHistory_empty i e heQ hemaxQ q hqpos omega),
    hhistory, gateRejectedBankCost_zero e heQ hem q ((e : ℝ) / 20) omega hstep,
    licensedOwners_eq_adoptedOwners e heQ hem q ((e : ℝ) / 20) omega hstep,
    hreserve.trans_lt hbudget, hliteral.trans_lt hbudget⟩

end
end ImbalancedChen.P4AActualRefinableArchivePayment
