import ImbalancedChen.P5HistoricalTypedGateAdmissibility
import ImbalancedChen.P1OriginalFifthQuantitativeGateRefinement
import ImbalancedChen.P5HistoricalCanonicalFilterReserve

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original finite archive has a strict correlated zero-buffer margin on
each CLOSED source box. Take its finite minimum BEFORE refining the mesh.
The actual original endpoint gate loses at most 16h; the buffer loses 2e.
This proves that the additional gate filter removes NO adopted source
owner on the common schedule. No cost or gain comparison is a premise.

The G finite zero-gate proofs are implemented but unexecuted predecessors.
This file neither runs nor supplies any new archive decision body.
-/
namespace ImbalancedChen.P5HistoricalUniformExtraGatePayment
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthCorrelatedRawBoxGates P1OriginalFifthQuantitativeGateRefinement
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthAdoptedOwnerBank
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthIndexedBankError
open P5HistoricalTypedGateAdmissibility P5HistoricalIndexedTrimGeometry
open P5HistoricalCanonicalFilterReserve

/-- The harmless positive entry makes the minimum nonempty without a
chosen row. Every original source position still contributes its margin. -/
def archiveGateMargins : Finset ℚ :=
  insert 1 (Finset.univ.image (fun i : ArchiveIndex => gateMarginQ 0 (archiveRow i)))

theorem archiveGateMargins_nonempty : archiveGateMargins.Nonempty := by
  exact ⟨1, Finset.mem_insert_self _ _⟩

def archiveGateMargin : ℚ := archiveGateMargins.min' archiveGateMargins_nonempty

theorem archiveGateMargin_pos : 0 < archiveGateMargin := by
  apply (Finset.lt_min'_iff _ _).mpr
  intro d hd
  rcases Finset.mem_insert.mp hd with rfl | hd
  · norm_num
  · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hd
    exact gateMarginQ_pos 0 (archiveRow i) (archiveRow_original_zero_gates i)

theorem archiveGateMargin_le_row (i : ArchiveIndex) :
    archiveGateMargin ≤ gateMarginQ 0 (archiveRow i) := by
  exact Finset.min'_le archiveGateMargins _
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

/-- All three families retain the source row's own selected mask. The
same point occurs in its tent and square before the original margin is
taken. This is stronger than a pointwise-support-only statement. -/
theorem archive_buffered_uniform_margin (i : ArchiveIndex) (e : ℚ)
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox (archiveRow i)) :
    (1 / 2 : ℝ) + ((archiveGateMargin - 2 * e : ℚ) : ℝ) ≤
        candidate (e : ℝ) (maskSlots 5 (archiveRow i).mask.toNat) t ∧
    (∀ j, prefixSquareExpr t j + ((archiveGateMargin - 2 * e : ℚ) : ℝ) ≤
        candidate (e : ℝ) (maskSlots 5 (archiveRow i).mask.toNat) t) ∧
    (∀ j ∉ maskSlots 5 (archiveRow i).mask.toNat,
      selectedSquareExpr (maskSlots 5 (archiveRow i).mask.toNat) t j +
          ((archiveGateMargin - 2 * e : ℚ) : ℝ) ≤
        candidate (e : ℝ) (maskSlots 5 (archiveRow i).mask.toNat) t) := by
  have hm := (correlatedRawBoxGateCheck_uniform_margin 0 (archiveRow i)
    (archiveRow_original_zero_gates i)).2 t ht
  have hd : (archiveGateMargin : ℝ) ≤ (gateMarginQ 0 (archiveRow i) : ℝ) := by
    exact_mod_cast archiveGateMargin_le_row i
  have hc : candidate (e : ℝ) (maskSlots 5 (archiveRow i).mask.toNat) t =
      candidate 0 (maskSlots 5 (archiveRow i).mask.toNat) t - 2 * (e : ℝ) := by
    simp only [candidate]
    ring
  simp only [Rat.cast_zero] at hm
  simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, hc]
  refine ⟨by linarith [hm.1], ?_, ?_⟩
  · intro j
    linarith [hm.2.1 j]
  · intro j hj
    linarith [hm.2.2 j hj]

/-- The actual Boolean endpoint gate is now proved for EVERY decoded row
of EVERY source index. The hypothesis is only a buffer/mesh inequality. -/
theorem archive_all_decoded_gates (e : ℚ) (m : ℕ)
    (hsmall : 2 * e + 16 * meshStepQ m < archiveGateMargin)
    (i : ArchiveIndex) :
    ∀ r ∈ decodeFifthRows (archiveRow i) m, gateCheck e m r = true := by
  apply all_decoded_gateCheck_eq_true_of_uniform_margin
    e (archiveGateMargin - 2 * e) (archiveRow i) m (by linarith)
  exact archive_buffered_uniform_margin i e

/-- The existing common schedule h≤e/20 is sufficient at every smaller
buffer z≤e. The original margin is fixed independently of e and q. -/
theorem archive_all_decoded_gates_on_schedule
    (e z : ℚ) (hz : z ≤ e) (hecap : e ≤ archiveGateMargin / 4)
    (q : ℕ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20)
    (i : ArchiveIndex) :
    ∀ r ∈ decodeFifthRows (archiveRow i) (refinedMesh q),
      gateCheck z (refinedMesh q) r = true := by
  have hstepQ : meshStepQ (refinedMesh q) ≤ e / 20 := by
    have hR : (meshStepQ (refinedMesh q) : ℝ) ≤ (e : ℝ) / 20 := by
      simpa only [cast_meshStepQ] using hstep
    exact_mod_cast hR
  apply archive_all_decoded_gates z (refinedMesh q) _ i
  linarith [archiveGateMargin_pos]

/-- Crucially, membership comes from the independently defined ADOPTED
owner, not from the already-filtered licensed owner. -/
theorem adopted_sourceOwnerRow_decoded (i : ArchiveIndex) (e : ℚ)
    (q : ℕ) (chi omega : ℝ) (j : Label5 (refinedMesh q))
    (hj : j ∈ adoptedOwners (archiveRow i) e q chi omega) :
    sourceOwnerRow i q j ∈ decodeFifthRows (archiveRow i) (refinedMesh q) := by
  obtain ⟨r, hr, hcell⟩ := adoptedOwners_original_decoded (archiveRow i) e q chi omega j hj
  have hmask := decodeFifthRows_selected_eq (archiveRow i) (refinedMesh q) r hr
  have heq : r = sourceOwnerRow i q j := by
    cases r
    simp only [sourceOwnerRow, FifthRow.mk.injEq] at *
    exact ⟨hcell, hmask⟩
  exact heq ▸ hr

theorem licensedOwners_eq_adoptedOwners
    (e : ℚ) (he : 0 ≤ e) (hecap : e ≤ archiveGateMargin / 4)
    (q : ℕ) (chi omega : ℝ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20)
    (i : ArchiveIndex) :
    licensedOwners i e q chi omega = adoptedOwners (archiveRow i) e q chi omega := by
  apply Finset.filter_eq_self.mpr
  intro j hj
  have hr := adopted_sourceOwnerRow_decoded i e q chi omega j hj
  exact ⟨archive_all_decoded_gates_on_schedule e 0 he hecap q hstep i _ hr,
    archive_all_decoded_gates_on_schedule e e le_rfl hecap q hstep i _ hr⟩

/-- This is the row bank passed to the existing common causal constructor,
with each source owner's original mask. No replacement cap is defined. -/
theorem licensedRows_eq_adopted_source_rows
    (e : ℚ) (he : 0 ≤ e) (hecap : e ≤ archiveGateMargin / 4)
    (q : ℕ) (chi omega : ℝ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20) :
    licensedRows e q chi omega = licensedIndices.biUnion (fun i =>
      (adoptedOwners (archiveRow i) e q chi omega).image (sourceOwnerRow i q)) := by
  unfold licensedRows
  simp_rw [licensedOwners_eq_adoptedOwners e he hecap q chi omega hstep]

/-- The actual old and buffered clipped source domains use the same
owners; all history/firstStop predicates inside ownerUnion are retained. -/
theorem indexedDomain_eq_adoptedDomain
    (e : ℚ) (he : 0 ≤ e) (hecap : e ≤ archiveGateMargin / 4)
    (q : ℕ) (chi omega : ℝ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20)
    (i : ArchiveIndex) (z : ℚ) :
    indexedDomain i e q chi omega z = adoptedDomain (archiveRow i) e q chi omega z := by
  unfold indexedDomain adoptedDomain
  rw [licensedOwners_eq_adoptedOwners e he hecap q chi omega hstep i]

theorem gateRejectedDomain_empty
    (e : ℚ) (he : 0 ≤ e) (hecap : e ≤ archiveGateMargin / 4)
    (q : ℕ) (chi omega : ℝ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20)
    (i : ArchiveIndex) : gateRejectedDomain i e q chi omega = ∅ := by
  rw [gateRejectedDomain, indexedDomain_eq_adoptedDomain e he hecap q chi omega hstep]
  exact Set.diff_self

theorem gateRejectedCost_zero
    (e : ℚ) (he : 0 ≤ e) (hecap : e ≤ archiveGateMargin / 4)
    (q : ℕ) (chi omega : ℝ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20)
    (i : ArchiveIndex) : gateRejectedCost i e q chi omega = 0 := by
  simp only [gateRejectedCost, gateRejectedDomain_empty e he hecap q chi omega hstep,
    measure_empty, ENNReal.toReal_zero, mul_zero]

theorem gateRejectedBankCost_zero
    (e : ℚ) (he : 0 ≤ e) (hecap : e ≤ archiveGateMargin / 4)
    (q : ℕ) (chi omega : ℝ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20) :
    gateRejectedBankCost e q chi omega = 0 := by
  unfold gateRejectedBankCost
  exact Finset.sum_eq_zero (fun i _ => gateRejectedCost_zero e he hecap q chi omega hstep i)

/-- Exact adopted-bank consumer. Only the history and canonical-filter
regions remain. It would be incorrect to claim that history is empty. -/
theorem licensedTrimCost_eq_history_add_filter
    (e : ℚ) (he : 0 ≤ e) (hecap : e ≤ archiveGateMargin / 4)
    (q : ℕ) (chi omega : ℝ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20) :
    licensedTrimCost e q chi omega =
      canonicalHistoryBankCost q chi omega + canonicalFilterBankCost e q chi omega := by
  have hrow (i : ArchiveIndex) (hi : i ∈ licensedIndices) :
      indexedTrimCost i e q chi omega =
        canonicalHistoryCost i q chi omega + canonicalFilterCost i e q chi omega := by
    rw [indexedTrimCost_eq_canonical_add_gate i hi,
      gateRejectedCost_zero e he hecap q chi omega hstep i, add_zero,
      omittedVolumeCost_exact_canonical_split]
  unfold licensedTrimCost canonicalHistoryBankCost canonicalFilterBankCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hrow

end
end ImbalancedChen.P5HistoricalUniformExtraGatePayment
