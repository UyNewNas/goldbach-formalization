import ImbalancedChen.P5AllChildrenReserveReassembly
import ImbalancedChen.P5HistoricalMask56FullSourceChildren
import ImbalancedChen.P1HistoricalFifthActualHistoryAdmission

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Pay the ACTUAL indexedActualReserve64 of Q's all-parent floor envelope.
D's exact complete-child reassembly is reused without another Jensen
proof. Buffered retained domains are identified with indexedDomain at e,
not with its zero-buffer baseline. The omitted domain is charged to the
actual zero-buffer omission AND the original moving-owner symmetric
difference. C's proved 428/75 section/Fubini estimate pays the latter.

Every original source index remains in the sums. There is one raw volume
and one modulus charge per parent, with no factor64 or owner count.
All inherited archive decisions remain UNEVALUATED. No new finite guard,
target reserve premise, data table, floor envelope or physical rho is used.
-/
namespace ImbalancedChen.P5HistoricalActualReserve64Budget
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1FifthUnitBoxGainDecomposition
open P1OriginalFifthLiteralKernelModulus P1OriginalFifthJointMeshSchedule
open P1OriginalFifthActualB13IntegralError P1OriginalFifthActualCrossingSections
open P1OriginalFifthMovingMeshFubiniBridge P1OriginalFifthAdoptedOwnerBank
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthIndexedBankError
open P1HistoricalFifthTypedBaseGeometry P5ChildSelectedOwnerJensenReserve
open P5AllChildrenReserveReassembly P5HistoricalMask56FullSourceChildren
open P5HistoricalIndexedTrimGeometry P5HistoricalCanonicalFilterReserve
open P5HistoricalUniformExtraGatePayment P5HistoricalGatePaidReserveSchedule
open P1HistoricalFifthActualHistoryAdmission

/-- All five original lower keys are positive and at most77. Hence the
ambient clipping in fixedParent loses no part of any actual source box. -/
theorem archive_fixedParent_eq_raw (i : ArchiveIndex) :
    fixedParent (archiveRow i) = (archiveRow i).originalBox := by
  apply Set.Subset.antisymm inter_subset_left
  intro t ht
  refine ⟨ht, mem_logPrimeBox.mpr (fun k => ?_)⟩
  have hk := rows_lower_key_bounds (archiveRow i) (archiveRow_source_member i) k
  have hlo : (1 : ℝ) ≤ ((archiveRow i).lo k : ℝ) := by exact_mod_cast hk.1
  have hhi : ((archiveRow i).lo k : ℝ) ≤ 77 := by exact_mod_cast hk.2
  have hl : (0 : ℝ) ≤ ((archiveRow i).lower k : ℝ) := by
    simp only [FifthWireRow.lower, archiveRow_grid]
    push_cast
    linarith
  have hu : ((archiveRow i).upper k : ℝ) ≤ (19 / 96 : ℝ) := by
    simp only [FifthWireRow.upper, archiveRow_grid]
    push_cast
    linarith
  exact ⟨hl.trans (ht k).1, (ht k).2.trans_le hu⟩

/-- The SAME actual licensed owners and strict selectedFifthCells tests
occur on both sides. This is the buffered domain, with z=e. -/
theorem archive_rawRetained_eq_indexedDomain
    (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    rawRetained (archiveRow i) e chi (refinedMesh q) omega
        (licensedOwners i e q chi omega) = indexedDomain i e q chi omega e := by
  unfold rawRetained selectedOwnerUnion indexedDomain ownerUnion rawOwnerDomain
  rw [selected_strict_owners_eq]
  ext t
  simp only [mem_inter_iff, mem_iUnion]
  aesop

/-- Exact D reassembly at the actual source index. This equality keeps
the buffered retained set; no zero-buffer replacement is made. -/
theorem indexedActualReserve64_eq_one_parent
    (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    indexedActualReserve64 i e q chi omega =
      rowMassBound (archiveRow i) *
        volume.real (rawOmitted (archiveRow i) e chi (refinedMesh q) omega
          (licensedOwners i e q chi omega)) +
      rowModulus (archiveRow i) e *
        volume.real (indexedDomain i e q chi omega e) := by
  rw [indexedActualReserve64,
    sum64_reserve_eq_single_raw_reserve (archiveRow i) (archiveRow_grid i),
    archive_rawRetained_eq_indexedDomain]

/-- A point omitted at e was already omitted at zero, or lies in the
actual domain motion of these very same owners. Open failures are paid,
not declared to be boundary faces. -/
theorem archive_rawOmitted_subset_zero_omission_union_motion
    (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    rawOmitted (archiveRow i) e chi (refinedMesh q) omega
        (licensedOwners i e q chi omega) ⊆
      indexedOmitted i e q chi omega ∪
        ownerSymmDiff (archiveRow i) 0 e chi chi (refinedMesh q) omega omega
          (licensedOwners i e q chi omega) := by
  intro t ht
  rw [rawOmitted, archive_rawRetained_eq_indexedDomain] at ht
  by_cases hz : t ∈ indexedDomain i e q chi omega 0
  · exact Or.inr (Or.inl ⟨hz, ht.2⟩)
  · exact Or.inl ⟨by rw [archive_fixedParent_eq_raw]; exact ht.1, hz⟩

/-- Actual full64 reserve is bounded by the existing B13 row envelope
plus the genuine zero-buffer omission. The target total-cost estimate
is not a premise: the original selected/firstStop crossing theorem
supplies the domain-motion volume, uniformly in q and owner count. -/
theorem indexedActualReserve64_le_rowEnvelope_add_trim
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (q : ℕ) (hq : 0 < q) (chi omega : ℝ)
    (hchi : chi ≤ (e : ℝ) / 10)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) :
    indexedActualReserve64 i e q chi omega ≤
      rowEnvelope (fun k => rowModulus (archiveRow k))
        (fun k => rowMassBound (archiveRow k)) i e + indexedTrimCost i e q chi omega := by
  let U := ownerSymmDiff (archiveRow i) 0 e chi chi (refinedMesh q) omega omega
    (licensedOwners i e q chi omega)
  let rate : ℝ := (428 / 75 : ℝ) * (e : ℝ) / (400 : ℝ)^4
  have hg := archiveRow_baseGeometry i
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hrate : 0 ≤ rate := by dsimp [rate]; positivity
  have hU : volume U ≤ ENNReal.ofReal rate :=
    actual_ownerSymmDiff_volume_le (archiveRow i) q hq hg.1 hg.2.2.2
      e he hemax chi chi omega omega hchi hstep (licensedOwners i e q chi omega)
      (licensedOwner_selected_zero i e q chi omega)
      (licensedOwner_selected_buffer i e q chi omega)
      (licensedOwner_firstStop_zero i e q chi omega)
      (licensedOwner_firstStop_buffer i e q chi omega)
  have hUfinite : volume U < ∞ := hU.trans_lt ENNReal.ofReal_lt_top
  have hUreal : volume.real U ≤ rate := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU
    simpa only [Measure.real, ENNReal.toReal_ofReal hrate] using h
  have hrawfinite : volume (archiveRow i).originalBox < ∞ := by
    rw [rawBox_volume _ hg.1]
    exact ENNReal.ofReal_lt_top
  have htrimfinite : volume (indexedOmitted i e q chi omega) < ∞ :=
    (measure_mono (fun _ ht => ht.1.1)).trans_lt hrawfinite
  have hsumfinite : volume (indexedOmitted i e q chi omega) + volume U ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨htrimfinite.ne, hUfinite.ne⟩
  have homit : volume.real (rawOmitted (archiveRow i) e chi (refinedMesh q) omega
        (licensedOwners i e q chi omega)) ≤
      volume.real (indexedOmitted i e q chi omega) + rate := by
    have hv : volume (rawOmitted (archiveRow i) e chi (refinedMesh q) omega
          (licensedOwners i e q chi omega)) ≤
        volume (indexedOmitted i e q chi omega) + volume U :=
      (measure_mono (archive_rawOmitted_subset_zero_omission_union_motion
        i e q chi omega)).trans (measure_union_le _ _)
    calc
      _ ≤ (volume (indexedOmitted i e q chi omega) + volume U).toReal :=
        ENNReal.toReal_mono hsumfinite hv
      _ = volume.real (indexedOmitted i e q chi omega) + volume.real U :=
        ENNReal.toReal_add htrimfinite.ne hUfinite.ne
      _ ≤ _ := add_le_add_left hUreal _
  have hretained : volume.real (indexedDomain i e q chi omega e) ≤ 1 / (400 : ℝ)^5 := by
    have hv := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((measure_mono (indexedDomain_subset_parent i e q chi omega e)).trans
        ((measure_mono inter_subset_left).trans_eq (rawBox_volume _ hg.1)))
    simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity :
      (0 : ℝ) ≤ 1 / (400 : ℝ)^5)] using hv
  have hM : 0 ≤ rowMassBound (archiveRow i) := by
    linarith [one_le_rowMassBound (archiveRow i)]
  rw [indexedActualReserve64_eq_one_parent]
  calc
    _ ≤ rowMassBound (archiveRow i) *
          (volume.real (indexedOmitted i e q chi omega) + rate) +
        rowModulus (archiveRow i) e * (1 / (400 : ℝ)^5) :=
      add_le_add (mul_le_mul_of_nonneg_left homit hM)
        (mul_le_mul_of_nonneg_left hretained (rowModulus_nonneg (archiveRow i) e))
    _ = _ := by unfold rowEnvelope indexedTrimCost rate; dsimp only [Measure.real]; ring

/-- At H's original gate margin and Q's actual history schedule, the
zero-buffer omission is only the original canonical filter strip. -/
theorem indexedTrimCost_eq_filter_on_schedule
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (hem : e ≤ archiveGateMargin / 4) (q : ℕ) (hq : 0 < q) (omega : ℝ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20) :
    indexedTrimCost i e q ((e : ℝ) / 20) omega =
      canonicalFilterCost i e q ((e : ℝ) / 20) omega := by
  rw [indexedTrimCost_eq_canonical_add_gate i (all_archive_indices_licensed i),
    gateRejectedCost_zero e he hem q ((e : ℝ) / 20) omega hstep i, add_zero,
    omittedVolumeCost_exact_canonical_split,
    archive_canonicalHistoryCost_zero i e he hemax q hq omega, zero_add]

/-- Per actual parent: one B13 row envelope and the original64*M*e
filter rate. The64 here is H's strip coefficient, not a child count. -/
theorem each_actual_reserve64_le_original_row_budget
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (hem : e ≤ archiveGateMargin / 4) (q : ℕ) (hq : 0 < q)
    (omega : ℝ) (hw0 : 0 ≤ omega) (hw : omega ≤ 1 / 800)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20)
    (hrough : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2) :
    indexedActualReserve64 i e q ((e : ℝ) / 20) omega ≤
      rowEnvelope (fun k => rowModulus (archiveRow k))
        (fun k => rowMassBound (archiveRow k)) i e +
        64 * rowMassBound (archiveRow i) * (e : ℝ) := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hh : (meshStepQ (refinedMesh q) : ℝ) ≤ 1 / 800 := by
    rw [cast_meshStepQ]
    linarith
  have hsmall : (meshStepQ (refinedMesh q) : ℝ) ≤ (e : ℝ) / 20 := by
    simpa only [cast_meshStepQ] using hstep
  have hc := canonicalFilterCost_le_actual_strip_rate i (all_archive_indices_licensed i)
    e he q ((e : ℝ) / 20) omega hw0 hw hh hstep
  have hrate : 12 * (4 * (e : ℝ) + 2 * (meshStepQ (refinedMesh q) : ℝ)) ≤
      64 * (e : ℝ) := by linarith
  have hM : 0 ≤ rowMassBound (archiveRow i) := by
    linarith [one_le_rowMassBound (archiveRow i)]
  have hf := hc.trans (mul_le_mul_of_nonneg_left hrate hM)
  have hb := indexedActualReserve64_le_rowEnvelope_add_trim i e he hemax q hq
    ((e : ℝ) / 20) omega (by linarith) hstep
  rw [indexedTrimCost_eq_filter_on_schedule i e he hemax hem q hq omega hstep] at hb
  nlinarith

/-- All292633 original positions, exactly once. The existing envelope
now pays the ACTUAL complete-child reserve, not just a literal-integral
error. No total reserve is assumed and no new scalar envelope is made. -/
theorem full_actual_reserve64_le_gatePaidEnvelope
    (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (hem : e ≤ archiveGateMargin / 4) (q : ℕ) (hq : 0 < q)
    (omega : ℝ) (hw0 : 0 ≤ omega) (hw : omega ≤ 1 / 800)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20)
    (hrough : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2) :
    (∑ i : ArchiveIndex, indexedActualReserve64 i e q ((e : ℝ) / 20) omega) ≤
      gatePaidEnvelope e := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ArchiveIndex))
    (fun i _hi => each_actual_reserve64_le_original_row_budget
      i e he hemax hem q hq omega hw0 hw hstep hrough)
  have heq : (∑ i : ArchiveIndex,
      rowEnvelope (fun k => rowModulus (archiveRow k))
        (fun k => rowMassBound (archiveRow k)) i e +
        64 * rowMassBound (archiveRow i) * (e : ℝ)) = gatePaidEnvelope e := by
    unfold gatePaidEnvelope bankEnvelope
    rw [Finset.sum_add_distrib]
    congr 1
    unfold P5HistoricalRejectedCoreReserve.sourceMassSum
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  exact hs.trans_eq heq

end
end ImbalancedChen.P5HistoricalActualReserve64Budget
