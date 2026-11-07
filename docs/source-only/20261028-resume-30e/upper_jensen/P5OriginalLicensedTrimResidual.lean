import ImbalancedChen.P5OriginalBufferOwnerGeometry
import ImbalancedChen.P1OriginalFifthUniformAdoptedBankError

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The licensed subfamily is selected by ORIGINAL integer third-plane AND
independent pair-gate margins, not by a desired trim or integral verdict.
Residual parents remain explicit and retain their true actual omitted mass.
-/
namespace ImbalancedChen.P5OriginalLicensedTrimResidual
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1FifthUnitBoxGainDecomposition
open P1OriginalFifthAdoptedOwnerBank
open P1OriginalFifthUniformAdoptedBankError
open P1OriginalFifthLiteralKernelModulus
open P1OriginalFifthJointMeshSchedule
open P1OriginalFifthActualB13IntegralError
open P5OriginalBufferOwnerGeometry

/-- Two original nonleading-pair branches. These labels concern the
inherited third owner, NOT the independent fifth raw.mask field. -/
def ownerLicenseCheck (raw : FifthWireRow) : Bool :=
  P1FifthMask5RawOwnerLicence.mask5WholeRawCheck raw ||
    P1FifthMask6RawOwnerLicence.mask6WholeRawCheck raw

def licensedRows (records : Finset FifthWireRow) : Finset FifthWireRow :=
  records.filter (fun raw => ownerLicenseCheck raw = true)

def residualRows (records : Finset FifthWireRow) : Finset FifthWireRow :=
  records.filter (fun raw => ownerLicenseCheck raw = false)

theorem licensed_key (raw : FifthWireRow) (hc : ownerLicenseCheck raw = true) :
    P1FifthRawKeyThirdOwnerPersistence.thirdOwnerKeyCheck raw = true := by
  rcases Bool.or_eq_true.mp hc with h5 | h6
  · exact P1FifthMask5RawOwnerLicence.mask5HistoryCheck_thirdOwnerKeyCheck raw
      (Bool.and_eq_true.mp h5).1
  · exact P1FifthMask6RawOwnerLicence.mask6HistoryCheck_thirdOwnerKeyCheck raw
      (Bool.and_eq_true.mp h6).1

theorem licensed_primitive_key_bounds (raw : FifthWireRow) (hc : ownerLicenseCheck raw = true) :
    raw.grid = 400 ∧ 0 ≤ raw.mask ∧ (∀ i : Fin 5, 1 ≤ raw.lo i) ∧ raw.lo 0 ≤ 77 := by
  rcases Bool.or_eq_true.mp hc with h5 | h6
  · have hcore := (Bool.and_eq_true.mp h5).1
    have hs : raw.grid = 400 ∧ 0 ≤ raw.mask ∧ (∀ i, 1 ≤ raw.lo i) ∧
        (∀ i : Fin 4, raw.lo i.succ + 1 ≤ raw.lo i.castSucc) ∧ raw.lo 0 ≤ 77 ∧
        0 < min (P1FifthMask5RawOwnerLicence.ascendingThirdNumerator raw)
          (P1FifthMask5RawOwnerLicence.descendingThirdNumerator raw) := of_decide_eq_true hcore
    exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.2.1⟩
  · have hcore := (Bool.and_eq_true.mp h6).1
    have hs : raw.grid = 400 ∧ 0 ≤ raw.mask ∧ (∀ i, 1 ≤ raw.lo i) ∧
        (∀ i : Fin 4, raw.lo i.succ + 1 ≤ raw.lo i.castSucc) ∧ raw.lo 0 ≤ 77 ∧
        0 < min (P1FifthMask6RawOwnerLicence.ascendingThirdNumerator raw)
          (P1FifthMask6RawOwnerLicence.descendingThirdNumerator raw) := of_decide_eq_true hcore
    exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.2.1⟩

/-- This consumes the original fullGamma dispatch and the separate xz/yz
pair gate from the existing whole-raw theorem. A positive Jensen thirdgap
by itself is never substituted for that licence. -/
theorem licensed_whole_original_owner_cover (raw : FifthWireRow)
    (hc : ownerLicenseCheck raw = true)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (q : ℕ) (hq : 0 < q)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) (hw : omega ≤ 1 / 400) :
    raw.originalBox = ⋃ r ∈ decodeFifthRows raw (refinedMesh q),
      rawOwnerDomain raw e chi (refinedMesh q) omega r.cell := by
  rcases Bool.or_eq_true.mp hc with h5 | h6
  · exact P1FifthMask5RawOwnerLicence.whole_raw_mask5_owner_cover raw h5
      e he hemax chi omega hchi q hq hstep hw
  · exact P1FifthMask6RawOwnerLicence.whole_raw_mask6_owner_cover raw h6
      e he hemax chi omega hchi q hq hstep hw

/-- The actual canonical adopted-owner constructor removes NO decoded
label on this independently licensed subfamily. -/
theorem licensed_adoptedOwners_eq_decoder (raw : FifthWireRow)
    (hc : ownerLicenseCheck raw = true) (e : ℚ) (hemax : e ≤ 3 / 51200)
    (q : ℕ) (chi omega : ℝ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) (hw : omega ≤ 1 / 400) :
    adoptedOwners raw e q chi omega = decodedLabels raw q :=
  adoptedOwners_eq_decodedLabels_of_key raw (licensed_key raw hc) e hemax q chi omega hstep hw

theorem licensed_buffered_adoptedDomain_eq_parent (raw : FifthWireRow)
    (hc : ownerLicenseCheck raw = true)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (q : ℕ) (hq : 0 < q)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) (hw : omega ≤ 1 / 400) :
    adoptedDomain raw e q chi omega e = raw.originalBox := by
  apply Set.Subset.antisymm (fun _ ht => (adoptedDomain_subset_fixedParent raw e q chi omega e ht).1)
  intro t ht
  rw [licensed_whole_original_owner_cover raw hc e he hemax chi omega hchi q hq hstep hw] at ht
  obtain ⟨r, hr, htOwner⟩ := mem_iUnion₂.mp ht
  have hj : r.cell ∈ adoptedOwners raw e q chi omega := by
    rw [licensed_adoptedOwners_eq_decoder raw hc e hemax q chi omega hstep hw]
    exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
  exact mem_iUnion₂.mpr ⟨r.cell, hj, htOwner⟩

/-- Zero-buffer source coverage is proved from the same physical buffered
owner via the actual Gamma/firstStop loss theorem. It is NOT inferred by
running the positive-e whole-box proof with the impossible chi<0 premise. -/
theorem licensed_baseline_adoptedDomain_eq_parent (raw : FifthWireRow)
    (hc : ownerLicenseCheck raw = true)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (q : ℕ) (hq : 0 < q)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) (hw : omega ≤ 1 / 400) :
    adoptedDomain raw e q chi omega 0 = raw.originalBox := by
  apply Set.Subset.antisymm (fun _ ht => (adoptedDomain_subset_fixedParent raw e q chi omega 0 ht).1)
  intro t ht
  rw [licensed_whole_original_owner_cover raw hc e he hemax chi omega hchi q hq hstep hw] at ht
  obtain ⟨r, hr, htOwner⟩ := mem_iUnion₂.mp ht
  have hj : r.cell ∈ adoptedOwners raw e q chi omega := by
    rw [licensed_adoptedOwners_eq_decoder raw hc e hemax q chi omega hstep hw]
    exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
  have hzero := fullCell_buffer_subset_zero e he.le chi (refinedMesh q) omega
    (adoptedOwners raw e q chi omega) r.cell
    (adoptedOwners_selected_zero raw e q chi omega r.cell hj)
    (adoptedOwners_selected_buffer raw e q chi omega r.cell hj) htOwner.2
  exact mem_iUnion₂.mpr ⟨r.cell, hj, htOwner.1, hzero⟩

theorem licensed_omittedParent_empty (raw : FifthWireRow)
    (hc : ownerLicenseCheck raw = true)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (q : ℕ) (hq : 0 < q)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) (hw : omega ≤ 1 / 400) :
    omittedParent raw e q chi omega = ∅ := by
  rw [omittedParent, licensed_baseline_adoptedDomain_eq_parent raw hc
    e he hemax chi omega hchi q hq hstep hw]
  exact Set.diff_eq_empty.mpr inter_subset_left

theorem licensed_omittedVolumeCost_zero (raw : FifthWireRow)
    (hc : ownerLicenseCheck raw = true)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (q : ℕ) (hq : 0 < q)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) (hw : omega ≤ 1 / 400) :
    omittedVolumeCost raw e q chi omega = 0 := by
  simp only [omittedVolumeCost, licensed_omittedParent_empty raw hc
    e he hemax chi omega hchi q hq hstep hw, measure_empty, ENNReal.toReal_zero, mul_zero]

/-- The residual is literally the archived rows for which NEITHER original
whole-box third-plus-pair margin check passes. No row is declared absent. -/
theorem residual_rows_exact (records : Finset FifthWireRow) (raw : FifthWireRow) :
    raw ∈ residualRows records ↔ raw ∈ records ∧
      P1FifthMask5RawOwnerLicence.mask5WholeRawCheck raw = false ∧
      P1FifthMask6RawOwnerLicence.mask6WholeRawCheck raw = false := by
  simp [residualRows, ownerLicenseCheck]

/-- All licensed actual trim costs vanish; the complete bank's unresolved
cost is EXACTLY its explicitly retained residual parent subfamily. -/
theorem trimVolumeBank_eq_residual
    (records : Finset FifthWireRow)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (q : ℕ) (hq : 0 < q)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) (hw : omega ≤ 1 / 400) :
    trimVolumeBank records e q chi omega = trimVolumeBank (residualRows records) e q chi omega := by
  unfold trimVolumeBank residualRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro raw _
  by_cases hc : ownerLicenseCheck raw = true
  · have hz := licensed_omittedVolumeCost_zero raw hc e he hemax chi omega hchi q hq hstep hw
    simp [hc, hz]
  · have hf : ownerLicenseCheck raw = false := Bool.eq_false_iff.mpr hc
    simp only [hf, if_true]

/-- A quantitative upper bound for the STILL unresolved subfamily uses each
real original clipped parent once. It is not a target-smallness assumption. -/
def residualParentVolumeCost (records : Finset FifthWireRow) : ℝ :=
  ∑ raw ∈ residualRows records, rowMassBound raw * (volume (fixedParent raw)).toReal

theorem residual_trim_le_parentVolumeCost (records : Finset FifthWireRow)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    trimVolumeBank (residualRows records) e q chi omega ≤ residualParentVolumeCost records := by
  apply Finset.sum_le_sum
  intro raw hr
  have hraw : raw ∈ records := (Finset.mem_filter.mp hr).1
  have hparentFinite : volume (fixedParent raw) < ∞ :=
    (measure_mono inter_subset_left).trans_lt (by rw [rawBox_volume raw (hgrid raw hraw)]; exact ENNReal.ofReal_lt_top)
  have hv := ENNReal.toReal_mono hparentFinite.ne
    (measure_mono (show omittedParent raw e q chi omega ⊆ fixedParent raw from sdiff_subset))
  exact mul_le_mul_of_nonneg_left hv (by linarith [one_le_rowMassBound raw])

/-- The original B13 error is now charged to residual RAW parents only;
no selected-owner or64-child multiplicity is introduced. -/
theorem full_bank_error_le_envelope_add_residual
    (records : Finset FifthWireRow)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hpositive : ∀ raw ∈ records, ∀ i, 1 ≤ raw.lo i)
    (hkey : ∀ raw ∈ records, raw.lo 0 ≤ 77)
    (q : ℕ) (hq : 0 < q) (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) (hw : omega ≤ 1 / 400) :
    |retainedBankIntegral records e q chi omega - parentBankIntegral records| ≤
      bankEnvelope records rowModulus rowMassBound e + residualParentVolumeCost records := by
  have h := retainedBank_parent_error_le records hgrid hpositive hkey q hq e he.le hemax
    chi omega hchi.le hstep
  rw [trimVolumeBank_eq_residual records e he hemax chi omega hchi q hq hstep hw] at h
  exact h.trans (add_le_add_left (residual_trim_le_parentVolumeCost records hgrid e q chi omega) _)

end
end ImbalancedChen.P5OriginalLicensedTrimResidual
