import ImbalancedChen.P1OriginalFifthActualB13IntegralError
import ImbalancedChen.P1OriginalFifthJointMeshSchedule
import Mathlib

/-!
A concrete common-adopted finite owner bank and its actual omitted mass.
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.

Common owners are constructed by filtering the SAME saved row's actual
decoder through the original two selected/firstStop tests. No verdict or
coverage is inferred for a removed child: its real fixed-parent remainder
is explicitly retained in the trim term.
-/
namespace ImbalancedChen.P1OriginalFifthAdoptedOwnerBank
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators ENNReal
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalCoarseFifthContinuation P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthRawBoxSelectorEquivalence P1FifthGrid400UnitBoxPartition
open P1FifthUnitBoxGainDecomposition P1FifthUnitBoxLiteralGainLower
open P1LiteralVariableFifthCompactSupplier
open P1OriginalFifthLiteralKernelModulus P1OriginalFifthActualB13IntegralError
open P1OriginalFifthMovingMeshFubiniBridge P1OriginalFifthJointMeshSchedule

abbrev Point := Fin 5 → ℝ

def decodedLabels (raw : FifthWireRow) (q : ℕ) : Finset (Label5 (refinedMesh q)) :=
  (decodeFifthRows raw (refinedMesh q)).image (fun r => r.cell)

/-- This is an actual finite constructor, not a supplied adoption verdict.
The same original raw decoder supplies every label on both sides. -/
def adoptedOwners (raw : FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Finset (Label5 (refinedMesh q)) :=
  ((selectedFifthCells 0 chi (refinedMesh q) omega (decodedLabels raw q)) ∩
    selectedFifthCells e chi (refinedMesh q) omega (decodedLabels raw q)).filter
      (fun j =>
        P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck 0 (refinedMesh q) j = true ∧
          P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck
            (e : ℝ) (refinedMesh q) j = true)

theorem adoptedOwners_original_decoded (raw : FifthWireRow) (e : ℚ) (q : ℕ)
    (chi omega : ℝ) (j : Label5 (refinedMesh q))
    (hj : j ∈ adoptedOwners raw e q chi omega) :
    ∃ r ∈ decodeFifthRows raw (refinedMesh q), r.cell = j := by
  have h0 := (Finset.mem_inter.mp (Finset.mem_filter.mp hj).1).1
  have hd := ((mem_selectedFifthCells 0 chi (refinedMesh q) omega
    (decodedLabels raw q) j).mp h0).1
  exact Finset.mem_image.mp hd

theorem adoptedOwners_selected_zero (raw : FifthWireRow) (e : ℚ) (q : ℕ)
    (chi omega : ℝ) (j : Label5 (refinedMesh q))
    (hj : j ∈ adoptedOwners raw e q chi omega) :
    j ∈ selectedFifthCells 0 chi (refinedMesh q) omega (adoptedOwners raw e q chi omega) := by
  have h0 := (Finset.mem_inter.mp (Finset.mem_filter.mp hj).1).1
  have h0' := (mem_selectedFifthCells 0 chi (refinedMesh q) omega (decodedLabels raw q) j).mp h0
  exact (mem_selectedFifthCells 0 chi (refinedMesh q) omega _ j).mpr ⟨hj, h0'.2⟩

theorem adoptedOwners_selected_buffer (raw : FifthWireRow) (e : ℚ) (q : ℕ)
    (chi omega : ℝ) (j : Label5 (refinedMesh q))
    (hj : j ∈ adoptedOwners raw e q chi omega) :
    j ∈ selectedFifthCells e chi (refinedMesh q) omega (adoptedOwners raw e q chi omega) := by
  have hE := (Finset.mem_inter.mp (Finset.mem_filter.mp hj).1).2
  have hE' := (mem_selectedFifthCells e chi (refinedMesh q) omega (decodedLabels raw q) j).mp hE
  exact (mem_selectedFifthCells e chi (refinedMesh q) omega _ j).mpr ⟨hj, hE'.2⟩

theorem adoptedOwners_firstStop_zero (raw : FifthWireRow) (e : ℚ) (q : ℕ)
    (chi omega : ℝ) (j : Label5 (refinedMesh q))
    (hj : j ∈ adoptedOwners raw e q chi omega) :
    P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck 0 (refinedMesh q) j = true :=
  (Finset.mem_filter.mp hj).2.1

theorem adoptedOwners_firstStop_buffer (raw : FifthWireRow) (e : ℚ) (q : ℕ)
    (chi omega : ℝ) (j : Label5 (refinedMesh q))
    (hj : j ∈ adoptedOwners raw e q chi omega) :
    P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck (e : ℝ) (refinedMesh q) j = true :=
  (Finset.mem_filter.mp hj).2.2

/-- The fixed saved parent retains the original half-open ambient clipping.
In particular a positive-volume open inherit/failure region is not silently
discarded, and neither a child projection nor a boundary face is removed. -/
def fixedParent (raw : FifthWireRow) : Set Point :=
  raw.originalBox ∩ logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))

def adoptedDomain (raw : FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) (z : ℚ) : Set Point :=
  ownerUnion raw z chi (refinedMesh q) omega (adoptedOwners raw e q chi omega)

def omittedParent (raw : FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) : Set Point :=
  fixedParent raw \ adoptedDomain raw e q chi omega 0

theorem fixedParent_measurable (raw : FifthWireRow) : MeasurableSet (fixedParent raw) :=
  (measurableSet_originalBox raw).inter (measurableSet_logPrimeBox _ _)

theorem adoptedDomain_measurable (raw : FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) (z : ℚ) :
    MeasurableSet (adoptedDomain raw e q chi omega z) := ownerUnion_measurable _ _ _ _ _ _

theorem omittedParent_measurable (raw : FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    MeasurableSet (omittedParent raw e q chi omega) :=
  (fixedParent_measurable raw).diff (adoptedDomain_measurable raw e q chi omega 0)

theorem adoptedDomain_subset_fixedParent (raw : FifthWireRow) (e : ℚ) (q : ℕ)
    (chi omega : ℝ) (z : ℚ) : adoptedDomain raw e q chi omega z ⊆ fixedParent raw := by
  intro t ht
  obtain ⟨j, _hj, htj⟩ := mem_iUnion₂.mp ht
  exact ⟨htj.1, htj.2.2.1⟩

theorem fixedParent_subset_positiveCube (raw : FifthWireRow)
    (hgrid : raw.grid = 400) (hpositive : ∀ i, 1 ≤ raw.lo i) :
    fixedParent raw ⊆ positiveCube (1 / 400 : ℝ) (19 / 96 : ℝ) := by
  intro t ht i _hi
  have hlo : (raw.lo i : ℝ) / 400 ≤ t i := by
    simpa [FifthWireRow.lower, hgrid] using (ht.1 i).1
  have hk : (1 : ℝ) ≤ (raw.lo i : ℝ) := by exact_mod_cast hpositive i
  exact ⟨by linarith, (mem_logPrimeBox.mp ht.2 i).2.le⟩

/-- Exact saved-parent clipping, with the original rational endpoints. -/
theorem fixedParent_eq_exact_box (raw : FifthWireRow) :
    fixedParent raw = logPrimeBox
      (fun i => max (raw.lower i : ℝ) 0)
      (fun i => min (raw.upper i : ℝ) (19 / 96 : ℝ)) := by
  ext t
  constructor
  · intro ht
    exact mem_logPrimeBox.mpr (fun i =>
      ⟨max_le (ht.1 i).1 (mem_logPrimeBox.mp ht.2 i).1,
        lt_min (ht.1 i).2 (mem_logPrimeBox.mp ht.2 i).2⟩)
  · intro ht
    have hh := mem_logPrimeBox.mp ht
    exact ⟨fun i => ⟨(le_max_left _ _).trans (hh i).1,
      (hh i).2.trans_le (min_le_left _ _)⟩,
      mem_logPrimeBox.mpr (fun i => ⟨(le_max_right _ _).trans (hh i).1,
        (hh i).2.trans_le (min_le_right _ _)⟩)⟩

theorem fixedParent_volume_exact (raw : FifthWireRow) :
    volume (fixedParent raw) = ∏ i : Fin 5,
      ENNReal.ofReal (min (raw.upper i : ℝ) (19 / 96 : ℝ) - max (raw.lower i : ℝ) 0) := by
  rw [fixedParent_eq_exact_box, logPrimeBox, volume_pi_pi]
  simp_rw [Real.volume_Ico]

/-- Omitted mass is literally the remainder in each true decoded Ico cell.
This equality preserves partially retained cells and all their true gates;
it is stronger than merely counting labels excluded from the bank. -/
theorem omittedParent_eq_exact_decoded_remainders (raw : FifthWireRow)
    (q : ℕ) (hq : 0 < q) (hgrid : raw.grid = 400) (hmask : 0 ≤ raw.mask)
    (e : ℚ) (chi omega : ℝ) :
    omittedParent raw e q chi omega =
      ⋃ r ∈ decodeFifthRows raw (refinedMesh q),
        logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell \
          adoptedDomain raw e q chi omega 0 := by
  have hcover := refined_originalBox_inter_ambient_eq_decode_union q hq raw hgrid hmask
  change fixedParent raw \ adoptedDomain raw e q chi omega 0 = _
  rw [show fixedParent raw = _ from hcover]
  ext t
  constructor
  · rintro ⟨ht, hnot⟩
    obtain ⟨r, hr, htr⟩ := mem_iUnion₂.mp ht
    exact mem_iUnion₂.mpr ⟨r, hr, htr, hnot⟩
  · intro ht
    obtain ⟨r, hr, htr, hnot⟩ := mem_iUnion₂.mp ht
    exact ⟨mem_iUnion₂.mpr ⟨r, hr, htr⟩, hnot⟩

/-- Distinct actual saved keys retain disjoint trim domains. This provides
exact bank geometry without charging an overlapped raw parent twice. -/
theorem omittedParents_pairwise_disjoint (records : Finset FifthWireRow)
    (hgrid : ∀ raw ∈ records, raw.grid = 400) (hkeys : KeyInjective records)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Set.PairwiseDisjoint (records : Set FifthWireRow)
      (fun raw => omittedParent raw e q chi omega) := by
  intro a ha b hb hne
  exact ((records_pairwise_disjoint records hgrid hkeys) ha hb hne).mono
    (fun _ ht => ht.1.1) (fun _ ht => ht.1.1)

def parentIntegral (raw : FifthWireRow) : ℝ :=
  ∫ t in fixedParent raw, positiveKernel raw 0 t

def ownerIntegral (raw : FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) (z : ℚ) : ℝ :=
  ∫ t in adoptedDomain raw e q chi omega z, positiveKernel raw (z : ℝ) t

def omittedMass (raw : FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∫ t in omittedParent raw e q chi omega, positiveKernel raw 0 t

def omittedVolumeCost (raw : FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  rowMassBound raw * (volume (omittedParent raw e q chi omega)).toReal

theorem omittedVolumeCost_nonneg (raw : FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    0 ≤ omittedVolumeCost raw e q chi omega :=
  mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_rowMassBound raw)) ENNReal.toReal_nonneg

theorem omittedMass_nonneg (raw : FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    0 ≤ omittedMass raw e q chi omega :=
  setIntegral_nonneg (omittedParent_measurable raw e q chi omega) (fun _ _ => le_max_left _ _)

theorem omittedMass_eq_parent_sub_baseline (raw : FifthWireRow)
    (hgrid : raw.grid = 400) (hpositive : ∀ i, 1 ≤ raw.lo i)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    omittedMass raw e q chi omega = parentIntegral raw - ownerIntegral raw e q chi omega 0 := by
  simpa only [omittedMass, omittedParent, parentIntegral, ownerIntegral, Rat.cast_zero] using
    setIntegral_sdiff (adoptedDomain_measurable raw e q chi omega 0)
      (positiveKernel_integrableOn_of_subset raw 0 (fixedParent raw)
        (fixedParent_subset_positiveCube raw hgrid hpositive))
      (adoptedDomain_subset_fixedParent raw e q chi omega 0)

theorem omittedMass_le_exact_volumeCost (raw : FifthWireRow)
    (hgrid : raw.grid = 400) (hpositive : ∀ i, 1 ≤ raw.lo i)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    omittedMass raw e q chi omega ≤ omittedVolumeCost raw e q chi omega := by
  have hsub : omittedParent raw e q chi omega ⊆ raw.originalBox := fun _ ht => ht.1.1
  have hfinite : volume (omittedParent raw e q chi omega) < ∞ := by
    exact (measure_mono hsub).trans_lt (by rw [rawBox_volume raw hgrid]; exact ENNReal.ofReal_lt_top)
  have hbound := norm_setIntegral_le_of_norm_le_const hfinite (fun t ht => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left 0 _)]
    exact positive_kernel_le_rowMassBound raw 0 (by norm_num) t
      (fixedParent_subset_positiveCube raw hgrid hpositive ht.1))
  change ‖omittedMass raw e q chi omega‖ ≤ omittedVolumeCost raw e q chi omega at hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (omittedMass_nonneg raw e q chi omega)] at hbound
  exact hbound

/-- Actual B13 applies to the finite bank constructed above, with every
selected/firstStop hypothesis discharged from the constructor itself. -/
theorem adopted_ownerIntegral_B13 (raw : FifthWireRow)
    (q : ℕ) (hq : 0 < q) (hgrid : raw.grid = 400)
    (hpositive : ∀ i, 1 ≤ raw.lo i) (hkey : raw.lo 0 ≤ 77)
    (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200) (chi omega : ℝ)
    (hchi : chi ≤ (e : ℝ) / 10)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) :
    |ownerIntegral raw e q chi omega e - ownerIntegral raw e q chi omega 0| ≤
      rowEnvelope rowModulus rowMassBound raw e := by
  simpa only [ownerIntegral, adoptedDomain, rowEnvelope, Rat.cast_zero] using
    actual_selected_owner_B13 raw q hq hgrid hpositive hkey e he hemax chi chi omega omega
      hchi hstep (adoptedOwners raw e q chi omega)
      (adoptedOwners_selected_zero raw e q chi omega)
      (adoptedOwners_selected_buffer raw e q chi omega)
      (adoptedOwners_firstStop_zero raw e q chi omega)
      (adoptedOwners_firstStop_buffer raw e q chi omega)

end
end ImbalancedChen.P1OriginalFifthAdoptedOwnerBank
