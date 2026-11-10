import ImbalancedChen.P5OriginalFourthFifthSourceInputs

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The reverse licence on the COMPLETE original fourth input. The only new
finite witness is the actual decoder followed by the existing integer
geometry Boolean on every decoded row. It does not inspect NPZ, regenerate
data, compute a gain or use the ordinary derivative table. The binary,
transparent literal, parser and geometry soundness are all reused.
No caller supplies an admission, geometry or target-integral licence.
-/
namespace ImbalancedChen.P1OriginalFourthAllRowsAdmission

open P5OriginalFourthFifthSourceInputs
open P1OriginalFourthPackedTable
open P1OriginalFourthIntegerGeometryAdmission

/-- Computable original-data check, before the opaque parse witness is
chosen. Failure to parse is false, rather than an empty accepted bank. -/
def originalGeometryCheck : Bool :=
  match decodeWireRows originalFourthBytes with
  | none => false
  | some rows => rows.all integerGeometryAccept

/-- A new closed ORIGINAL geometry proof obligation. UNEVALUATED: no
local guard, certifier, Lean or numerical replay was run. Root must
obtain actual remote elaboration/kernel evidence for these exact bytes. -/
theorem originalGeometryCheck_true : originalGeometryCheck = true := by decide

noncomputable section
open Set
open scoped Classical
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation

theorem all_original_rows_pass (raw : FourthWireRow)
    (hr : raw ∈ originalFourthWireRows) : integerGeometryAccept raw = true := by
  have h := originalGeometryCheck_true
  rw [originalGeometryCheck,originalFourth_parse] at h
  exact List.all_eq_true.mp h raw hr

theorem all_original_rows_geometry (raw : FourthWireRow)
    (hr : raw ∈ originalFourthWireRows) : raw.toProducerRow.Geometry :=
  integerGeometryAccept_geometry raw (all_original_rows_pass raw hr)

/-- The missing reverse direction, for every original raw occurrence. -/
theorem original_raw_admitted (raw : FourthWireRow)
    (hr : raw ∈ originalFourthWireRows) : originalAdmission4 raw.toProducerRow :=
  ⟨raw,hr,rfl,all_original_rows_pass raw hr⟩

theorem originalRows4_all_admitted (r : ProducerRow) (hr : r ∈ originalRows4) :
    originalAdmission4 r := by
  obtain ⟨raw,hm,rfl⟩ := (originalRows4_source r).mp hr
  exact original_raw_admitted raw hm

theorem originalAdmission4_iff_mem (r : ProducerRow) :
    originalAdmission4 r ↔ r ∈ originalRows4 :=
  ⟨originalAdmission4_mem r,originalRows4_all_admitted r⟩

theorem originalRows4_geometry (r : ProducerRow) (hr : r ∈ originalRows4) : r.Geometry :=
  originalAdmission4_geometry r (originalRows4_all_admitted r hr)

theorem original_raw_eligible (raw : FourthWireRow) (hr : raw ∈ originalFourthWireRows)
    (t : Point) (ht : t ∈ raw.toProducerRow.box) :
    producerEligible originalAdmission4 raw.toProducerRow t :=
  ⟨original_raw_admitted raw hr,ht⟩

def originalBoxUnion : Set Point :=
  ⋃ raw ∈ originalFourthWireRows, raw.toProducerRow.box

/-- Equality of actual original domains, including all original boundary
points. Historical strictness and common refinement are supplied separately. -/
theorem originalBoxUnion_eq_actual_eligible :
    originalBoxUnion = {t | ∃ r ∈ originalRows4, producerEligible originalAdmission4 r t} := by
  ext t
  constructor
  · intro ht
    obtain ⟨raw,hrest⟩ := mem_iUnion.mp ht
    obtain ⟨hr,ht⟩ := mem_iUnion.mp hrest
    exact ⟨raw.toProducerRow,(originalRows4_source _).mpr ⟨raw,hr,rfl⟩,
      original_raw_eligible raw hr t ht⟩
  · rintro ⟨r,hr,_,ht⟩
    obtain ⟨raw,hm,rfl⟩ := (originalRows4_source r).mp hr
    exact mem_iUnion.mpr ⟨raw,mem_iUnion.mpr ⟨hm,ht⟩⟩

/-- The actual full maximum includes every original row candidate. No
unique-winner, first-match, historical admission or integral is presumed. -/
theorem original_candidate_le_actual_profile (e seed : ℝ) (raw : FourthWireRow)
    (hr : raw ∈ originalFourthWireRows) (t : Point) (ht : t ∈ raw.toProducerRow.box) :
    raw.toProducerRow.bufferedCandidate e t ≤
      producerProfile4 e originalRows4 originalAdmission4 seed t := by
  rw [ProducerRow.bufferedCandidate_eq]
  exact producerProfile4_row_le e originalRows4 originalAdmission4 seed t raw.toProducerRow
    ((originalRows4_source _).mpr ⟨raw,hr,rfl⟩) (original_raw_eligible raw hr t ht)

theorem actual_profile_inherits_off_original_union (e seed : ℝ) (t : Point)
    (ht : t ∉ originalBoxUnion) :
    producerProfile4 e originalRows4 originalAdmission4 seed t = seed := by
  unfold producerProfile4
  apply profile4_eq_seed_of_outside
  intro r hr he
  apply ht
  rw [originalBoxUnion_eq_actual_eligible]
  exact ⟨r,hr,he⟩

end
end ImbalancedChen.P1OriginalFourthAllRowsAdmission
