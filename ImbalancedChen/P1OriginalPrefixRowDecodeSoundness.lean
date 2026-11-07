import ImbalancedChen.P1OriginalVariableFifthContinuation

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Typed raw-to-physical row semantics. Integer payload statistics remain raw
and are never interpreted as dynamic parents, history licences, fixed caps,
or proved gains. Fifth grid cells are decoded conservatively into genuinely
contained cells of a specified original 0..19/96 mesh. No coverage or
one-record/one-policy-cell identity is asserted.
-/

namespace ImbalancedChen.P1OriginalPrefixRowDecodeSoundness
open scoped BigOperators

/-- Bit i is original processing slot i, with no reversal or sorting. -/
def maskSlots (rank mask : ℕ) : Finset (Fin rank) :=
  Finset.univ.filter (fun i => Nat.testBit mask i.val)

@[simp] theorem mem_maskSlots {rank mask : ℕ} (i : Fin rank) :
    i ∈ maskSlots rank mask ↔ Nat.testBit mask i.val = true := by
  simp [maskSlots]

theorem sum_maskSlots {rank mask : ℕ} {α : Type*} [AddCommMonoid α] (f : Fin rank → α) :
    (∑ i ∈ maskSlots rank mask, f i) =
      ∑ i, if Nat.testBit mask i.val then f i else 0 := by
  simp [maskSlots, Finset.sum_filter]

/-- Exact unsigned17-byte fourth wire ABI: loLE16*4, hiLE16*4, maskU8. -/
structure FourthWireRow where
  lo : Fin 4 → ℕ
  hi : Fin 4 → ℕ
  mask : ℕ

/-- The original fourth producer endpoints are on lattice204800. -/
def FourthWireRow.toProducerRow (r : FourthWireRow) :
    P2OriginalFourthCapProducerInterface.ProducerRow := ⟨r.lo, r.hi, r.mask⟩

@[simp] theorem fourth_selected (r : FourthWireRow) :
    r.toProducerRow.selected = maskSlots 4 r.mask := rfl

@[simp] theorem fourth_lower (r : FourthWireRow) (i : Fin 4) :
    r.toProducerRow.lower i = (r.lo i : ℚ) / 204800 := rfl

@[simp] theorem fourth_upper (r : FourthWireRow) (i : Fin 4) :
    r.toProducerRow.upper i = (r.hi i : ℚ) / 204800 := rfl

theorem fourth_box (r : FourthWireRow) (t : Fin 4 → ℝ) :
    t ∈ r.toProducerRow.box ↔
      (∀ i, (r.lo i : ℝ) / 204800 ≤ t i) ∧
        (∀ i, t i ≤ (r.hi i : ℝ) / 204800) := by
  simp [P2OriginalFourthCapProducerInterface.ProducerRow.box,
    P2OriginalFourthCapProducerInterface.ProducerRow.lower,
    P2OriginalFourthCapProducerInterface.ProducerRow.upper, FourthWireRow.toProducerRow]

/-- Exact signed-int64 fifth wire ABI in the saved order. The last three
statistics are opaque, and no constant cap or parent/history is decoded. -/
structure FifthWireRow where
  grid : ℤ
  lo : Fin 5 → ℤ
  mask : ℤ
  vertexGapSum : ℤ
  ratioA : ℤ
  ratioB : ℤ

def FifthWireRow.lower (r : FifthWireRow) (i : Fin 5) : ℚ := (r.lo i : ℚ) / (r.grid : ℚ)
def FifthWireRow.upper (r : FifthWireRow) (i : Fin 5) : ℚ := ((r.lo i : ℚ) + 1) / (r.grid : ℚ)

def FifthWireRow.originalBox (r : FifthWireRow) : Set (Fin 5 → ℝ) :=
  {t | ∀ i, (r.lower i : ℝ) ≤ t i ∧ t i < (r.upper i : ℝ)}

/-- Exact rational containment of a candidate original mesh cell in the
saved1/grid box. This accommodates differing original mesh widths. -/
def fifthCellContained (r : FifthWireRow) (m : ℕ) (j : Fin 5 → Fin (m + 1)) : Prop :=
  ∀ i, r.lower i ≤ qLogPrimeMeshLo 0 (19 / 96) m j i ∧
    qLogPrimeMeshHi 0 (19 / 96) m j i ≤ r.upper i

noncomputable section
open scoped Classical
open P1OriginalVariableFifthContinuation

/-- Total conservative decoder. Invalid signed grids/masks decode to no
rows. A valid saved box can contain many, one, or no cells at this mesh. -/
def decodeFifthRows (r : FifthWireRow) (m : ℕ) : Finset (FifthRow m) :=
  if 0 < r.grid ∧ 0 ≤ r.mask then
    (Finset.univ.filter (fifthCellContained r m)).image
      (fun j => ({cell := j, selected := maskSlots 5 r.mask.toNat} : FifthRow m))
  else ∅

theorem mem_decodeFifthRows_iff (raw : FifthWireRow) (m : ℕ) (r : FifthRow m) :
    r ∈ decodeFifthRows raw m ↔
      0 < raw.grid ∧ 0 ≤ raw.mask ∧ ∃ j,
        fifthCellContained raw m j ∧
          r = ({cell := j, selected := maskSlots 5 raw.mask.toNat} : FifthRow m) := by
  unfold decodeFifthRows
  by_cases hvalid : 0 < raw.grid ∧ 0 ≤ raw.mask
  · rw [if_pos hvalid]
    constructor
    · intro hr
      obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hr
      exact ⟨hvalid.1, hvalid.2, j, (Finset.mem_filter.mp hj).2, heq.symm⟩
    · rintro ⟨_hg, _hm, j, hj, rfl⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
  · rw [if_neg hvalid]
    simp only [Finset.not_mem_empty, false_iff]
    rintro ⟨hg, hm, _⟩
    exact hvalid ⟨hg, hm⟩

theorem decodeFifthRows_selected_eq (raw : FifthWireRow) (m : ℕ) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows raw m) : r.selected = maskSlots 5 raw.mask.toNat := by
  obtain ⟨_hg, _hm, j, _hj, rfl⟩ := (mem_decodeFifthRows_iff raw m r).mp hr
  rfl

theorem decodeFifthRows_source_geometry (raw : FifthWireRow) (m : ℕ) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows raw m) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    0 < raw.grid ∧ 0 ≤ raw.mask ∧
      r.selected = maskSlots 5 raw.mask.toNat ∧ t ∈ raw.originalBox := by
  obtain ⟨hg, hm, j, hj, rfl⟩ := (mem_decodeFifthRows_iff raw m r).mp hr
  refine ⟨hg, hm, rfl, ?_⟩
  intro i
  have hc := mem_logPrimeMeshCell.mp ht i
  have hlo : (raw.lower i : ℝ) ≤ logPrimeMeshLo 0 (19 / 96) m j i := by
    have hq : (raw.lower i : ℝ) ≤ (qLogPrimeMeshLo 0 (19 / 96) m j i : ℝ) :=
      Rat.cast_le.mpr (hj i).1
    simpa only [congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m j) i] using hq
  have hhi : logPrimeMeshHi 0 (19 / 96) m j i ≤ (raw.upper i : ℝ) := by
    have hq : (qLogPrimeMeshHi 0 (19 / 96) m j i : ℝ) ≤ (raw.upper i : ℝ) :=
      Rat.cast_le.mpr (hj i).2
    simpa only [congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m j) i] using hq
  exact ⟨hlo.trans hc.1, hc.2.trans_le hhi⟩

/-- This filtered mathematical family is licensed by the actual rational
gateCheck. No assertion that the full saved payload passes is made. -/
def checkedFifthRows (raw : FifthWireRow) (m : ℕ) (e : ℚ) : Finset (FifthRow m) :=
  (decodeFifthRows raw m).filter (fun r => gateCheck e m r = true)

theorem checkedFifthRows_sound (raw : FifthWireRow) (m : ℕ) (e : ℚ) (r : FifthRow m)
    (hr : r ∈ checkedFifthRows raw m e) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    t ∈ raw.originalBox ∧ r.selected = maskSlots 5 raw.mask.toNat ∧
      (1 / 2 : ℝ) < candidate (e : ℝ) r.selected t ∧
      (∀ k, prefixSquareExpr t k < candidate (e : ℝ) r.selected t) ∧
      (∀ k ∉ r.selected, selectedSquareExpr r.selected t k < candidate (e : ℝ) r.selected t) := by
  obtain ⟨hraw, hcheck⟩ := Finset.mem_filter.mp hr
  have hs := decodeFifthRows_source_geometry raw m r hraw t ht
  exact ⟨hs.2.2.2, hs.2.2.1, gateCheck_sound e m r t hcheck ht⟩

/-- Whole-cell selected original owner tests are still separate from raw
row containment. Supplying the actual selected-owner membership gives the
literal original rawQ3 selection, not an ordinary surrogate parent. -/
theorem checkedFifthRows_original_eligible (raw : FifthWireRow) (m : ℕ) (e : ℚ)
    (chi omega : ℝ) (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (r : FifthRow m) (hr : r ∈ checkedFifthRows raw m e)
    (howner : r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    eligible e chi m omega J5 r t :=
  ⟨howner, (Finset.mem_filter.mp hr).2, ht⟩

end
end ImbalancedChen.P1OriginalPrefixRowDecodeSoundness