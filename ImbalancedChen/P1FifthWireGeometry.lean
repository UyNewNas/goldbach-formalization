import ImbalancedChen.P1FifthRowGeometry

/-! Shared exact geometric declarations; selected verification is recorded separately. -/
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
    simp only [Finset.notMem_empty, false_iff]
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
    simpa [congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m j) i] using hq
  have hhi : logPrimeMeshHi 0 (19 / 96) m j i ≤ (raw.upper i : ℝ) := by
    have hq : (qLogPrimeMeshHi 0 (19 / 96) m j i : ℝ) ≤ (raw.upper i : ℝ) :=
      Rat.cast_le.mpr (hj i).2
    simpa [congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m j) i] using hq
  exact ⟨hlo.trans hc.1, hc.2.trans_le hhi⟩

end
end ImbalancedChen.P1OriginalPrefixRowDecodeSoundness
