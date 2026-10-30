import ImbalancedChen.P1FifthWireGeometry
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