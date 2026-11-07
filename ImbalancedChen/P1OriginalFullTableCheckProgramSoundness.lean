import ImbalancedChen.P1OriginalFullTableActualProducerAdapter

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Finite table-check programs and their generic soundness. No program is
executed on the archived payload; no actual whole-table success is asserted.
The fifth program checks supplied actual mesh rows. Constructing them,
and the independent original parent/owner licence, are not synthesized
from the saved opaque statistics. No #eval or concrete witness is included.
-/

namespace ImbalancedChen.P1OriginalFullTableCheckProgramSoundness
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalPrefixRowFiniteCheckSoundness
open P2OriginalFourthCapProducerInterface

def fourthTableGeometryCheck (records : List FourthWireRow) : Bool :=
  records.all fourthGeometryCheck

theorem fourthTableGeometryCheck_iff (records : List FourthWireRow) :
    fourthTableGeometryCheck records = true ↔
      ∀ raw ∈ records, fourthGeometryCheck raw = true := by
  simp [fourthTableGeometryCheck]

def fifthTableCellGateCheck (m : ℕ) (e : ℚ)
    (rows : List (P1OriginalVariableFifthContinuation.FifthRow m)) : Bool :=
  rows.all (P1OriginalVariableFifthContinuation.gateCheck e m)

theorem fifthTableCellGateCheck_iff (m : ℕ) (e : ℚ)
    (rows : List (P1OriginalVariableFifthContinuation.FifthRow m)) :
    fifthTableCellGateCheck m e rows = true ↔
      ∀ r ∈ rows, P1OriginalVariableFifthContinuation.gateCheck e m r = true := by
  simp [fifthTableCellGateCheck]

noncomputable section
open scoped Classical
open P1OriginalFullTableActualProducerAdapter

theorem fourthTableGeometryCheck_sound (records : List FourthWireRow)
    (hc : fourthTableGeometryCheck records = true) (r : ProducerRow)
    (hr : r ∈ fourthFamily records) : r.Geometry :=
  fourthFamily_geometry records ((fourthTableGeometryCheck_iff records).mp hc) r hr

/-- If the complete check later passes, filtering drops no policy row.
This implication does not claim the archived input actually passed. -/
theorem wholeFourthPass_preserves_family (records : List FourthWireRow)
    (hc : fourthTableGeometryCheck records = true) :
    fourthFamily records = checkedFourthRows records := by
  have hall := (fourthTableGeometryCheck_iff records).mp hc
  have hfilter : records.toFinset.filter (fun raw => fourthGeometryCheck raw = true) =
      records.toFinset := by
    apply Finset.filter_eq_self.mpr
    intro raw hraw
    exact hall raw (List.mem_toFinset.mp hraw)
  simp only [fourthFamily_eq_finite_decoder, checkedFourthRows, checkedFourthFamily, hfilter]

/-- Rational passing gates and the ACTUAL original source owner together
give fifth eligibility. Neither condition is encoded by gap/A/B statistics. -/
theorem fifthTableCellGateCheck_original_eligible
    (m : ℕ) (e : ℚ) (chi omega : ℝ)
    (rows : List (P1OriginalVariableFifthContinuation.FifthRow m))
    (hc : fifthTableCellGateCheck m e rows = true)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (r : P1OriginalVariableFifthContinuation.FifthRow m) (hr : r ∈ rows)
    (howner : r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    P1OriginalVariableFifthContinuation.eligible e chi m omega J5 r t :=
  ⟨howner, (fifthTableCellGateCheck_iff m e rows).mp hc r hr, ht⟩

end
end ImbalancedChen.P1OriginalFullTableCheckProgramSoundness
