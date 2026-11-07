import ImbalancedChen.P1OriginalPrefixRowDecodeSoundness
import Mathlib.Tactic.FinCases

/-!
Lossless signed-column parser and lawful finite-table fifth-row decoder.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

All ten saved integers are retained. GapSum/A/B remain opaque. A decoded
physical row is a genuinely contained original mesh cell, using the source
mask's zero-based processing slots. Differing grids are never identified.
No dynamic parent, e/chi/omega, licence, constant cap or gain is synthesized.
The full historical table is an opt-in data archive and is not imported.
-/

namespace ImbalancedChen.P1HistoricalFifthTableParser
noncomputable section
open scoped Classical
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation

abbrev SavedColumns := Fin 10 → ℤ

def lowerColumn (i : Fin 5) : Fin 10 := ⟨i.val + 1, by omega⟩

/-- Literal [n,l1,l2,l3,l4,l5,mask,vertex_gap_sum,A,B] decoder. -/
def wireOfColumns (c : SavedColumns) : FifthWireRow :=
  ⟨c 0, ![c 1, c 2, c 3, c 4, c 5], c 6, c 7, c 8, c 9⟩

def wireColumns (r : FifthWireRow) : SavedColumns :=
  ![r.grid, r.lo 0, r.lo 1, r.lo 2, r.lo 3, r.lo 4,
    r.mask, r.vertexGapSum, r.ratioA, r.ratioB]

theorem wireColumns_wireOfColumns (c : SavedColumns) : wireColumns (wireOfColumns c) = c := by
  funext i
  fin_cases i <;> rfl

theorem wireOfColumns_wireColumns (r : FifthWireRow) : wireOfColumns (wireColumns r) = r := by
  rcases r with ⟨grid, lo, mask, gap, ratioA, ratioB⟩
  have hlo : (![lo 0, lo 1, lo 2, lo 3, lo 4] : Fin 5 → ℤ) = lo := by
    funext i
    fin_cases i <;> rfl
  change (⟨grid, ![lo 0, lo 1, lo 2, lo 3, lo 4], mask, gap, ratioA, ratioB⟩ : FifthWireRow) =
    ⟨grid, lo, mask, gap, ratioA, ratioB⟩
  rw [hlo]

@[simp] theorem wireOfColumns_lo (c : SavedColumns) (i : Fin 5) :
    (wireOfColumns c).lo i = c (lowerColumn i) := by
  fin_cases i <;> rfl

/-- Every signed field survives roundtrip, including all opaque statistics. -/
theorem wire_field_semantics (c : SavedColumns) :
    (wireOfColumns c).grid = c 0 ∧ (wireOfColumns c).mask = c 6 ∧
      (wireOfColumns c).vertexGapSum = c 7 ∧ (wireOfColumns c).ratioA = c 8 ∧
        (wireOfColumns c).ratioB = c 9 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Total conservative physical decoder: invalid signed grid/mask rows
produce no FifthRows. Rational containment handles differing mesh grids. -/
def decodeColumns (c : SavedColumns) (m : ℕ) : Finset (FifthRow m) :=
  decodeFifthRows (wireOfColumns c) m

theorem decodeColumns_sound (c : SavedColumns) (m : ℕ) (r : FifthRow m)
    (hr : r ∈ decodeColumns c m) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    0 < c 0 ∧ 0 ≤ c 6 ∧ r.selected = maskSlots 5 (c 6).toNat ∧
      t ∈ (wireOfColumns c).originalBox := by
  exact decodeFifthRows_source_geometry (wireOfColumns c) m r hr t ht

/-- Slot i keeps its source bit i; masks are never reversed or resorted. -/
theorem decodeColumns_selected_slot (c : SavedColumns) (m : ℕ) (r : FifthRow m)
    (hr : r ∈ decodeColumns c m) (i : Fin 5) :
    i ∈ r.selected ↔ Nat.testBit (c 6).toNat i.val = true := by
  rw [decodeFifthRows_selected_eq (wireOfColumns c) m r hr]
  exact mem_maskSlots i

/-- Table decoding is a finite union over the loaded raw rows. This code
is independent of the historical table's size and performs no replay. -/
def decodeTableAt (raw : Array FifthWireRow) (m : ℕ) : Finset (FifthRow m) :=
  raw.toList.toFinset.biUnion (fun wire => decodeFifthRows wire m)

theorem mem_decodeTableAt (raw : Array FifthWireRow) (m : ℕ) (r : FifthRow m) :
    r ∈ decodeTableAt raw m ↔ ∃ wire ∈ raw.toList, r ∈ decodeFifthRows wire m := by
  simp only [decodeTableAt, Finset.mem_biUnion, List.mem_toFinset]

theorem decodeTableAt_source_geometry (raw : Array FifthWireRow) (m : ℕ) (r : FifthRow m)
    (hr : r ∈ decodeTableAt raw m) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    ∃ wire ∈ raw.toList, 0 < wire.grid ∧ 0 ≤ wire.mask ∧
      r.selected = maskSlots 5 wire.mask.toNat ∧ t ∈ wire.originalBox := by
  obtain ⟨wire, hwire, hrow⟩ := (mem_decodeTableAt raw m r).mp hr
  exact ⟨wire, hwire, decodeFifthRows_source_geometry wire m r hrow t ht⟩

/-- This family applies the actual rational gateCheck as a mathematical
filter. No claim that the historical table passes it has been evaluated. -/
def checkedTableAt (raw : Array FifthWireRow) (m : ℕ) (e : ℚ) : Finset (FifthRow m) :=
  raw.toList.toFinset.biUnion (fun wire => checkedFifthRows wire m e)

theorem checkedTableAt_sound (raw : Array FifthWireRow) (m : ℕ) (e : ℚ) (r : FifthRow m)
    (hr : r ∈ checkedTableAt raw m e) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    ∃ wire ∈ raw.toList, t ∈ wire.originalBox ∧
      r.selected = maskSlots 5 wire.mask.toNat ∧
        (1 / 2 : ℝ) < candidate (e : ℝ) r.selected t ∧
        (∀ k, prefixSquareExpr t k < candidate (e : ℝ) r.selected t) ∧
        (∀ k ∉ r.selected, selectedSquareExpr r.selected t k < candidate (e : ℝ) r.selected t) := by
  obtain ⟨wire, hwire, hrow⟩ := Finset.mem_biUnion.mp hr
  exact ⟨wire, List.mem_toFinset.mp hwire, checkedFifthRows_sound wire m e r hrow t ht⟩

/-- Actual original-owner eligibility remains an explicit independent
policy input. Raw saved geometry never invents the missing parent/rough
licence or a passing whole-table witness. -/
theorem checkedTableAt_original_eligible (raw : Array FifthWireRow) (m : ℕ) (e : ℚ)
    (chi omega : ℝ) (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (r : FifthRow m) (hr : r ∈ checkedTableAt raw m e)
    (howner : r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    eligible e chi m omega J5 r t := by
  obtain ⟨wire, _hwire, hrow⟩ := Finset.mem_biUnion.mp hr
  exact checkedFifthRows_original_eligible wire m e chi omega J5 r hrow howner t ht

end
end ImbalancedChen.P1HistoricalFifthTableParser


