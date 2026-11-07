import ImbalancedChen.P1HistoricalFifthOriginalByteLiteral
import ImbalancedChen.P1OriginalFourthPackedParserCompleteness
import ImbalancedChen.P1OriginalFourthIntegerGeometryAdmission
import ImbalancedChen.P1HistoricalFifthCommonPolicyInputs

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Concrete ORIGINAL fourth and fifth inputs, not parameters for an arbitrary
bank. The fourth fixture is the unchanged 17-byte original-row payload:
SHA256 561f5dc9ff2f6d64ba739de830511f6f68bf1f7be0c724655a8435c7edb914da.
The fifth input is the already archived 292633-row owner construction.

The include elaborator is only a file-to-transparent-term reader. It is
not run during authoring. Its one closed length proof is UNEVALUATED.
The geometry filter is a bare source admission test; no analytic H/h
count licence is inferred from it. The input below instantiates the held
common constructor, whose eleven-cell sixth stage is not the complete
original sixth schedule and whose eighth guard is not the original87.
-/
namespace ImbalancedChen.P5OriginalFourthFifthSourceInputs

open Lean Elab Term
open P1HistoricalFifthOriginalByteLiteral

elab "include_original_fourth_bytes% " path:str : term => do
  let sourceFile := System.FilePath.mk (← getFileName)
  let raw ← IO.FS.readBinFile (sourceFile.withFileName path.getString)
  if raw.size != 62885159 then
    throwError "original fourth payload must contain 62885159 bytes; found {raw.size}"
  let mut layer : Array Expr := #[]
  for leaf in [: (raw.size + 255) / 256] do
    let start := 256 * leaf
    let count := min 256 (raw.size - start)
    let mut packed : Nat := 0
    for digit in [:count] do
      packed := 256 * packed + (raw.get! (start + count - 1 - digit)).toNat
    layer := layer.push <| mkApp2 (mkConst ``ByteLiteral.block)
      (mkNatLit count) (mkNatLit packed)
  while 1 < layer.size do
    let mut next : Array Expr := #[]
    for pair in [: (layer.size + 1) / 2] do
      let left := layer[2 * pair]!
      if 2 * pair + 1 < layer.size then
        next := next.push <| mkApp2 (mkConst ``ByteLiteral.node) left layer[2 * pair + 1]!
      else
        next := next.push left
    layer := next
  if layer.isEmpty then return mkConst ``ByteLiteral.empty else return layer[0]!

noncomputable section
open scoped Classical
open P1OriginalFourthPackedTable P1OriginalFourthPackedParserCompleteness
open P1OriginalFourthIntegerGeometryAdmission P2OriginalFourthCapProducerInterface

def originalFourthLiteral : ByteLiteral :=
  include_original_fourth_bytes% "provenance/original-fourth/FourthRows17LE.bin"

def originalFourthBytes : List Nat := originalFourthLiteral.bytes

/-- UNEVALUATED structural length guard, not a row-geometry check. -/
theorem originalFourthLiteral_length :
    originalFourthLiteral.byteLength = 62885159 := by decide

theorem originalFourthBytes_length : originalFourthBytes.length = 62885159 := by
  rw [originalFourthBytes, ByteLiteral.bytes_length, originalFourthLiteral_length]

theorem originalFourthBytes_valid : ValidBytes originalFourthBytes :=
  originalFourthLiteral.bytes_bound

theorem originalFourth_parse_exists :
    ∃ rows : List FourthWireRow, decodeWireRows originalFourthBytes = some rows := by
  apply decodeWireRows_complete
  rw [originalFourthBytes_length]
  exact ⟨3699127, by norm_num⟩

/-- There is no empty-bank fallback on a failed parse. -/
def originalFourthWireRows : List FourthWireRow :=
  Classical.choose originalFourth_parse_exists

theorem originalFourth_parse :
    decodeWireRows originalFourthBytes = some originalFourthWireRows :=
  Classical.choose_spec originalFourth_parse_exists

theorem originalFourth_wire_source :
    (∀ r ∈ originalFourthWireRows, UnsignedRow r) ∧
      originalFourthWireRows.length = 3699127 ∧
      encodeRows originalFourthWireRows = originalFourthBytes := by
  obtain ⟨hu, hl, he⟩ := decodeWireRows_sound _ _ originalFourthBytes_valid originalFourth_parse
  rw [originalFourthBytes_length] at hl
  exact ⟨hu, by omega, he⟩

def originalRows4 : Finset ProducerRow :=
  (originalFourthWireRows.map FourthWireRow.toProducerRow).toFinset

/-- Original integer geometry is an explicit test, not an arbitrary licence. -/
def originalAdmission4 (r : ProducerRow) : Prop :=
  ∃ raw ∈ originalFourthWireRows,
    raw.toProducerRow = r ∧ integerGeometryAccept raw = true

theorem originalRows4_source (r : ProducerRow) :
    r ∈ originalRows4 ↔ ∃ raw ∈ originalFourthWireRows, raw.toProducerRow = r := by
  simp only [originalRows4, List.mem_toFinset, List.mem_map]

theorem originalAdmission4_geometry (r : ProducerRow) (hr : originalAdmission4 r) :
    r.Geometry := by
  obtain ⟨raw, _, rfl, hg⟩ := hr
  exact integerGeometryAccept_geometry raw hg

theorem originalAdmission4_mem (r : ProducerRow) (hr : originalAdmission4 r) :
    r ∈ originalRows4 := by
  obtain ⟨raw, hm, he, _⟩ := hr
  exact (originalRows4_source r).mpr ⟨raw, hm, he⟩

/-- Concrete original banks. Only the legitimate pre-N hierarchy parameters
remain free. This is deliberately called heldData: no full-sixth or full87
claim is hidden in the name of this source instantiation. -/
def heldData (e : ℚ) (q : Nat) (chi omega : ℝ) :
    P5OriginalCommonRefinedConstructor.OriginalData :=
  P1HistoricalFifthCommonPolicyInputs.sourceData originalRows4 originalAdmission4 e q chi omega

theorem heldData_fourth (e : ℚ) (q : Nat) (chi omega : ℝ) :
    (heldData e q chi omega).rows4 = originalRows4 ∧
      (heldData e q chi omega).licensed4 = originalAdmission4 := ⟨rfl, rfl⟩

theorem heldData_fifth (e : ℚ) (q : Nat) (chi omega : ℝ) :
    (heldData e q chi omega).J5 =
      P1HistoricalFifthIndexedOwnerArchive.globalOwners e q chi omega ∧
    (heldData e q chi omega).rows5 =
      P1HistoricalFifthIndexedOwnerArchive.licensedRows e q chi omega := ⟨rfl, rfl⟩

theorem heldData_fifth_source (e : ℚ) (q : Nat) (chi omega : ℝ)
    (r : P1OriginalVariableFifthContinuation.FifthRow
      (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q))
    (hr : r ∈ (heldData e q chi omega).rows5) :
    ∃ i ∈ P1HistoricalFifthIndexedOwnerArchive.licensedIndices,
      r.cell ∈ P1HistoricalFifthIndexedOwnerArchive.licensedOwners i e q chi omega ∧
      r = P1HistoricalFifthIndexedOwnerArchive.sourceOwnerRow i q r.cell ∧
      r ∈ P1OriginalPrefixRowDecodeSoundness.decodeFifthRows
        (P1HistoricalFifthIndexedOwnerArchive.archiveRow i)
        (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) :=
  P1HistoricalFifthCommonPolicyInputs.full_archive_licensed_rows_source
    originalRows4 originalAdmission4 e q chi omega r hr

end
end ImbalancedChen.P5OriginalFourthFifthSourceInputs
