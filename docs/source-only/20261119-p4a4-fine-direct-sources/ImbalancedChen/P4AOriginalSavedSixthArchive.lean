import ImbalancedChen.P1HistoricalFifthOriginalByteLiteral
import ImbalancedChen.P2OriginalSixthElevenLogSemantics
import ImbalancedChen.P1OriginalVariableFourthContinuation

/-! SOURCE ONLY / UNCOMPILED. Exact original 632104 by 11 signed-i64
cells.npy source; copied byte for byte from the pinned release archive.
The first128 bytes are the ORIGINAL NPY v1 header. No old smaller-grid
witness is added. The three stored budget columns are retained as bytes
but do not enter the policy. Nothing here recomputes a numerical gain.

The transparent-term reader follows the already existing byte-literal
mechanism. It is not evaluated during source authoring. -/
namespace ImbalancedChen.P4AOriginalSavedSixthArchive
open Lean Elab Term
open P1HistoricalFifthOriginalByteLiteral

elab "include_original_sixth_bytes% " path:str : term => do
  let sourceFile := System.FilePath.mk (← getFileName)
  let raw ← IO.FS.readBinFile (sourceFile.withFileName path.getString)
  if raw.size != 55625280 then
    throwError "original sixth cells.npy must contain 55625280 bytes; found {raw.size}"
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
open scoped Classical BigOperators
open VariableEnvelope

def originalLiteral : ByteLiteral :=
  include_original_sixth_bytes% "provenance/OriginalSixthCells.npy"

def originalBytes : List ℕ := originalLiteral.bytes

theorem original_length : originalLiteral.byteLength = 55625280 := by decide

theorem original_bytes_length : originalBytes.length = 128 + 632104 * 11 * 8 := by
  rw [originalBytes, ByteLiteral.bytes_length, original_length]

/-- Exact original NPY v1 header, including <i8, C order and shape(632104,11).
Closed source-byte body, UNEVALUATED; length alone is not used as its proof. -/
def originalHeader : List ℕ := [147, 78, 85, 77, 80, 89, 1, 0, 118, 0, 123, 39, 100, 101, 115, 99, 114, 39, 58, 32, 39, 60, 105, 56, 39, 44, 32, 39, 102, 111, 114, 116, 114, 97, 110, 95, 111, 114, 100, 101, 114, 39, 58, 32, 70, 97, 108, 115, 101, 44, 32, 39, 115, 104, 97, 112, 101, 39, 58, 32, 40, 54, 51, 50, 49, 48, 52, 44, 32, 49, 49, 41, 44, 32, 125, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 10]

theorem original_header : originalBytes.take 128 = originalHeader := by decide

abbrev Row := Fin 632104

/-- NPY C-order signed little-endian64; no decoding failure becomes an
empty source. The file and fixed shape are part of the transparent term. -/
def unsignedWord (i : Row) (column : Fin 11) : ℕ :=
  P1HistoricalFifthSigned64Payload.unsignedLE
    ((originalBytes.drop (128 + 8 * (11 * i.val + column.val))).take 8)

def word (i : Row) (column : Fin 11) : ℤ :=
  let n := unsignedWord i column
  if n < 2^63 then (n : ℤ) else (n : ℤ) - 2^64

def denominator (i : Row) : ℝ := (word i 0 : ℝ)
def lowerCorner (i : Row) (j : Fin 6) : ℝ :=
  (word i ⟨j.val+1, by omega⟩ : ℝ) / denominator i
def upperCorner (i : Row) (j : Fin 6) : ℝ :=
  ((word i ⟨j.val+1, by omega⟩ : ℝ)+1) / denominator i
def selectedMask (i : Row) : ℕ := (word i 7).toNat

def InBox (i : Row) (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) : Prop :=
  ∀ j, lowerCorner i j ≤ t j ∧ t j < upperCorner i j

def midpoint (i : Row) : Certificates.P2OriginalSixthElevenLogSemantics.Physical :=
  fun j => (lowerCorner i j + upperCorner i j) / 2

/-- Original midpoint argmin of A,D,Lambda, with the same first-minimum
tie order. Its selected plane is evaluated on t, never on the midpoint. -/
def oldPlane (i : Row) (mask : ℕ) (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) : ℝ :=
  let s := Certificates.P2OriginalSixthElevenLogSemantics.subsetSum mask (midpoint i)
  if A s ≤ C s ∧ A s ≤ cap then A (Certificates.P2OriginalSixthElevenLogSemantics.subsetSum mask t)
  else if C s ≤ cap then C (Certificates.P2OriginalSixthElevenLogSemantics.subsetSum mask t)
  else cap

def oldUpper (i : Row) (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) : ℝ :=
  P1OriginalVariableFourthContinuation.finiteMax (Finset.Icc 1 31)
    (fun _ => True) (fun m => oldPlane i m t) (Certificates.P2OriginalSixthElevenLogSemantics.W t)

def endpoint (i : Row) (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) : ℝ := v (Certificates.P2OriginalSixthElevenLogSemantics.selectedSum (selectedMask i) t)

/-- The original whole-box geometric tests, applied as own-prefix
admission conditions. Their accepted-table certification is not assumed. -/
def Source (i : Row) (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) : Prop :=
  denominator i = 400 ∧ InBox i t ∧ 32 ≤ selectedMask i ∧ selectedMask i < 64 ∧
    (1 / 50 : ℝ) ≤ t 5 ∧
    (∀ j, Certificates.P2OriginalSixthElevenLogSemantics.fullSquare j t < endpoint i t) ∧
    (∀ j, Certificates.P2OriginalSixthElevenLogSemantics.bit (selectedMask i) j.val = false →
      Certificates.P2OriginalSixthElevenLogSemantics.remainingSquare (selectedMask i) j t < endpoint i t) ∧
    endpoint i t - Certificates.P2OriginalSixthElevenLogSemantics.S6 t ≤ 3 * t 5 ∧ oldUpper i t < endpoint i t

theorem source_mask_range (i : Row) (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) (h : Source i t) :
    selectedMask i ∈ Finset.Icc 1 63 := by
  have hlo := h.2.2.1
  have hhi := h.2.2.2.1
  simp only [Finset.mem_Icc]
  omega

theorem source_endpoint_eq_selected_tent (i : Row) (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) :
    endpoint i t = v (Certificates.P2OriginalSixthElevenLogSemantics.selectedSum (selectedMask i) t) := rfl

theorem old_tent_le_oldPlane (i : Row) (mask : ℕ) (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) :
    v (Certificates.P2OriginalSixthElevenLogSemantics.subsetSum mask t) ≤ oldPlane i mask t := by
  unfold oldPlane
  split_ifs
  · rw [v_eq_min]; exact min_le_left _ _
  · rw [v_eq_min]; exact min_le_right _ _
  · exact v_le_cap _

end
end ImbalancedChen.P4AOriginalSavedSixthArchive
