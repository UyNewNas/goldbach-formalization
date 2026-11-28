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


/-- The same original block reader on a fixed contiguous byte interval.
Each private declaration remains within the unchanged per-command budget. -/
elab "include_original_sixth_part% " path:str offset:num size:num : term => do
  let sourceFile := System.FilePath.mk (← getFileName)
  let raw ← IO.FS.readBinFile (sourceFile.withFileName path.getString)
  if raw.size != 55625280 then
    throwError "original sixth cells.npy must contain 55625280 bytes; found {raw.size}"
  let firstByte := offset.getNat
  let byteCount := size.getNat
  unless firstByte % 256 == 0 && decide (firstByte + byteCount ≤ raw.size) do
    throwError "invalid original sixth byte partition"
  let mut layer : Array Expr := #[]
  for leaf in [: (byteCount + 255) / 256] do
    let start := firstByte + 256 * leaf
    let count := min 256 (byteCount - 256 * leaf)
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

private def originalPart000 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 0 1048576

private theorem originalPart000_length : originalPart000.byteLength = 1048576 := by decide

private def originalPart001 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 1048576 1048576

private theorem originalPart001_length : originalPart001.byteLength = 1048576 := by decide

private def originalPart002 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 2097152 1048576

private theorem originalPart002_length : originalPart002.byteLength = 1048576 := by decide

private def originalPart003 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 3145728 1048576

private theorem originalPart003_length : originalPart003.byteLength = 1048576 := by decide

private def originalPart004 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 4194304 1048576

private theorem originalPart004_length : originalPart004.byteLength = 1048576 := by decide

private def originalPart005 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 5242880 1048576

private theorem originalPart005_length : originalPart005.byteLength = 1048576 := by decide

private def originalPart006 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 6291456 1048576

private theorem originalPart006_length : originalPart006.byteLength = 1048576 := by decide

private def originalPart007 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 7340032 1048576

private theorem originalPart007_length : originalPart007.byteLength = 1048576 := by decide

private def originalPart008 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 8388608 1048576

private theorem originalPart008_length : originalPart008.byteLength = 1048576 := by decide

private def originalPart009 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 9437184 1048576

private theorem originalPart009_length : originalPart009.byteLength = 1048576 := by decide

private def originalPart010 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 10485760 1048576

private theorem originalPart010_length : originalPart010.byteLength = 1048576 := by decide

private def originalPart011 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 11534336 1048576

private theorem originalPart011_length : originalPart011.byteLength = 1048576 := by decide

private def originalPart012 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 12582912 1048576

private theorem originalPart012_length : originalPart012.byteLength = 1048576 := by decide

private def originalPart013 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 13631488 1048576

private theorem originalPart013_length : originalPart013.byteLength = 1048576 := by decide

private def originalPart014 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 14680064 1048576

private theorem originalPart014_length : originalPart014.byteLength = 1048576 := by decide

private def originalPart015 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 15728640 1048576

private theorem originalPart015_length : originalPart015.byteLength = 1048576 := by decide

private def originalPart016 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 16777216 1048576

private theorem originalPart016_length : originalPart016.byteLength = 1048576 := by decide

private def originalPart017 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 17825792 1048576

private theorem originalPart017_length : originalPart017.byteLength = 1048576 := by decide

private def originalPart018 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 18874368 1048576

private theorem originalPart018_length : originalPart018.byteLength = 1048576 := by decide

private def originalPart019 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 19922944 1048576

private theorem originalPart019_length : originalPart019.byteLength = 1048576 := by decide

private def originalPart020 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 20971520 1048576

private theorem originalPart020_length : originalPart020.byteLength = 1048576 := by decide

private def originalPart021 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 22020096 1048576

private theorem originalPart021_length : originalPart021.byteLength = 1048576 := by decide

private def originalPart022 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 23068672 1048576

private theorem originalPart022_length : originalPart022.byteLength = 1048576 := by decide

private def originalPart023 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 24117248 1048576

private theorem originalPart023_length : originalPart023.byteLength = 1048576 := by decide

private def originalPart024 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 25165824 1048576

private theorem originalPart024_length : originalPart024.byteLength = 1048576 := by decide

private def originalPart025 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 26214400 1048576

private theorem originalPart025_length : originalPart025.byteLength = 1048576 := by decide

private def originalPart026 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 27262976 1048576

private theorem originalPart026_length : originalPart026.byteLength = 1048576 := by decide

private def originalPart027 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 28311552 1048576

private theorem originalPart027_length : originalPart027.byteLength = 1048576 := by decide

private def originalPart028 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 29360128 1048576

private theorem originalPart028_length : originalPart028.byteLength = 1048576 := by decide

private def originalPart029 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 30408704 1048576

private theorem originalPart029_length : originalPart029.byteLength = 1048576 := by decide

private def originalPart030 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 31457280 1048576

private theorem originalPart030_length : originalPart030.byteLength = 1048576 := by decide

private def originalPart031 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 32505856 1048576

private theorem originalPart031_length : originalPart031.byteLength = 1048576 := by decide

private def originalPart032 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 33554432 1048576

private theorem originalPart032_length : originalPart032.byteLength = 1048576 := by decide

private def originalPart033 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 34603008 1048576

private theorem originalPart033_length : originalPart033.byteLength = 1048576 := by decide

private def originalPart034 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 35651584 1048576

private theorem originalPart034_length : originalPart034.byteLength = 1048576 := by decide

private def originalPart035 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 36700160 1048576

private theorem originalPart035_length : originalPart035.byteLength = 1048576 := by decide

private def originalPart036 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 37748736 1048576

private theorem originalPart036_length : originalPart036.byteLength = 1048576 := by decide

private def originalPart037 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 38797312 1048576

private theorem originalPart037_length : originalPart037.byteLength = 1048576 := by decide

private def originalPart038 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 39845888 1048576

private theorem originalPart038_length : originalPart038.byteLength = 1048576 := by decide

private def originalPart039 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 40894464 1048576

private theorem originalPart039_length : originalPart039.byteLength = 1048576 := by decide

private def originalPart040 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 41943040 1048576

private theorem originalPart040_length : originalPart040.byteLength = 1048576 := by decide

private def originalPart041 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 42991616 1048576

private theorem originalPart041_length : originalPart041.byteLength = 1048576 := by decide

private def originalPart042 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 44040192 1048576

private theorem originalPart042_length : originalPart042.byteLength = 1048576 := by decide

private def originalPart043 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 45088768 1048576

private theorem originalPart043_length : originalPart043.byteLength = 1048576 := by decide

private def originalPart044 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 46137344 1048576

private theorem originalPart044_length : originalPart044.byteLength = 1048576 := by decide

private def originalPart045 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 47185920 1048576

private theorem originalPart045_length : originalPart045.byteLength = 1048576 := by decide

private def originalPart046 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 48234496 1048576

private theorem originalPart046_length : originalPart046.byteLength = 1048576 := by decide

private def originalPart047 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 49283072 1048576

private theorem originalPart047_length : originalPart047.byteLength = 1048576 := by decide

private def originalPart048 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 50331648 1048576

private theorem originalPart048_length : originalPart048.byteLength = 1048576 := by decide

private def originalPart049 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 51380224 1048576

private theorem originalPart049_length : originalPart049.byteLength = 1048576 := by decide

private def originalPart050 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 52428800 1048576

private theorem originalPart050_length : originalPart050.byteLength = 1048576 := by decide

private def originalPart051 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 53477376 1048576

private theorem originalPart051_length : originalPart051.byteLength = 1048576 := by decide

private def originalPart052 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 54525952 1048576

private theorem originalPart052_length : originalPart052.byteLength = 1048576 := by decide

private def originalPart053 : ByteLiteral :=
  include_original_sixth_part% "provenance/OriginalSixthCells.npy" 55574528 50752

private theorem originalPart053_length : originalPart053.byteLength = 50752 := by decide

def originalLiteral : ByteLiteral :=
  (ByteLiteral.node (ByteLiteral.node (ByteLiteral.node (ByteLiteral.node (ByteLiteral.node (ByteLiteral.node originalPart000 originalPart001) (ByteLiteral.node originalPart002 originalPart003)) (ByteLiteral.node (ByteLiteral.node originalPart004 originalPart005) (ByteLiteral.node originalPart006 originalPart007))) (ByteLiteral.node (ByteLiteral.node (ByteLiteral.node originalPart008 originalPart009) (ByteLiteral.node originalPart010 originalPart011)) (ByteLiteral.node (ByteLiteral.node originalPart012 originalPart013) (ByteLiteral.node originalPart014 originalPart015)))) (ByteLiteral.node (ByteLiteral.node (ByteLiteral.node (ByteLiteral.node originalPart016 originalPart017) (ByteLiteral.node originalPart018 originalPart019)) (ByteLiteral.node (ByteLiteral.node originalPart020 originalPart021) (ByteLiteral.node originalPart022 originalPart023))) (ByteLiteral.node (ByteLiteral.node (ByteLiteral.node originalPart024 originalPart025) (ByteLiteral.node originalPart026 originalPart027)) (ByteLiteral.node (ByteLiteral.node originalPart028 originalPart029) (ByteLiteral.node originalPart030 originalPart031))))) (ByteLiteral.node (ByteLiteral.node (ByteLiteral.node (ByteLiteral.node (ByteLiteral.node originalPart032 originalPart033) (ByteLiteral.node originalPart034 originalPart035)) (ByteLiteral.node (ByteLiteral.node originalPart036 originalPart037) (ByteLiteral.node originalPart038 originalPart039))) (ByteLiteral.node (ByteLiteral.node (ByteLiteral.node originalPart040 originalPart041) (ByteLiteral.node originalPart042 originalPart043)) (ByteLiteral.node (ByteLiteral.node originalPart044 originalPart045) (ByteLiteral.node originalPart046 originalPart047)))) (ByteLiteral.node (ByteLiteral.node (ByteLiteral.node originalPart048 originalPart049) (ByteLiteral.node originalPart050 originalPart051)) (ByteLiteral.node originalPart052 originalPart053))))

def originalBytes : List ℕ := originalLiteral.bytes

theorem original_length : originalLiteral.byteLength = 55625280 := by
  have glue {left right : ByteLiteral} {m n : Nat}
      (hl : left.byteLength = m) (hr : right.byteLength = n) :
      (ByteLiteral.node left right).byteLength = m + n :=
    congrArg₂ Nat.add hl hr
  exact (glue (glue (glue (glue (glue (glue originalPart000_length originalPart001_length) (glue originalPart002_length originalPart003_length)) (glue (glue originalPart004_length originalPart005_length) (glue originalPart006_length originalPart007_length))) (glue (glue (glue originalPart008_length originalPart009_length) (glue originalPart010_length originalPart011_length)) (glue (glue originalPart012_length originalPart013_length) (glue originalPart014_length originalPart015_length)))) (glue (glue (glue (glue originalPart016_length originalPart017_length) (glue originalPart018_length originalPart019_length)) (glue (glue originalPart020_length originalPart021_length) (glue originalPart022_length originalPart023_length))) (glue (glue (glue originalPart024_length originalPart025_length) (glue originalPart026_length originalPart027_length)) (glue (glue originalPart028_length originalPart029_length) (glue originalPart030_length originalPart031_length))))) (glue (glue (glue (glue (glue originalPart032_length originalPart033_length) (glue originalPart034_length originalPart035_length)) (glue (glue originalPart036_length originalPart037_length) (glue originalPart038_length originalPart039_length))) (glue (glue (glue originalPart040_length originalPart041_length) (glue originalPart042_length originalPart043_length)) (glue (glue originalPart044_length originalPart045_length) (glue originalPart046_length originalPart047_length)))) (glue (glue (glue originalPart048_length originalPart049_length) (glue originalPart050_length originalPart051_length)) (glue originalPart052_length originalPart053_length))))

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
  dsimp only [oldPlane]
  split_ifs
  · rw [v_eq_min]; exact min_le_left _ _
  · rw [v_eq_min]; exact min_le_right _ _
  · exact v_le_cap _

end
end ImbalancedChen.P4AOriginalSavedSixthArchive
