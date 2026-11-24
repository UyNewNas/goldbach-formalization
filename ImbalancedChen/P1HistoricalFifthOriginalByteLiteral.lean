import Lean
import ImbalancedChen.P1HistoricalFifthSigned64PayloadCompleteness

/-!
SOURCE_ONLY / UNCOMPILED / ZERO CREDIT.

A small include-bytes elaborator. It reads a binary file only when the user
elaborates an application, and returns an ordinary transparent constructor
term. It does not read any typed row, decode NPY, run a decision procedure,
create a theorem, or put an IO action in the resulting mathematical object.
No application of this elaborator was run while authoring this source.

Each leaf is a length and a base-256 natural-number literal for at most256
successive raw bytes. The length preserves all leading/high zero bytes.
The balanced node tree preserves file order and avoids a23-million-deep
literal expression. The kernel expands leaves with the existing pure
encodeNatLE function. Packing a raw byte slice is not re-encoding typed data.
-/
namespace ImbalancedChen.P1HistoricalFifthOriginalByteLiteral
open P1HistoricalFifthSigned64Payload P1HistoricalFifthSigned64PayloadCompleteness

inductive ByteLiteral where
  | empty : ByteLiteral
  | block (count packed : Nat) : ByteLiteral
  | node (left right : ByteLiteral) : ByteLiteral
  deriving Inhabited

noncomputable def ByteLiteral.prependBytes : ByteLiteral → List Nat → List Nat
  | .empty, tail => tail
  | .block count packed, tail => encodeNatLE count packed ++ tail
  | .node left right, tail => left.prependBytes (right.prependBytes tail)

/-- A continuation avoids copying a whole subtree at every node. -/
noncomputable def ByteLiteral.bytes (literal : ByteLiteral) : List Nat :=
  literal.prependBytes []

def ByteLiteral.byteLength : ByteLiteral → Nat
  | .empty => 0
  | .block count _ => count
  | .node left right => left.byteLength + right.byteLength

theorem ByteLiteral.prependBytes_length (literal : ByteLiteral) (tail : List Nat) :
    (literal.prependBytes tail).length = literal.byteLength + tail.length := by
  induction literal generalizing tail with
  | empty => simp [ByteLiteral.prependBytes, ByteLiteral.byteLength]
  | block count packed =>
      exact (List.length_append _ _).trans
        (congrArg (fun n => n + tail.length) (encodeNatLE_length count packed))
  | node left right ihl ihr =>
      change (left.prependBytes (right.prependBytes tail)).length =
        (left.byteLength + right.byteLength) + tail.length
      rw [ihl, ihr, Nat.add_assoc]

theorem ByteLiteral.bytes_length (literal : ByteLiteral) :
    literal.bytes.length = literal.byteLength := by
  simpa only [ByteLiteral.bytes, List.length_nil, Nat.add_zero] using
    literal.prependBytes_length []

theorem ByteLiteral.prependBytes_bound (literal : ByteLiteral) (tail : List Nat)
    (ht : ∀ b ∈ tail, b < 256) : ∀ b ∈ literal.prependBytes tail, b < 256 := by
  induction literal generalizing tail with
  | empty => exact ht
  | block count packed =>
      intro b hb
      rcases List.mem_append.mp hb with hl | hr
      · exact encodeNatLE_byte_bound count packed b hl
      · exact ht b hr
  | node left right ihl ihr => exact ihl _ (ihr tail ht)

theorem ByteLiteral.bytes_bound (literal : ByteLiteral) :
    ∀ b ∈ literal.bytes, b < 256 :=
  literal.prependBytes_bound [] (by simp)

/-- The transparent leaf representation loses no raw byte or high zero.
This theorem is about arbitrary raw slices, independent of the typed hub. -/
theorem block_roundtrip (raw : List Nat) (hb : ∀ b ∈ raw, b < 256) :
    (ByteLiteral.block raw.length (unsignedLE raw)).bytes = raw := by
  simpa only [ByteLiteral.bytes, ByteLiteral.prependBytes, List.append_nil] using
    encodeNatLE_unsignedLE raw hb

open Lean Elab Term

/-- The path is interpreted relative to the consuming Lean source file.
Only ordinary constructors and natural literals occur in the returned term.
The size check is an early IO diagnostic; the kernel-facing file length and
header have their own closed proof bodies in the consuming module. -/
elab (name := includeOriginalBytes) "include_original_bytes% " path:str : term => do
  let sourceFile := System.FilePath.mk (← getFileName)
  let raw ← IO.FS.readBinFile (sourceFile.withFileName path.getString)
  if raw.size != 23410768 then
    throwError "original cells.npy must contain exactly23410768 bytes; found {raw.size}"
  let mut layer : Array Expr := #[]
  for leaf in [: (raw.size + 255) / 256] do
    let start := 256 * leaf
    let count := min 256 (raw.size - start)
    let mut packed : Nat := 0
    for digit in [:count] do
      -- Visiting high indices first gives little-endian radix digits.
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
  if layer.isEmpty then
    return mkConst ``ByteLiteral.empty
  else
    return layer[0]!

end ImbalancedChen.P1HistoricalFifthOriginalByteLiteral
