import Lean
import ImbalancedChen.P1OriginalPrefixRowDecodeSoundness

/-! Raw fixed-width slices of the two independently stored original NPY
entries. The elaborator packs bytes only. The signed little-endian fields,
UTF32 decimal interpretation, shape and header checks are ordinary Lean
definitions. No archive assertion is introduced by the elaborator. -/
namespace ImbalancedChen.P4AOriginalNewFifthArchiveReader
open P1OriginalPrefixRowDecodeSoundness

inductive Words where
  | empty
  | leaf (cells floor : ℕ)
  | branch (left right : Words)
  deriving Inhabited

def Words.prepend : Words → List (ℕ × ℕ) → List (ℕ × ℕ)
  | .empty, tail => tail
  | .leaf c f, tail => (c,f) :: tail
  | .branch l r, tail => l.prepend (r.prepend tail)

def Words.list (w : Words) : List (ℕ × ℕ) := w.prepend []

def Words.total {α : Type*} [Zero α] [Add α] (f : ℕ × ℕ → α) : Words → α
  | .empty => 0
  | .leaf c q => f (c,q)
  | .branch l r => l.total f + r.total f

def Words.size : Words → ℕ
  | .empty => 0
  | .leaf _ _ => 1
  | .branch l r => l.size + r.size

theorem Words.prepend_eq (w : Words) (tail : List (ℕ × ℕ)) :
    w.prepend tail = w.list ++ tail := by
  induction w generalizing tail with
  | empty => rfl
  | leaf c q => rfl
  | branch l r il ir =>
    change l.prepend (r.prepend tail) = l.prepend (r.prepend []) ++ tail
    simp only [il (r.prepend tail), il (r.prepend []), ir tail, ir [],
      List.append_nil, List.append_assoc]

theorem Words.sum_list {α : Type*} [AddMonoid α] (w : Words) (f : ℕ × ℕ → α) :
    (w.list.map f).sum = w.total f := by
  induction w with
  | empty => rfl
  | leaf c q => simp [Words.list, Words.prepend, Words.total]
  | branch l r il ir =>
    change ((l.prepend r.list).map f).sum = l.total f + r.total f
    rw [Words.prepend_eq, List.map_append, List.sum_append, il, ir]

theorem Words.length_list (w : Words) : w.list.length = w.size := by
  have aux (v : Words) (tail : List (ℕ × ℕ)) : (v.prepend tail).length = v.size + tail.length := by
    induction v generalizing tail with
    | empty => simp [Words.prepend, Words.size]
    | leaf c f => simp [Words.prepend, Words.size, Nat.add_comm]
    | branch l r il ir => simp [Words.prepend, Words.size, il, ir, Nat.add_assoc]
  simpa [Words.list] using aux w []

def Words.all (p : ℕ × ℕ → Bool) : Words → Bool
  | .empty => true
  | .leaf c f => p (c,f)
  | .branch l r => l.all p && r.all p

theorem Words.all_spec (p : ℕ × ℕ → Bool) (w : Words) (h : w.all p = true) :
    ∀ r ∈ w.list, p r = true := by
  have aux (v : Words) (hv : v.all p = true) (tail : List (ℕ × ℕ))
      (ht : ∀ r ∈ tail, p r = true) : ∀ r ∈ v.prepend tail, p r = true := by
    induction v generalizing tail with
    | empty => exact ht
    | leaf c f =>
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hm
      · exact hv
      · exact ht r hm
    | branch l r il ir =>
      obtain ⟨hl,hr⟩ := Bool.and_eq_true.mp hv
      exact il hl _ (ir hr _ ht)
  exact aux w h [] (by simp)

structure Block where
  cellsHeader : ℕ
  floorsHeader : ℕ
  words : Words
  deriving Inhabited

def expectedHeader (count : ℕ) (floor : Bool) : ℕ :=
  let shape := if floor then "(" ++ toString count ++ ",)" else "(" ++ toString count ++ ", 10)"
  let dtype := if floor then "<U40" else "<i8"
  let descr := "{'descr': '" ++ dtype ++ "', 'fortran_order': False, 'shape': " ++ shape ++ ", }"
  let txt := descr.toList.map Char.toNat
  let bytes := [147,78,85,77,80,89,1,0,118,0] ++ txt ++ List.replicate (117-txt.length) 32 ++ [10]
  bytes.foldr (fun byte rest => byte + 256*rest) 0

def signedField (packed column : ℕ) : ℤ :=
  let u := (packed / 2^(64*column)) % 2^64
  if u < 2^63 then (u : ℤ) else (u : ℤ) - (2 : ℤ)^64

def wire (x : ℕ × ℕ) : FifthWireRow :=
  ⟨signedField x.1 0, fun k => signedField x.1 (1+k.val),
    signedField x.1 6, signedField x.1 7, signedField x.1 8, signedField x.1 9⟩

/-- At most forty original codepoints. After the first NUL every
remaining byte must be zero. A digit occupies exactly one UTF32LE word. -/
def readDecimal : ℕ → ℕ → ℕ → Bool → Option ℕ
  | 0, p, n, seen => if p = 0 ∧ seen = true then some n else none
  | k+1, p, n, seen =>
      if p = 0 then (if seen then some n else none)
      else let c := p % 2^32
           if 48 ≤ c ∧ c ≤ 57 then readDecimal k (p/2^32) (10*n+(c-48)) true else none

def saved? (x : ℕ × ℕ) := readDecimal 40 x.2 0 false
def saved (x : ℕ × ℕ) := (saved? x).getD 0

open Lean Elab Term

private def packBytes (b : ByteArray) (first count : Nat) : Nat := Id.run do
  let mut packed := 0
  for j in [:count] do
    packed := 256*packed + (b.get! (first+count-1-j)).toNat
  return packed

/-- Each leaf stores exactly the 80 raw cell bytes and the 160 raw
floor bytes at the same source position. Both entire 128-byte NPY
headers are included. External staging extracts the original ZIP
members verbatim and verifies the registry's raw hashes. -/
elab "include_new_fifth_pair% " cellpath:str floorpath:str : term => do
  let file := System.FilePath.mk (← getFileName)
  let c ← IO.FS.readBinFile (file.withFileName cellpath.getString)
  let f ← IO.FS.readBinFile (file.withFileName floorpath.getString)
  if c.size < 128 || (c.size-128)%80 != 0 then throwError "invalid original cells byte count"
  let n := (c.size-128)/80
  if f.size != 128 + 160*n then throwError "original arrays have different row counts"
  let mut layer : Array Expr := #[]
  for j in [:n] do
    layer := layer.push (mkApp2 (mkConst ``Words.leaf)
      (mkNatLit (packBytes c (128+80*j) 80)) (mkNatLit (packBytes f (128+160*j) 160)))
  while 1 < layer.size do
    let mut next : Array Expr := #[]
    for j in [:(layer.size+1)/2] do
      let l := layer[2*j]!
      next := next.push (if 2*j+1 < layer.size then mkApp2 (mkConst ``Words.branch) l layer[2*j+1]! else l)
    layer := next
  let words := if layer.isEmpty then mkConst ``Words.empty else layer[0]!
  return mkApp3 (mkConst ``Block.mk) (mkNatLit (packBytes c 0 128)) (mkNatLit (packBytes f 0 128)) words

end ImbalancedChen.P4AOriginalNewFifthArchiveReader
