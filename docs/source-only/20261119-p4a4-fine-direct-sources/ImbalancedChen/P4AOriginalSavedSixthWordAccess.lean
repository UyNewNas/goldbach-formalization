import ImbalancedChen.P4AOriginalSavedSixthArchive

/-! Indexed access to S09's exact immutable NPY literal. Caching the
left subtree lengths avoids traversal of all preceding rows for every
field. Each returned byte is proved equal to ordinary sequential list
indexing; 11-field signed little-endian rows retain their original
positions. -/
namespace ImbalancedChen.P4AOriginalSavedSixthWordAccess
noncomputable section
open P1HistoricalFifthOriginalByteLiteral
open P1HistoricalFifthSigned64Payload
open P4AOriginalSavedSixthArchive (Row originalLiteral originalBytes)

inductive Cached where
  | empty
  | block (count packed : ℕ)
  | node (leftSize : ℕ) (left right : Cached)

def cached : ByteLiteral → ℕ × Cached
  | .empty => (0,.empty)
  | .block n x => (n,.block n x)
  | .node l r =>
    let a := cached l
    let b := cached r
    (a.1+b.1,.node a.1 a.2 b.2)

def leafByte : ℕ → ℕ → ℕ
  | x,0 => x%256
  | x,k+1 => leafByte (x/256) k

def byteAt : Cached → ℕ → ℕ
  | .empty,_ => 0
  | .block n p,k => if k<n then leafByte p k else 0
  | .node n l r,k => if k<n then byteAt l k else byteAt r (k-n)

private theorem append_bytes (x : ByteLiteral) (xs : List ℕ) :
    x.prependBytes xs = x.bytes ++ xs := by
  induction x generalizing xs with
  | empty => rfl
  | block n v => simp [ByteLiteral.prependBytes,ByteLiteral.bytes]
  | node l r il ir =>
    change l.prependBytes (r.prependBytes xs) = l.prependBytes (r.prependBytes []) ++ xs
    rw [il (r.prependBytes xs),ir xs,il (r.prependBytes []),ir []]
    simp [List.append_assoc]

private theorem cached_size (x : ByteLiteral) : (cached x).1=x.byteLength := by
  induction x with
  | empty => rfl
  | block n v => rfl
  | node l r il ir => simp [cached,ByteLiteral.byteLength,il,ir]

private theorem leaf_get (n p k : ℕ) :
    (encodeNatLE n p)[k]?.getD 0 = if k<n then leafByte p k else 0 := by
  induction n generalizing p k with
  | zero => simp [encodeNatLE]
  | succ n ih =>
    cases k with
    | zero => simp [encodeNatLE,leafByte]
    | succ k => simp [encodeNatLE,leafByte,ih]

theorem byteAt_eq (x : ByteLiteral) (k : ℕ) :
    byteAt (cached x).2 k = x.bytes[k]?.getD 0 := by
  induction x generalizing k with
  | empty => simp [cached,byteAt,ByteLiteral.bytes,ByteLiteral.prependBytes]
  | block n p => simp [cached,byteAt,ByteLiteral.bytes,ByteLiteral.prependBytes,leaf_get]
  | node l r il ir =>
    have h : (ByteLiteral.node l r).bytes = l.bytes ++ r.bytes := by
      change l.prependBytes (r.prependBytes []) = _
      rw [append_bytes]; rfl
    rw [h]
    simp only [cached,byteAt,cached_size]
    by_cases hk : k < l.byteLength
    · rw [if_pos hk,List.getElem?_append_left (by simpa [ByteLiteral.bytes_length] using hk),il]
    · rw [if_neg hk,List.getElem?_append_right (by simpa [ByteLiteral.bytes_length] using Nat.le_of_not_lt hk),
        ByteLiteral.bytes_length,ir]

def indexed := (cached originalLiteral).2
def offset (i : Row) (j : Fin 11) := 128+8*(11*i.val+j.val)
def eight (i : Row) (j : Fin 11) : List ℕ := List.ofFn (fun k : Fin 8 => byteAt indexed (offset i j+k.val))

theorem eight_eq (i : Row) (j : Fin 11) :
    eight i j = ((originalBytes.drop (offset i j)).take 8) := by
  have hin : offset i j+8 ≤ originalBytes.length := by
    rw [P4AOriginalSavedSixthArchive.original_bytes_length]
    dsimp [offset]; omega
  apply List.ext_getElem
  · simp [eight,List.length_take,List.length_drop]; omega
  · intro k hl hr
    have hk : k<8 := by simpa [eight] using hl
    have hu : offset i j+k<originalBytes.length := by omega
    simp [eight,indexed,byteAt_eq,← P4AOriginalSavedSixthArchive.originalBytes,
      List.getElem?_eq_getElem hu,List.getElem_take,List.getElem_drop]

def word (i : Row) (j : Fin 11) : ℤ :=
  let u := unsignedLE (eight i j)
  if u<2^63 then (u:ℤ) else (u:ℤ)-2^64

theorem word_eq (i : Row) (j : Fin 11) : word i j = P4AOriginalSavedSixthArchive.word i j := by
  simp only [word,eight_eq,P4AOriginalSavedSixthArchive.word,P4AOriginalSavedSixthArchive.unsignedWord,offset]

end
end ImbalancedChen.P4AOriginalSavedSixthWordAccess
