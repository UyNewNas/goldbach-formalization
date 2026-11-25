import Lean

/-!
Experimental raw-character representation only. The tree/prepend pattern follows
P4AOriginalNewFifthArchiveReader.Words, but the character codec and its complete
round-trip are proved here. No old String equality, JSON rule or typed decoder
is changed. Each leaf carries its exact count, so trailing NUL is preserved.
-/
namespace ImbalancedChen.P2OriginalSaving19PackedChars

noncomputable section

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

def radix : Nat := UInt32.size

theorem radix_pos : 0 < radix := by decide

theorem char_toNat_lt_radix (c : Char) : c.toNat < radix :=
  UInt32.toNat_lt_size c.val

def packWord : List Char → Nat :=
  List.rec (motive := fun _ => Nat)
    0
    (fun c _ previous => c.toNat + radix * previous)

/-- Count controls decoding; zero is a valid encoded NUL, never a terminator. -/
def unpackWord : Nat → Nat → List Char :=
  Nat.rec (motive := fun _ => Nat → List Char)
    (fun _ => [])
    (fun _ previous word => Char.ofNat (word % radix) :: previous (word / radix))

theorem length_unpackWord (n word : Nat) : (unpackWord n word).length = n := by
  induction n generalizing word with
  | zero => rfl
  | succ n ih => simp only [unpackWord, List.length_cons, ih]

/-- All Unicode Char values, including NUL, are recovered exactly. A mere digit
bound would not exclude surrogate codepoints; this proof recovers the original
Char.toNat and then uses Char.ofNat_toNat. -/
theorem unpackWord_packWord (cs : List Char) :
    unpackWord cs.length (packWord cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.length_cons, packWord, unpackWord,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (char_toNat_lt_radix c),
      Nat.add_mul_div_left _ _ radix_pos,
      Nat.div_eq_of_lt (char_toNat_lt_radix c), Nat.zero_add,
      Char.ofNat_toNat, ih]

/-- A block can be skipped arithmetically without decoding its skipped prefix. -/
theorem unpackWord_drop (skip n word : Nat) :
    unpackWord (n - skip) (word / radix ^ skip) = (unpackWord n word).drop skip := by
  induction skip generalizing n word with
  | zero => simp only [Nat.sub_zero, Nat.pow_zero, Nat.div_one, List.drop_zero]
  | succ skip ih =>
    cases n with
    | zero => simp only [Nat.zero_sub, unpackWord, List.drop_nil]
    | succ n =>
      simpa only [Nat.succ_sub_succ_eq_sub, unpackWord, List.drop_succ_cons,
        Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm] using
        (ih n (word / radix))

inductive Tree where
  | empty
  | leaf (count word : Nat)
  | branch (left right : Tree)
  deriving Inhabited

def Tree.prepend : Tree → List Char → List Char :=
  Tree.rec (motive := fun _ => List Char → List Char)
    (fun tail => tail)
    (fun n word tail => unpackWord n word ++ tail)
    (fun _ _ left right tail => left (right tail))

def Tree.toList (t : Tree) : List Char := t.prepend []

def Tree.count : Tree → Nat :=
  Tree.rec (motive := fun _ => Nat)
    0
    (fun n _ => n)
    (fun _ _ left right => left + right)

theorem Tree.prepend_eq (t : Tree) (tail : List Char) :
    t.prepend tail = t.toList ++ tail := by
  induction t generalizing tail with
  | empty => rfl
  | leaf n word => simp only [Tree.toList, Tree.prepend, List.append_nil]
  | branch l r il ir =>
    change l.prepend (r.prepend tail) = l.prepend (r.prepend []) ++ tail
    simp only [il, ir, List.append_nil, List.append_assoc]

theorem Tree.toList_empty : Tree.empty.toList = [] := rfl

theorem Tree.toList_leaf (n word : Nat) : (Tree.leaf n word).toList = unpackWord n word := by
  simp only [Tree.toList, Tree.prepend, List.append_nil]

theorem Tree.toList_branch (l r : Tree) : (Tree.branch l r).toList = l.toList ++ r.toList :=
  l.prepend_eq r.toList

theorem Tree.length_toList (t : Tree) : t.toList.length = t.count := by
  induction t with
  | empty => rfl
  | leaf n word => simp only [Tree.toList_leaf, length_unpackWord, Tree.count]
  | branch l r il ir =>
    simp only [Tree.toList_branch, List.length_append, il, ir, Tree.count]

/-- Skip whole subtrees using their proved character count. An exhausted leaf
becomes empty; otherwise divide off precisely the skipped codepoints. -/
def Tree.drop (skip : Nat) : Tree → Tree :=
  fun t =>
    Tree.rec (motive := fun _ => Nat → Tree)
      (fun _ => .empty)
      (fun n word skip =>
        if skip < n then .leaf (n - skip) (word / radix ^ skip) else .empty)
      (fun l r left right skip =>
        if skip < l.count then .branch (left skip) r
        else right (skip - l.count))
      t skip

theorem Tree.toList_drop (t : Tree) (skip : Nat) :
    (t.drop skip).toList = t.toList.drop skip := by
  induction t generalizing skip with
  | empty => simp only [Tree.drop, Tree.toList_empty, List.drop_nil]
  | leaf n word =>
    by_cases h : skip < n
    · simp only [Tree.drop, h, if_true, Tree.toList_leaf, unpackWord_drop]
    · have hn : n ≤ skip := Nat.le_of_not_gt h
      simp only [Tree.drop, h, if_false, Tree.toList_empty, Tree.toList_leaf]
      exact (List.drop_eq_nil_of_le (by simpa only [length_unpackWord] using hn)).symm
  | branch l r il ir =>
    by_cases h : skip < l.count
    · simp only [Tree.drop, h, if_true, Tree.toList_branch, il]
      rw [List.drop_append]
      have hr : skip - l.toList.length = 0 := by
        rw [l.length_toList]
        exact Nat.sub_eq_zero_of_le (Nat.le_of_lt h)
      rw [hr, List.drop_zero]
    · have hl : l.toList.length ≤ skip := by
        rw [l.length_toList]
        exact Nat.le_of_not_gt h
      simp only [Tree.drop, h, if_false, Tree.toList_branch, ir]
      rw [List.drop_append, List.drop_eq_nil_of_le hl, List.nil_append, l.length_toList]

theorem Tree.count_drop (t : Tree) (skip : Nat) :
    (t.drop skip).count = t.count - skip := by
  rw [← (t.drop skip).length_toList, t.toList_drop, List.length_drop, t.length_toList]

def blockLimit : Nat := 256

/-- Fuel controls only tree shape. At zero, all remaining characters are packed
in one exact-length leaf, so even this fallback never truncates input. -/
def packTreeGo : Nat → List Char → Tree :=
  Nat.rec (motive := fun _ => List Char → Tree)
    (fun cs => .leaf cs.length (packWord cs))
    (fun _ previous cs =>
      if cs.length ≤ blockLimit then .leaf cs.length (packWord cs)
      else
        let cut := cs.length / 2
        .branch (previous (cs.take cut)) (previous (cs.drop cut)))

def pack (cs : List Char) : Tree := packTreeGo cs.length cs

/-- Whole-tree content and order, for every input and every shape fuel. -/
theorem unpack_packTreeGo (fuel : Nat) (cs : List Char) :
    (packTreeGo fuel cs).toList = cs := by
  induction fuel generalizing cs with
  | zero => simpa only [packTreeGo, Tree.toList_leaf] using unpackWord_packWord cs
  | succ fuel ih =>
    by_cases h : cs.length ≤ blockLimit
    · simpa only [packTreeGo, h, if_true, Tree.toList_leaf] using unpackWord_packWord cs
    · simp only [packTreeGo, h, if_false, Tree.toList_branch, ih, List.take_append_drop]

theorem unpack_pack (cs : List Char) : (pack cs).toList = cs :=
  unpack_packTreeGo cs.length cs

theorem count_pack (cs : List Char) : (pack cs).count = cs.length := by
  rw [← (pack cs).length_toList, unpack_pack]

theorem drop_pack (cs : List Char) (skip : Nat) :
    ((pack cs).drop skip).toList = cs.drop skip := by
  rw [Tree.toList_drop, unpack_pack]

#print axioms unpackWord_packWord
#print axioms unpackWord_drop
#print axioms Tree.length_toList
#print axioms Tree.toList_drop
#print axioms unpack_pack
#print axioms count_pack
#print axioms drop_pack

end
end ImbalancedChen.P2OriginalSaving19PackedChars
