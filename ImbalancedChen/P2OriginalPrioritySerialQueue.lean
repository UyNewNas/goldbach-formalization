import ImbalancedChen.P2OriginalAdaptiveSourceSplit

/-!
SOURCEONLY / UNCOMPILED / P2.4 OPEN.

Content semantics of the original heap: key (-(hi-lo),serial), with serial
incremented ONLY for a positive-width enclosure. `popBest` is a finite-content
implementation of that priority, not a claim about Python's binary array
layout. Its specification below proves the exact key comparison. No enclosure
is evaluated here. `enclose` remains the original Q80 evaluator port.
-/

namespace ImbalancedChen.P2OriginalPrioritySerialQueueSourceOnly

noncomputable section
open P4AOriginalInitialSeedInventorySourceOnly
open P2OriginalAdaptiveSourceSplitSourceOnly

structure Bounds where
  lower : ℤ
  upper : ℤ

structure Entry where
  cell : SeedCell
  bounds : Bounds
  serial : ℕ

def error (p : Entry) : ℤ := p.bounds.upper - p.bounds.lower

def active (p : Entry) : Prop := p.bounds.lower < p.bounds.upper

/-- Lexicographic order of the literal Python key (-(hi-lo),serial).
The non-strict serial comparison also specifies the reflexive case. -/
def Before (p q : Entry) : Prop :=
  error q < error p ∨ (error p = error q ∧ p.serial ≤ q.serial)

theorem before_refl (p : Entry) : Before p p := by
  exact Or.inr ⟨rfl,le_rfl⟩

theorem before_total (p q : Entry) : Before p q ∨ Before q p := by
  unfold Before
  omega

theorem before_trans {p q r : Entry} (hpq : Before p q) (hqr : Before q r) :
    Before p r := by
  unfold Before at *
  omega

theorem before_key_iff (p q : Entry) :
    Before p q ↔
      -error p < -error q ∨ (-error p = -error q ∧ p.serial ≤ q.serial) := by
  unfold Before
  omega

/-- An equal-error child cannot jump ahead of an older positive-width item. -/
theorem before_equal_error_iff (p q : Entry) (h : error p = error q) :
    Before p q ↔ p.serial ≤ q.serial := by
  unfold Before
  omega

def issueSerial (enclose : SeedCell → Bounds) (c : SeedCell) (s : ℕ) : ℕ :=
  if (enclose c).lower < (enclose c).upper then s + 1 else 0

def advance (enclose : SeedCell → Bounds) (c : SeedCell) (s : ℕ) : ℕ :=
  if (enclose c).lower < (enclose c).upper then s + 1 else s

def issue (enclose : SeedCell → Bounds) (c : SeedCell) (s : ℕ) : Entry :=
  ⟨c,enclose c,issueSerial enclose c s⟩

theorem advance_mono (enclose : SeedCell → Bounds) (c : SeedCell) (s : ℕ) :
    s ≤ advance enclose c s := by
  by_cases h : (enclose c).lower < (enclose c).upper <;> simp [advance,h]

theorem issue_serial_le (enclose : SeedCell → Bounds) (c : SeedCell) (s : ℕ) :
    (issue enclose c s).serial ≤ advance enclose c s := by
  by_cases h : (enclose c).lower < (enclose c).upper <;> simp [issue,issueSerial,advance,h]

theorem issue_active_fresh (enclose : SeedCell → Bounds) (c : SeedCell) (s : ℕ)
    (h : active (issue enclose c s)) :
    (issue enclose c s).serial = s + 1 ∧ advance enclose c s = s + 1 := by
  change (enclose c).lower < (enclose c).upper at h
  simp [issue,issueSerial,advance,h]

/-- Literal side0 insertion followed by side1, including evaluations whose
zero uncertainty means they receive no positive serial and enter no heap. -/
def children (enclose : SeedCell → Bounds) (s : ℕ) (c : SeedCell) : List Entry :=
  [issue enclose (sourceLeft c) s,
   issue enclose (sourceRight c) (advance enclose (sourceLeft c) s)]

def afterChildren (enclose : SeedCell → Bounds) (s : ℕ) (c : SeedCell) : ℕ :=
  advance enclose (sourceRight c) (advance enclose (sourceLeft c) s)

theorem afterChildren_mono (enclose : SeedCell → Bounds) (s : ℕ) (c : SeedCell) :
    s ≤ afterChildren enclose s c :=
  (advance_mono enclose (sourceLeft c) s).trans
    (advance_mono enclose (sourceRight c) (advance enclose (sourceLeft c) s))

theorem children_serial_le (enclose : SeedCell → Bounds) (s : ℕ) (c : SeedCell)
    (p : Entry) (hp : p ∈ children enclose s c) :
    p.serial ≤ afterChildren enclose s c := by
  simp only [children,List.mem_cons,List.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact (issue_serial_le enclose _ _).trans (advance_mono enclose _ _)
  · exact issue_serial_le enclose _ _

theorem active_children_fresh (enclose : SeedCell → Bounds) (s : ℕ) (c : SeedCell)
    (p : Entry) (hp : p ∈ children enclose s c) (ha : active p) :
    s < p.serial := by
  simp only [children,List.mem_cons,List.mem_singleton] at hp
  rcases hp with rfl | rfl
  · rw [(issue_active_fresh enclose _ _ ha).1]
    omega
  · rw [(issue_active_fresh enclose _ _ ha).1]
    have h := advance_mono enclose (sourceLeft c) s
    omega

theorem active_children_tie_order (enclose : SeedCell → Bounds) (s : ℕ) (c : SeedCell)
    (hl : active (issue enclose (sourceLeft c) s))
    (hr : active (issue enclose (sourceRight c) (advance enclose (sourceLeft c) s))) :
    (issue enclose (sourceLeft c) s).serial <
      (issue enclose (sourceRight c) (advance enclose (sourceLeft c) s)).serial := by
  rw [(issue_active_fresh enclose _ _ hl).1,
    (issue_active_fresh enclose _ _ hr).1,
    (issue_active_fresh enclose _ _ hl).2]
  omega

def heapContents (xs : List Entry) : List Entry := xs.filter (fun p => decide (active p))

/-- Select the least literal priority key; return every other entry once.
Its list order is deliberately not used as Python's heap-array order. -/
def popBest : List Entry → Option (Entry × List Entry)
  | [] => none
  | p :: ps =>
      match popBest ps with
      | none => some (p,[])
      | some (q,qs) =>
          if Before p q then some (p,ps) else some (q,p :: qs)

theorem popBest_none_iff (xs : List Entry) : popBest xs = none ↔ xs = [] := by
  cases xs with
  | nil => simp [popBest]
  | cons p ps =>
      cases h : popBest ps with
      | none => simp [popBest,h]
      | some pair =>
          rcases pair with ⟨q,qs⟩
          by_cases hkey : Before p q <;> simp [popBest,h,hkey]

/-- Both the exact removal multiset and priority of the returned parent are
proved; neither is a heap-validity assumption supplied by the caller. -/
theorem popBest_spec (xs : List Entry) (p : Entry) (rest : List Entry)
    (h : popBest xs = some (p,rest)) :
    xs.Perm (p :: rest) ∧ p ∈ xs ∧ ∀ q ∈ xs, Before p q := by
  induction xs generalizing p rest with
  | nil => simp [popBest] at h
  | cons a xs ih =>
      cases hs : popBest xs with
      | none =>
          have hx : xs = [] := (popBest_none_iff xs).mp hs
          subst xs
          simp only [popBest] at h
          cases h
          exact ⟨List.Perm.refl _,by simp,by
            intro q hq
            have hq' : q = a := by simpa using hq
            subst q
            exact before_refl a⟩
      | some pair =>
          rcases pair with ⟨b,bs⟩
          obtain ⟨hperm,hmem,hmin⟩ := ih b bs hs
          by_cases hab : Before a b
          · simp only [popBest,hs,if_pos hab] at h
            cases h
            refine ⟨List.Perm.refl _,by simp,?_⟩
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact before_refl a
            · exact before_trans hab (hmin q hq)
          · simp only [popBest,hs,if_neg hab] at h
            cases h
            refine ⟨(List.Perm.cons a hperm).trans (List.Perm.swap a b bs),
              List.mem_cons.mpr (Or.inr hmem),?_⟩
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact (before_total a b).resolve_left hab
            · exact hmin q hq

theorem popped_active (xs : List Entry) (p : Entry) (rest : List Entry)
    (h : popBest (heapContents xs) = some (p,rest)) : active p := by
  have hp := (List.mem_filter.mp (popBest_spec _ _ _ h).2.1).2
  exact of_decide_eq_true hp

/-- Maximal uncertainty and smallest serial at equal uncertainty, exactly
the source key. An exact/empty leaf cannot be selected by this heap. -/
theorem popped_priority (xs : List Entry) (p : Entry) (rest : List Entry)
    (h : popBest (heapContents xs) = some (p,rest)) (q : Entry)
    (hq : q ∈ xs) (ha : active q) :
    error q ≤ error p ∧ (error q = error p → p.serial ≤ q.serial) := by
  have hq' : q ∈ heapContents xs := List.mem_filter.mpr ⟨hq,by simp [ha]⟩
  have hk := (popBest_spec _ _ _ h).2.2 q hq'
  unfold Before at hk
  omega

end
end ImbalancedChen.P2OriginalPrioritySerialQueueSourceOnly
