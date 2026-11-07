import ImbalancedChen.P5OriginalFeedbackDomains

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal physical state for the finite enhanced lower construction.  A slot
contains its physical exponent and its ORIGINAL selected-slot tag.  New
feedback primes are unselected.  The total level is stored once; residual
level and alpha are computed from the complete physical prefix.  No
admission, distribution, density, beta identity, or support certificate is
a field of this datatype.  Ancestor cap/cell traces are separate data: the
constructors below preserve the old word literally, so such traces can be
pulled back along the prefix projection without optimizing an old cap.
-/

namespace ImbalancedChen.P2EnhancedLowerPhysicalNode

noncomputable section

structure Slot where
  exponent : ℝ
  selected : Bool

structure PhysicalNode where
  occurrence : Fin 11
  total : ℝ
  slots : List Slot
  ceiling : ℝ
  argument : ℝ

def word (n : PhysicalNode) : List ℝ := n.slots.map Slot.exponent
def residual (n : PhysicalNode) : ℝ := n.total - (word n).sum
def alpha (n : PhysicalNode) : ℝ := (1 - (word n).sum) / residual n

def selectedWord : List Slot → List ℝ
  | [] => []
  | a :: as => if a.selected = true then a.exponent :: selectedWord as else selectedWord as

def remainingWord : List Slot → List ℝ
  | [] => []
  | a :: as => if a.selected = true then remainingWord as else a.exponent :: remainingWord as

/-- Complete-prefix square tests in physical exponent coordinates.  The
closed version retains structural equality; strict compact buffers are
chosen by the separate geometric refinement, never by deleting a clamp. -/
def SquareGates (nu T : ℝ) : List ℝ → Prop
  | [] => True
  | x :: xs => T + 2*x ≤ nu ∧ SquareGates nu (T+x) xs

def fullGates (n : PhysicalNode) : Prop := SquareGates n.total 0 (word n)
def selectedGates (n : PhysicalNode) : Prop :=
  SquareGates n.total (selectedWord n.slots).sum (remainingWord n.slots)

def unselected (x : ℝ) : Slot := ⟨x, false⟩

/-- Appending a physical prime keeps the old marked word and total Q.
Its physical exponent becomes the stable ceiling for later primes. -/
def appendOne (n : PhysicalNode) (x s : ℝ) : PhysicalNode :=
  { n with slots := n.slots ++ [unselected x], ceiling := x, argument := s }

/-- Original pair coordinates have x<y; the prime word appends [y,x]. -/
def appendPair (n : PhysicalNode) (x y s : ℝ) : PhysicalNode :=
  { n with slots := n.slots ++ [unselected y, unselected x],
    ceiling := x, argument := s }

/-- A comparison changes only the physical cutoff argument. -/
def compareAt (n : PhysicalNode) (s : ℝ) : PhysicalNode := { n with argument := s }

theorem selectedWord_append (xs ys : List Slot) :
    selectedWord (xs ++ ys) = selectedWord xs ++ selectedWord ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : a.selected = true <;> simp [selectedWord, h, ih]

theorem remainingWord_append (xs ys : List Slot) :
    remainingWord (xs ++ ys) = remainingWord xs ++ remainingWord ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : a.selected = true <;> simp [remainingWord, h, ih]

theorem selected_remaining_sum (xs : List Slot) :
    (selectedWord xs).sum + (remainingWord xs).sum = (xs.map Slot.exponent).sum := by
  induction xs with
  | nil => simp [selectedWord, remainingWord]
  | cons a xs ih =>
      cases h : a.selected <;>
        simp [selectedWord, remainingWord, h, List.sum_cons,
          add_assoc, add_left_comm, add_comm] at * <;> linarith only [ih]

theorem squareGates_append_iff (nu T : ℝ) (xs ys : List ℝ) :
    SquareGates nu T (xs ++ ys) ↔
      SquareGates nu T xs ∧ SquareGates nu (T+xs.sum) ys := by
  induction xs generalizing T with
  | nil => simp [SquareGates]
  | cons x xs ih => simp [SquareGates, ih, List.sum_cons, add_assoc, and_assoc]

@[simp] theorem word_appendOne (n : PhysicalNode) (x s : ℝ) :
    word (appendOne n x s) = word n ++ [x] := by
  simp [word, appendOne, unselected]

@[simp] theorem word_appendPair (n : PhysicalNode) (x y s : ℝ) :
    word (appendPair n x y s) = word n ++ [y,x] := by
  simp [word, appendPair, unselected]

@[simp] theorem residual_appendOne (n : PhysicalNode) (x s : ℝ) :
    residual (appendOne n x s) = residual n-x := by
  change n.total-(word (appendOne n x s)).sum = residual n-x
  rw [word_appendOne]
  simp only [List.sum_append, List.sum_cons, List.sum_nil]
  dsimp [residual]
  ring

@[simp] theorem residual_appendPair (n : PhysicalNode) (x y s : ℝ) :
    residual (appendPair n x y s) = residual n-y-x := by
  change n.total-(word (appendPair n x y s)).sum = residual n-y-x
  rw [word_appendPair]
  simp only [List.sum_append, List.sum_cons, List.sum_nil]
  dsimp [residual]
  ring

@[simp] theorem selected_appendOne (n : PhysicalNode) (x s : ℝ) :
    selectedWord (appendOne n x s).slots = selectedWord n.slots := by
  simp [appendOne, selectedWord_append, selectedWord, unselected]

@[simp] theorem selected_appendPair (n : PhysicalNode) (x y s : ℝ) :
    selectedWord (appendPair n x y s).slots = selectedWord n.slots := by
  simp [appendPair, selectedWord_append, selectedWord, unselected]

/-- Both new full and new selected-remaining tests are the SAME residual
test.  All old tests remain, with their literal original selected labels. -/
theorem appendOne_gates {n : PhysicalNode} {x s : ℝ}
    (hf : fullGates n) (hs : selectedGates n) (hx : 2*x ≤ residual n) :
    fullGates (appendOne n x s) ∧ selectedGates (appendOne n x s) := by
  have hsum := selected_remaining_sum n.slots
  constructor
  · rw [fullGates, word_appendOne, squareGates_append_iff]
    refine ⟨hf, ?_⟩
    change 0+(word n).sum+2*x ≤ n.total ∧ True
    constructor
    · dsimp [residual] at hx; linarith only [hx]
    · trivial
  · change SquareGates n.total (selectedWord (n.slots ++ [unselected x])).sum
      (remainingWord (n.slots ++ [unselected x]))
    simp only [selectedWord_append, remainingWord_append]
    simp only [selectedWord, remainingWord, unselected, Bool.false_eq_true,
      if_false, List.append_nil, List.nil_append]
    rw [squareGates_append_iff]
    refine ⟨hs, ?_⟩
    change (selectedWord n.slots).sum+(remainingWord n.slots).sum+2*x ≤ n.total ∧ True
    constructor
    · dsimp [residual, word] at hx; linarith only [hx, hsum]
    · trivial

theorem appendPair_gates {n : PhysicalNode} {x y s : ℝ}
    (hf : fullGates n) (hs : selectedGates n)
    (hy : 2*y ≤ residual n) (hx : y+2*x ≤ residual n) :
    fullGates (appendPair n x y s) ∧ selectedGates (appendPair n x y s) := by
  have h1 := appendOne_gates (s := s) hf hs hy
  have h2 := appendOne_gates (s := s) h1.1 h1.2
    (show 2*x ≤ residual (appendOne n y s) by
      rw [residual_appendOne]; linarith only [hx])
  have heq : appendOne (appendOne n y s) x s = appendPair n x y s := by
    cases n
    simp [appendOne, appendPair, List.append_assoc]
  simpa only [heq] using h2

theorem appendOne_old_slots (n : PhysicalNode) (x s : ℝ) :
    (appendOne n x s).slots.take n.slots.length = n.slots := by
  simp [appendOne]

theorem appendPair_old_slots (n : PhysicalNode) (x y s : ℝ) :
    (appendPair n x y s).slots.take n.slots.length = n.slots := by
  simp [appendPair]

/-- These are identities for the state, not a comparison between
different densities or a licence to reset Q or alpha at a child. -/
theorem compareAt_preserves_state (n : PhysicalNode) (s : ℝ) :
    (compareAt n s).total=n.total ∧ (compareAt n s).slots=n.slots ∧
    (compareAt n s).ceiling=n.ceiling ∧ residual (compareAt n s)=residual n ∧
    alpha (compareAt n s)=alpha n := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end
end ImbalancedChen.P2EnhancedLowerPhysicalNode
