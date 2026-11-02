import ImbalancedChen.Part5OriginalH430FrozenRootRefinement
import ImbalancedChen.FinitePrimeGeometryCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Concrete ordinary-feedback components, physical query pullbacks, and
prime-slot itineraries.  A path consumes zero, one, or two primes at each
step.  The unused Point coordinate is zero padding, NOT an extra prime
summation or an extra multiplicity.  An actual canonical Program is
computed from these native coordinates before it is placed in GraphVertex.

The switched base costs are not StepShape children.  This file makes no
claim that their source carriers, or a numerical immutable430 action,
have been realized by the ordinary feedback graph.
-/

namespace ImbalancedChen.Part5OriginalH430NativeQueryPaths

noncomputable section
open Set Classical
open scoped BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430AbsoluteQueries
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement

/-- Lists retain original labelled occurrences and their literal scalar
coefficients; they are not a set of distinct prime products. -/
def components : Original106Action → List (StepShape × ℝ)
  | .inl (i, j) => [(.w1Fixed i j, 1), (.w1Singleton i j, 1 / 2)]
  | .inr j =>
      [(.w2Fixed j true, 4 / 5), (.w2Fixed j false, 1 / 5),
       (.w2Singleton j 0, 1 / 5), (.w2Singleton j 1, 1 / 5),
       (.w2Singleton j 2, 1 / 5),
       (.w2Pair j 0, 1 / 5), (.w2Pair j 1, 1 / 5),
       (.w2Pair j 2, 1 / 5), (.w2Pair j 3, 1 / 5)]

def componentSum (a : Original106Action) (F : StepShape → ℝ) : ℝ :=
  ((components a).map (fun c => c.2 * F c.1)).sum

theorem W1_components_exact (i : Fin 7) (j : Fin 10) (F : StepShape → ℝ) :
    componentSum (.inl (i, j)) F = F (.w1Fixed i j) + F (.w1Singleton i j) / 2 := by
  simp [componentSum, components]
  ring

theorem W2_components_exact (j : Fin 36) (F : StepShape → ℝ) :
    componentSum (.inr j) F =
      (4 * F (.w2Fixed j true) + F (.w2Fixed j false) +
        (∑ i : Fin 3, F (.w2Singleton j i)) +
        (∑ i : Fin 4, F (.w2Pair j i))) / 5 := by
  simp [componentSum, components, Fin.sum_univ_succ]
  ring

/-- Only integral feedback components occur here.  Fixed comparisons
remain the separate coefficient-bearing list entries above. -/
inductive FeedbackQuery where
  | w1 (i : Fin 7) (j : Fin 10)
  | w2Singleton (bank : Fin 36) (piece : Fin 3)
  | w2Pair (bank : Fin 36) (piece : Fin 4)
  | buchstabUpper (cell : Fin 200)
  | buchstabLower (cell : Fin 150)
  deriving DecidableEq, Fintype

def FeedbackQuery.primitive : FeedbackQuery → Primitive
  | .w1 i j => .w1 i j
  | .w2Singleton j k => .w2Singleton j k
  | .w2Pair j k => .w2Pair j k
  | .buchstabUpper j => .buchstabUpper j
  | .buchstabLower j => .buchstabLower j

def FeedbackQuery.shape : FeedbackQuery → StepShape
  | .w1 i j => .w1Singleton i j
  | .w2Singleton j k => .w2Singleton j k
  | .w2Pair j k => .w2Pair j k
  | .buchstabUpper _ => .buchstabUpper
  | .buchstabLower _ => .buchstabLower

def FeedbackQuery.coordinate (n : PhysicalNode) (z : Point) :
    (q : FeedbackQuery) → Space q.primitive
  | .w1 _ _ => normalized n z 0
  | .w2Singleton _ _ => normalized n z 0
  | .w2Pair _ _ => normalized n z
  | .buchstabUpper _ => buchstabArgument n z
  | .buchstabLower _ => buchstabArgument n z

theorem actual_child_query (n : PhysicalNode) (z : Point) (q : FeedbackQuery) :
    (perform n q.shape z).argument =
      (data q.primitive).query (q.coordinate n z) := by
  cases q <;> rfl

/-- A primitive Buchstab integral has a FIXED table-cell start.  The
physical LocalDomain has the actual moving parent argument.  Their
equality must be established by a real cell/transport dictionary. -/
def StartMatches (n : PhysicalNode) : FeedbackQuery → Prop
  | .buchstabUpper i => n.argument = upperStart i
  | .buchstabLower i => n.argument = lowerStart i
  | _ => True

theorem actual_child_domain {n : PhysicalNode} {z : Point} (q : FeedbackQuery)
    (hstart : StartMatches n q) (hz : LocalDomain n q.shape z) :
    q.coordinate n z ∈ (data q.primitive).domain := by
  cases q with
  | w1 i j => exact hz.2.2.1
  | w2Singleton j k => exact hz.2.2.1
  | w2Pair j k => exact hz.2.2.1
  | buchstabUpper i =>
      change n.argument = upperStart i at hstart
      simpa only [hstart] using hz.2.2
  | buchstabLower i =>
      change n.argument = lowerStart i at hstart
      simpa only [hstart] using hz.2.2.2

/-- Each original closed query atom, including a singleton knot, is
pulled back along the ACTUAL physical child argument. -/
theorem actual_query_atom {n : PhysicalNode} {z : Point} (q : FeedbackQuery)
    (b : Part5OriginalUpsilon5CausalDictionary.FloorAtom)
    (hstart : StartMatches n q) (hz : LocalDomain n q.shape z) :
    q.coordinate n z ∈ atomSet q.primitive b ↔
      (perform n q.shape z).argument ∈
        P5OriginalFeedbackTableKernels.tableAtomSet (data q.primitive).lower b := by
  constructor
  · intro h
    rw [actual_child_query]
    exact h.2
  · intro h
    refine ⟨actual_child_domain q hstart hz, ?_⟩
    change (data q.primitive).query (q.coordinate n z) ∈ _
    rw [← actual_child_query]
    exact h

def arity : StepShape → ℕ
  | .buchstabUpper | .buchstabLower | .w1Singleton _ _ | .w2Singleton _ _ => 1
  | .w2Pair _ _ => 2
  | _ => 0

theorem arity_le_two (s : StepShape) : arity s ≤ 2 := by cases s <;> simp [arity]

/-- The external selected root occupies its own slot.  A zero-arity
comparison has NO native prime slot, and a singleton has exactly one. -/
abbrev NativeSlot {depth : ℕ} (shape : Fin depth → StepShape) :=
  Unit ⊕ ((i : Fin depth) × Fin (arity (shape i)))

def nativeRank {depth : ℕ} (shape : Fin depth → StepShape) : ℕ :=
  Fintype.card (NativeSlot shape)

theorem nativeRank_exact {depth : ℕ} (shape : Fin depth → StepShape) :
    nativeRank shape = 1 + ∑ i : Fin depth, arity (shape i) := by
  simp [nativeRank, NativeSlot, Fintype.card_sigma]

theorem nativeRank_le {depth : ℕ} (shape : Fin depth → StepShape) :
    nativeRank shape ≤ 1 + 2 * depth := by
  rw [nativeRank_exact]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin depth)))
    (fun i _ => arity_le_two (shape i))
  simpa [mul_comm] using Nat.add_le_add_left h 1

def nativeRootCoordinate {depth : ℕ} {shape : Fin depth → StepShape}
    (x : NativeSlot shape → ℝ) : ℝ := x (.inl ())

def nativeCoordinates {depth : ℕ} (shape : Fin depth → StepShape)
    (x : NativeSlot shape → ℝ) : Coordinates depth := fun i j =>
  if h : j.val < arity (shape i) then x (.inr ⟨i, ⟨j.val, h⟩⟩) else 0

def nativePrimeLogs {depth : ℕ} {shape : Fin depth → StepShape}
    (N : ℕ) (p : NativeSlot shape → ℕ) : NativeSlot shape → ℝ :=
  fun slot => Real.log (p slot : ℝ) / Real.log (N : ℝ)

def nativeProgram {depth : ℕ} (mesh : ℕ) (shape : Fin depth → StepShape)
    (x : NativeSlot shape → ℝ) : Program mesh depth :=
  canonicalProgram 0 1 mesh shape (nativeCoordinates shape x)

def nativeVertex {depth : ℕ} (hd : depth ≤ 440) (mesh : ℕ)
    (shape : Fin depth → StepShape) (x : NativeSlot shape → ℝ) : GraphVertex mesh 440 :=
  ⟨⟨depth, Nat.lt_succ_of_le hd⟩, nativeProgram mesh shape x⟩

theorem nativeVertex_generation {depth : ℕ} (hd : depth ≤ 440) (mesh : ℕ)
    (shape : Fin depth → StepShape) (x : NativeSlot shape → ℝ) :
    (nativeVertex hd mesh shape x).1.val = depth := rfl

theorem nativeProgram_member {depth : ℕ} (mesh : ℕ) (n : TypedNode)
    (shape : Fin depth → StepShape) (x : NativeSlot shape → ℝ)
    (hx : LocalPath 0 1 depth n shape (nativeCoordinates shape x)) :
    Member 0 1 depth n (nativeProgram mesh shape x) (nativeCoordinates shape x) :=
  canonicalProgram_member n shape _ hx

def actualNode {depth : ℕ} (N precision mesh : ℕ) (root : Root) (tau : ℝ)
    (shape : Fin depth → StepShape) (p : NativeSlot shape → ℕ) : TypedNode :=
  let x := nativePrimeLogs N p
  realize depth (frozenRoot precision root tau (nativeRootCoordinate x))
    (nativeProgram mesh shape x) (nativeCoordinates shape x)

theorem actualNode_same_Q {depth : ℕ} (N precision mesh : ℕ) (root : Root) (tau : ℝ)
    (shape : Fin depth → StepShape) (p : NativeSlot shape → ℕ) :
    (actualNode N precision mesh root tau shape p).physical.total =
      frozenLevel precision
        (sourceRoot root tau (nativeRootCoordinate (nativePrimeLogs N p))).physical.total := by
  unfold actualNode
  rw [realize_total]
  rfl

theorem actualNode_selected_root_only {depth : ℕ}
    (N precision mesh : ℕ) (root : Root) (tau : ℝ)
    (shape : Fin depth → StepShape) (p : NativeSlot shape → ℕ) :
    selectedWord (actualNode N precision mesh root tau shape p).physical.slots =
      [nativeRootCoordinate (nativePrimeLogs N p)] := by
  unfold actualNode
  rw [realize_selected]
  simp [frozenRoot, sourceRoot, selectedWord]

/-- Every inherited cap lookup is evaluated on the same old prefix.
This identity includes equality/inherit data and makes no smoothness claim. -/
theorem actual_ancestor_choice {depth capDepth capMesh : ℕ}
    (N precision mesh : ℕ) (root : Root) (tau : ℝ)
    (shape : Fin depth → StepShape) (p : NativeSlot shape → ℕ)
    (P : P2PhysicalIncomingPrefixCells.CapPlan capDepth capMesh) (a b : ℝ) :
    P2PhysicalIncomingPrefixCells.incomingChoice P a b 1
        (markedWord (actualNode N precision mesh root tau shape p).physical) =
      P2PhysicalIncomingPrefixCells.incomingChoice P a b 1
        (markedWord (frozenRoot precision root tau
          (nativeRootCoordinate (nativePrimeLogs N p))).physical) := by
  apply realize_ancestor_choice
  simp [frozenRoot, sourceRoot]

/-- A query occurrence records its actual entire Program, not just the
integer generation paired with a fresh independent Primitive. -/
abbrev QueryOccurrence (mesh : ℕ) :=
  GraphVertex mesh 440 × FeedbackQuery × Part5OriginalUpsilon5CausalDictionary.FloorAtom

def occurrenceInput {mesh : ℕ} (n : TypedNode) (v : GraphVertex mesh 440)
    (z : Coordinates v.1.val) (q : FeedbackQuery) (next : Point) : Space q.primitive :=
  q.coordinate (realize v.1.val n v.2 z).physical next

theorem occurrence_query_exact {mesh : ℕ} (n : TypedNode) (v : GraphVertex mesh 440)
    (z : Coordinates v.1.val) (q : FeedbackQuery) (next : Point) :
    (perform (realize v.1.val n v.2 z).physical q.shape next).argument =
      (data q.primitive).query (occurrenceInput n v z q next) :=
  actual_child_query _ _ q

end
end ImbalancedChen.Part5OriginalH430NativeQueryPaths
