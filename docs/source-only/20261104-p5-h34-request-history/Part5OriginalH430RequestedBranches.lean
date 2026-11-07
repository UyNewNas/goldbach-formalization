import ImbalancedChen.Part5OriginalH430RequestedReads

/-!
Literal positive feedback requests. SOURCE ONLY / UNCOMPILED.
Only the original winner is expanded. Each edge fixes its own original
coefficient, request kind, physical StepShape and ordered prime append.
No arbitrary generation map, mark, admission certificate or count bound
is a field. Endpoint/repeat corrections remain in the earlier packets.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedBranches

noncomputable section
open Set
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430PrimeChildAdmission Part5OriginalH430IntegerItineraries
open Part5OriginalH430BankSlotTargets Part5OriginalH430FixedReadDictionary
open Part5OriginalH430RequestedReads
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430FixedReadRows
open P2OriginalChildPhysicalNormalization

/-- Component tags remain distinct even for equal prime products/queries. -/
inductive Edge (N : ℕ) where
  | retained (cell : Fin 200)
  | buchstab (upper : Bool) (prime : Fin (N+1))
  | w1Fixed (target : Fin 7) (anchor : Fin 10)
  | w1Prime (target : Fin 7) (anchor : Fin 10) (prime : Fin (N+1))
  | w2Fixed (bank : Fin 36) (anchor : Bool)
  | w2Prime (bank : Fin 36) (piece : Fin 3) (prime : Fin (N+1))
  | w2Pair (bank : Fin 36) (piece : Fin 4) (primes : Fin (N+1) × Fin (N+1))
  deriving DecidableEq

def edgeShape {N : ℕ} : Edge N → StepShape
  | .retained _ => .retain
  | .buchstab true _ => .buchstabUpper
  | .buchstab false _ => .buchstabLower
  | .w1Fixed i j => .w1Fixed i j
  | .w1Prime i j _ => .w1Singleton i j
  | .w2Fixed j b => .w2Fixed j b
  | .w2Prime j k _ => .w2Singleton j k
  | .w2Pair j k _ => .w2Pair j k

def edgePrimes {N : ℕ} : Edge N → IntegerPoint
  | .buchstab _ p | .w1Prime _ _ p | .w2Prime _ _ p => ![p.val,1]
  | .w2Pair _ _ p => ![p.1.val,p.2.val]
  | _ => ![1,1]

def edgeCoordinates {N : ℕ} (e : Edge N) : Point :=
  fun i => physicalPrime N (edgePrimes e i)

def edgeMode {N : ℕ} : Edge N → ReadMode
  | .retained i => .cell i
  | .w1Fixed _ j => .cell (w1Cell j)
  | .w2Fixed j b => .cell (w2Cell j b)
  | _ => .scalar

def edgeWeight {N : ℕ} : Edge N → ℝ
  | .retained _ | .buchstab _ _ | .w1Fixed _ _ => 1
  | .w1Prime _ _ _ => 1/2
  | .w2Fixed _ true => 4/5
  | .w2Fixed _ false | .w2Prime _ _ _ | .w2Pair _ _ _ => 1/5

theorem edgeWeight_pos {N : ℕ} (e : Edge N) : 0 < edgeWeight e := by
  cases e with
  | w2Fixed j b => cases b <;> norm_num [edgeWeight]
  | _ => norm_num [edgeWeight]

def nextRequest {N : ℕ} (r : Request) (e : Edge N) : Request :=
  ⟨advance r.node (edgeShape e) (edgeCoordinates e),
    r.old ++ appendedWord (edgeShape e) (edgePrimes e), edgeMode e⟩

/-- All single/pair sums are the EXISTING strict production carriers. -/
def w1Edges (N : ℕ) (Q : ℝ) (r : Request) (i : Fin 7) (j : Fin 10) : List (Edge N) :=
  (singleChildren (.w1 i j) N Q r.old r.node.physical.ceiling).toList.map (.w1Prime i j)

def w2SingleEdges (N : ℕ) (Q : ℝ) (r : Request) (j : Fin 36) (k : Fin 3) : List (Edge N) :=
  (singleChildren (.w2 j k) N Q r.old r.node.physical.ceiling).toList.map (.w2Prime j k)

def w2PairEdges (N : ℕ) (Q : ℝ) (r : Request) (j : Fin 36) (k : Fin 4) : List (Edge N) :=
  (pairChildren j k N Q r.old r.node.physical.ceiling).toList.map (.w2Pair j k)

def bankEdges (N : ℕ) (Q : ℝ) (r : Request) : Original106Action → List (Edge N)
  | .inl (i,j) => .w1Fixed i j :: w1Edges N Q r i j
  | .inr j => [.w2Fixed j true, .w2Fixed j false] ++
      w2SingleEdges N Q r j 0 ++ w2SingleEdges N Q r j 1 ++ w2SingleEdges N Q r j 2 ++
      w2PairEdges N Q r j 0 ++ w2PairEdges N Q r j 1 ++
      w2PairEdges N Q r j 2 ++ w2PairEdges N Q r j 3

def branchEdges (N : ℕ) (Q : ℝ) (r : Request) (i : Fin 200) : Choice → List (Edge N)
  | .retained => [.retained i]
  | .buchstab =>
      (singleChildren (.buchstab r.node.upper r.node.physical.argument)
        N Q r.old r.node.physical.ceiling).toList.map (.buchstab r.node.upper)
  | .bank k => bankEdges N Q r (actionOfSlot k)

/-- Resolve at g+1, choose against iterate(g), then generate ONLY its
components. There is no union over unselected alternatives. -/
def children (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) : List (Edge N) :=
  match resolve (g+1) r with
  | none => []
  | some i => branchEdges N Q r i (roundDecision (iterate g) r.node.upper i).choice

theorem child_source {N g : ℕ} {Q : ℝ} {r : Request} {e : Edge N}
    (he : e ∈ children N Q g r) :
    ∃ i c, Selected g r i c ∧ e ∈ branchEdges N Q r i c := by
  unfold children at he
  cases hi : resolve (g+1) r with
  | none => simp only [hi, List.not_mem_nil] at he
  | some i => exact ⟨i, _, ⟨hi,rfl⟩, by simpa only [hi] using he⟩

theorem exterior_children_empty {N g : ℕ} {Q : ℝ} {r : Request}
    (h : resolve (g+1) r = none) :
    children N Q g r = [] ∧ requestValue (iterate (g+1)) r = 0 :=
  ⟨by simp only [children,h], resolve_none_value h⟩

private theorem retained_mem_branch {N : ℕ} {Q : ℝ} {r : Request}
    {i j : Fin 200} {c : Choice} (he : Edge.retained j ∈ branchEdges N Q r i c) :
    j = i ∧ c = .retained := by
  cases c with
  | retained =>
      refine ⟨?_,rfl⟩
      simpa only [branchEdges, List.mem_singleton, Edge.retained.injEq] using he
  | buchstab => simp [branchEdges] at he
  | bank k =>
      cases ha : actionOfSlot k with
      | inl ij => rcases ij with ⟨a,b⟩; simp [branchEdges,ha,bankEdges,w1Edges] at he
      | inr a => simp [branchEdges,ha,bankEdges,w2SingleEdges,w2PairEdges] at he

/-- A carried specified cell is never silently converted back to a
scalar lookup. Dynamic successors intentionally remain scalar requests. -/
theorem child_readValid {N g : ℕ} {Q : ℝ} {r : Request} {e : Edge N}
    (hr : ReadValid r) (he : e ∈ children N Q g r) : ReadValid (nextRequest r e) := by
  cases e with
  | retained j =>
      obtain ⟨i,c,hsel,he'⟩ := child_source he
      obtain ⟨rfl,_⟩ := retained_mem_branch he'
      exact resolve_contains hr hsel.1
  | w1Fixed i j => exact w1Cell_contains j
  | w2Fixed j b => exact w2Cell_contains j b
  | buchstab b p => cases b <;> trivial
  | w1Prime i j p => trivial
  | w2Prime j k p => trivial
  | w2Pair j k p => trivial

@[simp] theorem next_total {N : ℕ} (r : Request) (e : Edge N) :
    (nextRequest r e).node.physical.total = r.node.physical.total :=
  perform_total _ _ _

@[simp] theorem next_selected {N : ℕ} (r : Request) (e : Edge N) :
    selectedWord (nextRequest r e).node.physical.slots = selectedWord r.node.physical.slots :=
  perform_selected _ _ _

theorem next_old_slots {N : ℕ} (r : Request) (e : Edge N) :
    (nextRequest r e).node.physical.slots.take r.node.physical.slots.length = r.node.physical.slots :=
  perform_old_slots _ _ _

theorem next_word {N : ℕ} {r : Request} (e : Edge N)
    (hr : word r.node.physical = r.old.map (physicalPrime N)) :
    word (nextRequest r e).node.physical = (nextRequest r e).old.map (physicalPrime N) := by
  change word (perform r.node.physical (edgeShape e) (edgeCoordinates e)) = _
  rw [perform_word, hr, List.map_append]

/-- Each requested value has a concrete coefficient row. Cell indices
are labels of reads, not assertions of open-atom membership. -/
def requestAtom (r : Request) : RowAtom → ℝ :=
  match r.mode with
  | .cell i => fun b => if b = (if r.node.upper then .inl (.inl i) else .inr (.inl i)) then 1 else 0
  | .scalar => fun b =>
      match b with
      | .inl a => if r.node.upper then (tableAtomSet false a).indicator (fun _ => 1) r.node.physical.argument else 0
      | .inr a => if r.node.upper then 0 else (tableAtomSet true a).indicator (fun _ => 1) r.node.physical.argument

private theorem indicator_one_mul (lower : Bool) (b : FloorAtom) (s v : ℝ) :
    (tableAtomSet lower b).indicator (fun _ => (1 : ℝ)) s * v =
      (tableAtomSet lower b).indicator (fun _ => v) s := by
  by_cases hb : s ∈ tableAtomSet lower b <;> simp [hb]

theorem requestAtom_value (t : Table) (r : Request) :
    (∑ b : RowAtom, requestAtom r b * oldAtomValue (t true) (t false) b) = requestValue t r := by
  cases hm : r.mode with
  | cell i => cases hu : r.node.upper <;> simp [requestAtom,requestValue,hm,hu,oldAtomValue,floorAtomValue,ite_mul]
  | scalar =>
      cases hu : r.node.upper
      all_goals
        simp only [requestAtom,requestValue,hm,hu,Fintype.sum_sum_type,
          Bool.false_eq_true,if_false,if_true,Bool.not_false,Bool.not_true,
          oldAtomValue,zero_mul,Finset.sum_const_zero,zero_add,add_zero,tableFunction]
        apply Finset.sum_congr rfl
        intro b _
        exact indicator_one_mul _ _ _ _

/-- Coefficients are applied to actual child words BEFORE any reindexing
by products. Repeated parent histories remain different list positions. -/
def edgeRow {N : ℕ} (Q : ℝ) (r : Request) (es : List (Edge N)) (b : RowAtom) : ℝ :=
  (es.map (fun e => edgeWeight e * thetaAtom N Q (parentProduct (nextRequest r e).old) *
    requestAtom (nextRequest r e) b)).sum

def edgeValue {N : ℕ} (Q : ℝ) (t : Table) (r : Request) (es : List (Edge N)) : ℝ :=
  (es.map (fun e => edgeWeight e * thetaAtom N Q (parentProduct (nextRequest r e).old) *
    requestValue t (nextRequest r e))).sum

theorem edgeRow_value {N : ℕ} (Q : ℝ) (t : Table) (r : Request) (es : List (Edge N)) :
    (∑ b : RowAtom, edgeRow Q r es b * oldAtomValue (t true) (t false) b) =
      edgeValue Q t r es := by
  induction es with
  | nil => simp [edgeRow,edgeValue]
  | cons e es ih =>
      simp only [edgeRow,edgeValue,List.map_cons,List.sum_cons,add_mul,Finset.sum_add_distrib] at *
      rw [ih]
      congr 1
      rw [show (∑ b : RowAtom,
        (edgeWeight e * thetaAtom N Q (parentProduct (nextRequest r e).old) * requestAtom (nextRequest r e) b) *
          oldAtomValue (t true) (t false) b) =
        edgeWeight e * thetaAtom N Q (parentProduct (nextRequest r e).old) *
          ∑ b : RowAtom, requestAtom (nextRequest r e) b * oldAtomValue (t true) (t false) b by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring]
      rw [requestAtom_value]

/-- Exact unchanged-parent term for retention, using its SPECIFIED cell. -/
theorem retained_edgeValue (N : ℕ) (Q : ℝ) (t : Table) (r : Request) (i : Fin 200) :
    edgeValue Q t r [Edge.retained (N := N) i] =
      thetaAtom N Q (parentProduct r.old) * floorValue (t r.node.upper) i := by
  simp [edgeValue,nextRequest,edgeWeight,edgeShape,edgeMode,appendedWord,
    advance,childUpper,perform,requestValue]

end
end ImbalancedChen.Part5OriginalH430RequestedBranches
