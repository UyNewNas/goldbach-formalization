import ImbalancedChen.Part5OriginalH430RequestedBranches

/-!
Concrete finite selected-request history, with computed predecessor indices
and products of ORIGINAL positive edge coefficients. SOURCE ONLY / UNCOMPILED.
This is the feedback-request history, not yet an equality with the complete
U3/U4 count source or a common 441-level analytic realization.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedHistory

noncomputable section
open Set
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches

/-- The full tagged path is retained even when two final products agree.
No caller supplies g, sigma, a source equality, or an analytic licence. -/
structure Occurrence (N : ℕ) where
  path : List (Edge N)
  current : Request
  remaining : ℕ

def origin {N : ℕ} (generation : ℕ) (r : Request) : Occurrence N := ⟨[],r,generation⟩

def prepend {N : ℕ} (e : Edge N) (o : Occurrence N) : Occurrence N :=
  ⟨e :: o.path, o.current, o.remaining⟩

def mark {N : ℕ} (o : Occurrence N) : ℝ := (o.path.map edgeWeight).prod

@[simp] theorem mark_origin {N : ℕ} (g : ℕ) (r : Request) : mark (origin (N := N) g r) = 1 := rfl

@[simp] theorem mark_prepend {N : ℕ} (e : Edge N) (o : Occurrence N) :
    mark (prepend e o) = edgeWeight e * mark o := rfl

theorem mark_pos {N : ℕ} (o : Occurrence N) : 0 < mark o := by
  have h (p : List (Edge N)) : 0 < (p.map edgeWeight).prod := by
    induction p with
    | nil => norm_num
    | cons e p ih => exact mul_pos (edgeWeight_pos e) ih
  exact h o.path

/-- Includes the current request and every selected descendant, with
list occurrences preserved. The finite fuel is the scalar generation,
not an arbitrary physical Program's depth or a reoptimized cutoff. -/
def history (N : ℕ) (Q : ℝ) : ℕ → Request → List (Occurrence N)
  | 0, r => [origin 0 r]
  | g+1, r => origin (g+1) r ::
      (children N Q g r).flatMap (fun e => (history N Q g (nextRequest r e)).map (prepend e))

def replay {N : ℕ} : Request → List (Edge N) → Request
  | r, [] => r
  | r, e::es => replay (nextRequest r e) es

/-- Every prefix uses its own actual state and the previous scalar table.
The predicate contains no desired error or count bound. -/
def ChosenPath (N : ℕ) (Q : ℝ) : ℕ → Request → List (Edge N) → Prop
  | _, _, [] => True
  | 0, _, _::_ => False
  | g+1, r, e::es => e ∈ children N Q g r ∧ ChosenPath N Q g (nextRequest r e) es

theorem history_facts {N g : ℕ} {Q : ℝ} {r : Request} {o : Occurrence N}
    (ho : o ∈ history N Q g r) :
    ChosenPath N Q g r o.path ∧ o.remaining + o.path.length = g ∧
      o.current = replay r o.path := by
  induction g generalizing r o with
  | zero =>
      have heq : o = origin 0 r := by simpa only [history,List.mem_singleton] using ho
      subst o
      exact ⟨trivial,rfl,rfl⟩
  | succ g ih =>
      rcases (show o = origin (g+1) r ∨ o ∈
        (children N Q g r).flatMap (fun e => (history N Q g (nextRequest r e)).map (prepend e)) by
          simpa only [history,List.mem_cons] using ho) with rfl | ho
      · exact ⟨trivial,by simp [origin],rfl⟩
      · obtain ⟨e,he,ho⟩ := List.mem_flatMap.mp ho
        obtain ⟨t,ht,rfl⟩ := List.mem_map.mp ho
        obtain ⟨hpath,hlen,hcurrent⟩ := ih ht
        refine ⟨⟨he,hpath⟩,?_,hcurrent⟩
        change t.remaining + (e::t.path).length = g+1
        simp only [List.length_cons]
        omega

theorem chosen_readValid {N g : ℕ} {Q : ℝ} {r : Request} {es : List (Edge N)}
    (hr : ReadValid r) (hs : ChosenPath N Q g r es) : ReadValid (replay r es) := by
  induction es generalizing g r with
  | nil => exact hr
  | cons e es ih =>
      cases g with
      | zero => exact False.elim hs
      | succ g => exact ih (child_readValid hr hs.1) hs.2

theorem replay_total {N : ℕ} (r : Request) (es : List (Edge N)) :
    (replay r es).node.physical.total = r.node.physical.total := by
  induction es generalizing r with
  | nil => rfl
  | cons e es ih => exact (ih (nextRequest r e)).trans (next_total r e)

theorem replay_selected {N : ℕ} (r : Request) (es : List (Edge N)) :
    selectedWord (replay r es).node.physical.slots = selectedWord r.node.physical.slots := by
  induction es generalizing r with
  | nil => rfl
  | cons e es ih => exact (ih (nextRequest r e)).trans (next_selected r e)

theorem replay_word {N : ℕ} (r : Request) (es : List (Edge N))
    (hr : word r.node.physical = r.old.map (physicalPrime N)) :
    word (replay r es).node.physical = (replay r es).old.map (physicalPrime N) := by
  induction es generalizing r with
  | nil => exact hr
  | cons e es ih => exact ih (nextRequest r e) (next_word e hr)

theorem replay_slots_prefix {N : ℕ} (r : Request) (es : List (Edge N)) :
    ∃ suffix, (replay r es).node.physical.slots = r.node.physical.slots ++ suffix := by
  induction es generalizing r with
  | nil => exact ⟨[],(List.append_nil _).symm⟩
  | cons e es ih =>
      obtain ⟨xs,hxs⟩ := P2EnhancedLowerFinitePhysicalGraph.perform_prefix
        r.node.physical (edgeShape e) (edgeCoordinates e)
      obtain ⟨ys,hys⟩ := ih (nextRequest r e)
      refine ⟨xs++ys,?_⟩
      change (replay (nextRequest r e) es).node.physical.slots = _
      simpa only [nextRequest,advance,hxs,List.append_assoc] using hys

/-- Every old prefix filter sees exactly the same marked input. This
is not an assertion that the COMPLETE source filter has been identified. -/
theorem replay_ancestor_filter {N : ℕ} (r : Request) (es : List (Edge N))
    (P : List Slot → Prop) :
    P ((replay r es).node.physical.slots.take r.node.physical.slots.length) ↔
      P r.node.physical.slots := by
  obtain ⟨xs,hxs⟩ := replay_slots_prefix r es
  simp [hxs]

/-- The concrete predecessor index is defined only for an active request.
A seed request is NOT silently mapped to generation429 or a wrapped index. -/
def predecessor (remaining : ℕ) : Option (Fin 430) :=
  if h : 0 < remaining ∧ remaining ≤ 430 then some ⟨remaining-1,by omega⟩ else none

theorem predecessor_exact {remaining : ℕ} (h0 : 0 < remaining) (h430 : remaining ≤ 430) :
    ∃ g : Fin 430, predecessor remaining = some g ∧ g.val+1 = remaining := by
  refine ⟨⟨remaining-1,by omega⟩,?_,by omega⟩
  simp only [predecessor,dif_pos ⟨h0,h430⟩]

/-- Use precisely the existing U3/U4 frozen root and its original root
prime. A root-level positive mark may later scale the whole history. -/
def rootRequest (N precision : ℕ) (root : Root) (tau : ℝ) (p : ℕ) : Request :=
  ⟨frozenRoot precision root tau (physicalPrime N p), [p], .scalar⟩

def rootHistory (N precision : ℕ) (root : Root) (tau : ℝ) (p : ℕ) : List (Occurrence N) :=
  history N (rootQ N precision root tau p) 430 (rootRequest N precision root tau p)

theorem rootHistory_computed_data {N precision : ℕ} {root : Root} {tau : ℝ} {p : ℕ}
    {o : Occurrence N} (ho : o ∈ rootHistory N precision root tau p) :
    o.remaining + o.path.length = 430 ∧ 0 < mark o ∧ ReadValid o.current ∧
    (0 < o.remaining → ∃ g : Fin 430, predecessor o.remaining = some g ∧ g.val+1 = o.remaining) := by
  obtain ⟨hpath,hlen,hcurrent⟩ := history_facts ho
  refine ⟨hlen,mark_pos o,?_,fun hpos => predecessor_exact hpos (by omega)⟩
  rw [hcurrent]
  exact chosen_readValid (r := rootRequest N precision root tau p) trivial hpath

theorem rootHistory_sameQ {N precision : ℕ} {root : Root} {tau : ℝ} {p : ℕ}
    {o : Occurrence N} (ho : o ∈ rootHistory N precision root tau p) :
    (N : ℝ)^o.current.node.physical.total = rootQ N precision root tau p := by
  rw [(history_facts ho).2.2,replay_total]
  rfl

theorem rootHistory_integer_word {N precision : ℕ} {root : Root} {tau : ℝ} {p : ℕ}
    {o : Occurrence N} (ho : o ∈ rootHistory N precision root tau p) :
    word o.current.node.physical = o.current.old.map (physicalPrime N) := by
  rw [(history_facts ho).2.2]
  apply replay_word
  simp [rootRequest,frozenRoot,sourceRoot,word]

theorem rootHistory_selected_root {N precision : ℕ} {root : Root} {tau : ℝ} {p : ℕ}
    {o : Occurrence N} (ho : o ∈ rootHistory N precision root tau p) :
    selectedWord o.current.node.physical.slots = [physicalPrime N p] := by
  rw [(history_facts ho).2.2,replay_selected]
  simp [rootRequest,frozenRoot,sourceRoot,selectedWord]

/-- A level is a list of occurrences, not a set of products. The complete
node pool is NEVER summed as though all generations were simultaneous. -/
def levelRequests (N precision : ℕ) (root : Root) (tau : ℝ) (p generation : ℕ) :
    List (Occurrence N) :=
  (rootHistory N precision root tau p).filter (fun o => decide (o.remaining = generation))

abbrev LevelIndex (N precision : ℕ) (root : Root) (tau : ℝ) (p generation : ℕ) :=
  Fin (levelRequests N precision root tau p generation).length

def levelOccurrence {N precision : ℕ} {root : Root} {tau : ℝ} {p generation : ℕ}
    (i : LevelIndex N precision root tau p generation) : Occurrence N :=
  (levelRequests N precision root tau p generation).get i

def levelMark {N precision : ℕ} {root : Root} {tau : ℝ} {p generation : ℕ}
    (i : LevelIndex N precision root tau p generation) : ℝ := mark (levelOccurrence i)

theorem levelOccurrence_source {N precision : ℕ} {root : Root} {tau : ℝ} {p generation : ℕ}
    (i : LevelIndex N precision root tau p generation) :
    levelOccurrence i ∈ rootHistory N precision root tau p ∧
      (levelOccurrence i).remaining = generation := by
  have hm : levelOccurrence i ∈ levelRequests N precision root tau p generation :=
    List.get_mem _ _
  simpa only [levelRequests,List.mem_filter,decide_eq_true_eq] using hm

/-- Concrete nonnegative sigma and immutable predecessor for each indexed
occurrence at a level. No claim identifies this indexed list with the
complete original count source, and no analytic estimate is a premise. -/
theorem level_computed_assignment {N precision : ℕ} {root : Root} {tau : ℝ}
    {p generation : ℕ} (i : LevelIndex N precision root tau p generation)
    (hg : 0 < generation) :
    0 < levelMark i ∧ ∃ g : Fin 430,
      predecessor (levelOccurrence i).remaining = some g ∧ g.val+1 = generation := by
  obtain ⟨ho,he⟩ := levelOccurrence_source i
  have h := rootHistory_computed_data ho
  have hpos : 0 < (levelOccurrence i).remaining := by rwa [he]
  obtain ⟨g,hg1,hg2⟩ := h.2.2.2 hpos
  exact ⟨mark_pos _,g,hg1,hg2.trans he⟩

end
end ImbalancedChen.Part5OriginalH430RequestedHistory
