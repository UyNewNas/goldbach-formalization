import ImbalancedChen.P2OriginalPrioritySerialQueue
import ImbalancedChen.P2OriginalAdaptiveForestSourceIdentity

/-!
SOURCEONLY / UNCOMPILED / P2.4 OPEN.

A source-indexed adaptive forest and the actual priority/serial transition.
Every branch is the original relative-width/floor-midpoint split, never an
arbitrary partition. Cached lower/upper totals follow the producer's exact
subtract-parent/add-side0/add-side1 assignments. The proved invariant keeps
ALL leaves, while the heap projection keeps only positive uncertainty.

`enclose` is an unevaluated Q80 evaluator input, not an enclosure-soundness or
endpoint premise. Identifying it with every branch of the original Python
evaluator, proving its analytic soundness and authenticating/evaluating the
historical two-million-step run remain open.
-/

namespace ImbalancedChen.P2OriginalPriorityForestLedgerSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open P4AOriginalClosedTreeStructuralAggregationSourceOnly
open P4AClosedCutTreePositionalChargeBindingSourceOnly
open P2OriginalAdaptiveSourceSplitSourceOnly
open P2OriginalAdaptiveForestSourceIdentitySourceOnly
open P2OriginalPrioritySerialQueueSourceOnly

/-- Indexed by the RAW source box. The width assertion is the exact original
assertion before a split, and both children have their literal source boxes. -/
inductive SourceTree (enclose : SeedCell → Bounds) : SeedCell → Type where
  | leaf (c : SeedCell) (serial : ℕ) : SourceTree enclose c
  | split (c : SeedCell)
      (width : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c))
      (left : SourceTree enclose (sourceLeft c))
      (right : SourceTree enclose (sourceRight c)) : SourceTree enclose c

def treeEntries {enclose : SeedCell → Bounds} {c : SeedCell} :
    SourceTree enclose c → List Entry
  | .leaf c serial => [⟨c,enclose c,serial⟩]
  | .split _ _ left right => treeEntries left ++ treeEntries right

def eraseTree {enclose : SeedCell → Bounds} {c : SeedCell} :
    SourceTree enclose c → ClosedCutTree
  | .leaf _ _ => .leaf
  | .split c _ left right =>
      .split (originalAxis c) (originalMidpoint c) (eraseTree left) (eraseTree right)

/-- No later split is made on the skeleton's unnormalized h-lower boxes. -/
theorem tree_integer_boxes {enclose : SeedCell → Bounds} {c : SeedCell}
    (tree : SourceTree enclose c) :
    integerLeafBoxes (eraseTree tree) c.1 c.2 = (treeEntries tree).map Entry.cell := by
  induction tree with
  | leaf c serial => rfl
  | split c width left right ihL ihR =>
      have hmid := originalMidpoint_interior c width
      have hl : leftIntegerUpper c.2 (originalAxis c) (originalMidpoint c) =
          (sourceLeft c).2 := by
        simp [leftIntegerUpper,sourceLeft,min_eq_right hmid.2.le]
      have hr : rightIntegerLower c.1 (originalAxis c) (originalMidpoint c) =
          (sourceRight c).1 := by
        simp [rightIntegerLower,sourceRight,max_eq_right hmid.1.le]
      simpa only [eraseTree,integerLeafBoxes,treeEntries,List.map_append,hl,hr,
        sourceLeft,sourceRight] using congrArg₂ List.append ihL ihR

inductive SourceForest (enclose : SeedCell → Bounds) : List SeedCell → Type where
  | nil : SourceForest enclose []
  | cons {c : SeedCell} {cs : List SeedCell}
      (tree : SourceTree enclose c) (rest : SourceForest enclose cs) :
      SourceForest enclose (c :: cs)

def entries {enclose : SeedCell → Bounds} {cs : List SeedCell} :
    SourceForest enclose cs → List Entry
  | .nil => []
  | .cons tree rest => treeEntries tree ++ entries rest

def eraseForest {enclose : SeedCell → Bounds} {cs : List SeedCell} :
    SourceForest enclose cs → List ClosedCutTree
  | .nil => []
  | .cons tree rest => eraseTree tree :: eraseForest rest

theorem eraseForest_length {enclose : SeedCell → Bounds} {cs : List SeedCell}
    (forest : SourceForest enclose cs) : (eraseForest forest).length = cs.length := by
  induction forest with
  | nil => rfl
  | cons tree rest ih => simpa only [eraseForest,List.length_cons] using congrArg Nat.succ ih

theorem forest_integer_boxes {enclose : SeedCell → Bounds} {cs : List SeedCell}
    (forest : SourceForest enclose cs) :
    sourceIntegerForest (eraseForest forest) cs = (entries forest).map Entry.cell := by
  induction forest with
  | nil => rfl
  | cons tree rest ih =>
      simp only [eraseForest,sourceIntegerForest,entries,List.map_append,
        tree_integer_boxes,ih]

def completeTree {enclose : SeedCell → Bounds}
    (forest : SourceForest enclose initialSeeds) : ClosedCutTree :=
  originalAdaptiveTree (eraseForest forest) (by
    rw [eraseForest_length,initialSeeds_eq_records,records_length])

/-- Complete ordered leaf identity, inherited from the original21 raw seeds.
In particular zero-error and empty portions do not vanish in the heap filter. -/
theorem completeTree_closedLeaves {enclose : SeedCell → Bounds}
    (forest : SourceForest enclose initialSeeds) :
    closedLeaves (completeTree forest) compactRegion =
      (entries forest).map (fun p => rootCell p.cell) := by
  unfold completeTree
  rw [originalAdaptiveTree_closedLeaves,forest_integer_boxes,List.map_map]

theorem complete_integral_identity {enclose : SeedCell → Bounds}
    (forest : SourceForest enclose initialSeeds) :
    originalCompactThirdCorrection =
      ((entries forest).map (fun p => ∫ t in rootCell p.cell, compactKernel t)).sum := by
  rw [originalCompactThirdCorrection_eq_sum_closedLeaves (completeTree forest),
    completeTree_closedLeaves,List.map_map]

def lowerSum (xs : List Entry) : ℤ := (xs.map (fun p => p.bounds.lower)).sum
def upperSum (xs : List Entry) : ℤ := (xs.map (fun p => p.bounds.upper)).sum
def errorSum (xs : List Entry) : ℤ := (xs.map error).sum

theorem lowerSum_append (xs ys : List Entry) :
    lowerSum (xs ++ ys) = lowerSum xs + lowerSum ys := by
  simp [lowerSum]

theorem upperSum_append (xs ys : List Entry) :
    upperSum (xs ++ ys) = upperSum xs + upperSum ys := by
  simp [upperSum]

theorem errorSum_eq_difference (xs : List Entry) :
    errorSum xs = upperSum xs - lowerSum xs := by
  induction xs with
  | nil => simp [errorSum,upperSum,lowerSum]
  | cons p ps ih =>
      change error p + errorSum ps =
        (p.bounds.upper + upperSum ps) - (p.bounds.lower + lowerSum ps)
      rw [ih]
      unfold error
      omega

/-- Well-formed zero-error intervals leave the heap without removing their
charges from either cached total. Their uncertainty contribution is zero. -/
theorem errorSum_heapContents (xs : List Entry)
    (hbound : ∀ p ∈ xs, p.bounds.lower ≤ p.bounds.upper) :
    errorSum (heapContents xs) = errorSum xs := by
  revert hbound
  induction xs with
  | nil => intro hbound; simp [heapContents,errorSum]
  | cons p ps ih =>
      intro hbound
      have hp := hbound p (by simp)
      have ht := ih (by
        intro q hq
        exact hbound q (List.mem_cons.mpr (Or.inr hq)))
      by_cases ha : active p
      · simpa [heapContents,ha,errorSum] using congrArg (fun n => error p + n) ht
      · have he : error p = 0 := by
          unfold active at ha
          unfold error
          omega
        simpa [heapContents,ha,errorSum,he] using ht

theorem tree_entry_enclose {enclose : SeedCell → Bounds} {c : SeedCell}
    (tree : SourceTree enclose c) (p : Entry) (hp : p ∈ treeEntries tree) :
    p.bounds = enclose p.cell := by
  induction tree generalizing p with
  | leaf c serial =>
      have hp' : p = ⟨c,enclose c,serial⟩ := by simpa [treeEntries] using hp
      subst p
      rfl
  | split c width left right ihL ihR =>
      rcases List.mem_append.mp hp with hp | hp
      · exact ihL p hp
      · exact ihR p hp

theorem entry_enclose {enclose : SeedCell → Bounds} {cs : List SeedCell}
    (forest : SourceForest enclose cs) (p : Entry) (hp : p ∈ entries forest) :
    p.bounds = enclose p.cell := by
  induction forest generalizing p with
  | nil => simp [entries] at hp
  | cons tree rest ih =>
      rcases List.mem_append.mp hp with hp | hp
      · exact tree_entry_enclose tree p hp
      · exact ih p hp

/-- A genuine source leaf replacement, at any depth, preserving every other
position. Child serials follow side0 then side1, including skipped heap puts. -/
inductive TreeRefines (enclose : SeedCell → Bounds) (s : ℕ) :
    Entry → {c : SeedCell} → SourceTree enclose c → SourceTree enclose c → Prop where
  | root (c : SeedCell) (old : ℕ)
      (width : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c)) :
      TreeRefines enclose s ⟨c,enclose c,old⟩ (.leaf c old)
        (.split c width
          (.leaf (sourceLeft c) (issueSerial enclose (sourceLeft c) s))
          (.leaf (sourceRight c)
            (issueSerial enclose (sourceRight c) (advance enclose (sourceLeft c) s))))
  | left {p : Entry} {c : SeedCell} {left left' : SourceTree enclose (sourceLeft c)}
      (width : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c))
      (right : SourceTree enclose (sourceRight c))
      (refines : TreeRefines enclose s p left left') :
      TreeRefines enclose s p (.split c width left right) (.split c width left' right)
  | right {p : Entry} {c : SeedCell} {right right' : SourceTree enclose (sourceRight c)}
      (width : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c))
      (left : SourceTree enclose (sourceLeft c))
      (refines : TreeRefines enclose s p right right') :
      TreeRefines enclose s p (.split c width left right) (.split c width left right')

theorem tree_refines_entries {enclose : SeedCell → Bounds} {s : ℕ} {p : Entry}
    {c : SeedCell} {tree tree' : SourceTree enclose c}
    (h : TreeRefines enclose s p tree tree') :
    ∃ pre post, treeEntries tree = pre ++ p :: post ∧
      treeEntries tree' = pre ++ children enclose s p.cell ++ post := by
  induction h with
  | root c old width => exact ⟨[],[],rfl,by simp [treeEntries,children,issue]⟩
  | left width right h ih =>
      obtain ⟨pre,post,hpre,hpost⟩ := ih
      exact ⟨pre,post ++ treeEntries right,by
        simp only [treeEntries,hpre,List.append_assoc,List.cons_append],by
        simp only [treeEntries,hpost,List.append_assoc]⟩
  | right width left h ih =>
      obtain ⟨pre,post,hpre,hpost⟩ := ih
      exact ⟨treeEntries left ++ pre,post,by
        simp only [treeEntries,hpre,List.append_assoc],by
        simp only [treeEntries,hpost,List.append_assoc]⟩

inductive ForestRefines (enclose : SeedCell → Bounds) (s : ℕ) (p : Entry) :
    {cs : List SeedCell} → SourceForest enclose cs → SourceForest enclose cs → Prop where
  | here {c : SeedCell} {cs : List SeedCell} {tree tree' : SourceTree enclose c}
      (rest : SourceForest enclose cs) (h : TreeRefines enclose s p tree tree') :
      ForestRefines enclose s p (.cons tree rest) (.cons tree' rest)
  | there {c : SeedCell} {cs : List SeedCell} (tree : SourceTree enclose c)
      {rest rest' : SourceForest enclose cs} (h : ForestRefines enclose s p rest rest') :
      ForestRefines enclose s p (.cons tree rest) (.cons tree rest')

theorem forest_refines_entries {enclose : SeedCell → Bounds} {s : ℕ} {p : Entry}
    {cs : List SeedCell} {forest forest' : SourceForest enclose cs}
    (h : ForestRefines enclose s p forest forest') :
    ∃ pre post, entries forest = pre ++ p :: post ∧
      entries forest' = pre ++ children enclose s p.cell ++ post := by
  induction h with
  | here rest h =>
      obtain ⟨pre,post,hpre,hpost⟩ := tree_refines_entries h
      exact ⟨pre,post ++ entries rest,by
        simp only [entries,hpre,List.append_assoc,List.cons_append],by
        simp only [entries,hpost,List.append_assoc]⟩
  | there tree h ih =>
      obtain ⟨pre,post,hpre,hpost⟩ := ih
      exact ⟨treeEntries tree ++ pre,post,by
        simp only [entries,hpre,List.append_assoc],by
        simp only [entries,hpost,List.append_assoc]⟩

/-- Every selected actual leaf can be split inside its existing source tree;
the next tree is constructed rather than supplied as a correspondence port. -/
theorem tree_refinement_exists {enclose : SeedCell → Bounds} {c : SeedCell}
    (tree : SourceTree enclose c) (s : ℕ) (p : Entry)
    (hp : p ∈ treeEntries tree)
    (width : p.cell.1 (originalAxis p.cell) + 2 ≤ p.cell.2 (originalAxis p.cell)) :
    ∃ tree', TreeRefines enclose s p tree tree' := by
  induction tree generalizing p with
  | leaf c serial =>
      have hp' : p = ⟨c,enclose c,serial⟩ := by simpa [treeEntries] using hp
      subst p
      exact ⟨_,TreeRefines.root c serial width⟩
  | split c oldWidth left right ihL ihR =>
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨left',hleft⟩ := ihL p hp width
        exact ⟨_,TreeRefines.left oldWidth right hleft⟩
      · obtain ⟨right',hright⟩ := ihR p hp width
        exact ⟨_,TreeRefines.right oldWidth left hright⟩

theorem forest_refinement_exists {enclose : SeedCell → Bounds} {cs : List SeedCell}
    (forest : SourceForest enclose cs) (s : ℕ) (p : Entry)
    (hp : p ∈ entries forest)
    (width : p.cell.1 (originalAxis p.cell) + 2 ≤ p.cell.2 (originalAxis p.cell)) :
    ∃ forest', ForestRefines enclose s p forest forest' := by
  induction forest generalizing p with
  | nil => simp [entries] at hp
  | cons tree rest ih =>
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨tree',h⟩ := tree_refinement_exists tree s p hp width
        exact ⟨_,ForestRefines.here rest h⟩
      · obtain ⟨rest',h⟩ := ih p hp width
        exact ⟨_,ForestRefines.there tree h⟩

/-- The cached sums are the full source sums, not sums over heap entries. -/
theorem refine_sum_updates {enclose : SeedCell → Bounds} {s : ℕ} {p : Entry}
    {cs : List SeedCell} {forest forest' : SourceForest enclose cs}
    (h : ForestRefines enclose s p forest forest') :
    lowerSum (entries forest') = lowerSum (entries forest) - p.bounds.lower +
        lowerSum (children enclose s p.cell) ∧
    upperSum (entries forest') = upperSum (entries forest) - p.bounds.upper +
        upperSum (children enclose s p.cell) ∧
    (entries forest').length = (entries forest).length + 1 := by
  obtain ⟨pre,post,hpre,hpost⟩ := forest_refines_entries h
  rw [hpre,hpost]
  simp only [lowerSum_append,upperSum_append,lowerSum,upperSum,List.map_cons,
    List.sum_cons,List.length_append,List.length_cons,children,List.length_nil]
  omega

private theorem perm_move_parent (pre post : List Entry) (p : Entry) :
    (pre ++ p :: post).Perm (p :: (pre ++ post)) := by
  induction pre with
  | nil => exact List.Perm.refl _
  | cons a pre ih =>
      exact (List.Perm.cons a ih).trans (List.Perm.swap a p (pre ++ post))

/-- Exact multiset update of the heap, proved from the full source-tree
replacement and the specified pop. No arbitrary heap/source alignment is
assumed. The output includes precisely the positive-width children. -/
theorem refine_heap_contents {enclose : SeedCell → Bounds} {s : ℕ} {p : Entry}
    {cs : List SeedCell} {forest forest' : SourceForest enclose cs} {rest : List Entry}
    (h : ForestRefines enclose s p forest forest')
    (hpop : popBest (heapContents (entries forest)) = some (p,rest)) :
    (heapContents (entries forest')).Perm
      (rest ++ heapContents (children enclose s p.cell)) := by
  obtain ⟨pre,post,hpre,hpost⟩ := forest_refines_entries h
  have hp : active p := popped_active _ _ _ hpop
  have hold : heapContents (entries forest) =
      heapContents pre ++ p :: heapContents post := by
    rw [hpre]
    simp [heapContents,List.filter_append,hp]
  have hnew : heapContents (entries forest') =
      heapContents pre ++ heapContents (children enclose s p.cell) ++ heapContents post := by
    rw [hpost]
    simp only [heapContents,List.filter_append]
  have hremove := (popBest_spec _ _ _ hpop).1
  rw [hold] at hremove
  have hrest : rest.Perm (heapContents pre ++ heapContents post) :=
    (hremove.symm.trans (perm_move_parent _ _ _)).cons_inv
  rw [hnew]
  have hmove :
      (heapContents pre ++ heapContents (children enclose s p.cell) ++ heapContents post).Perm
        (heapContents (children enclose s p.cell) ++ (heapContents pre ++ heapContents post)) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := heapContents pre)
        (l₂ := heapContents (children enclose s p.cell))).append_right (heapContents post)
  exact hmove.trans ((hrest.symm.append_left _).trans (List.perm_append_comm))

/-- Initialization follows initial_cells in source order, incrementing only
for heap insertions. Every evaluated seed is retained in the forest. -/
def seedForest (enclose : SeedCell → Bounds) :
    (cs : List SeedCell) → ℕ → SourceForest enclose cs × ℕ
  | [],s => (.nil,s)
  | c :: cs,s =>
      let rest := seedForest enclose cs (advance enclose c s)
      (.cons (.leaf c (issueSerial enclose c s)) rest.1,rest.2)

theorem seedForest_entries_length (enclose : SeedCell → Bounds) (cs : List SeedCell)
    (s : ℕ) : (entries (seedForest enclose cs s).1).length = cs.length := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
      simp only [seedForest,entries,treeEntries,List.length_append,List.length_cons,
        List.length_nil]
      rw [ih]
      omega

theorem seedForest_serial (enclose : SeedCell → Bounds) (cs : List SeedCell) (s : ℕ) :
    s ≤ (seedForest enclose cs s).2 ∧
      ∀ p ∈ entries (seedForest enclose cs s).1,
        p.serial ≤ (seedForest enclose cs s).2 := by
  induction cs generalizing s with
  | nil => exact ⟨le_rfl,by simp [seedForest,entries]⟩
  | cons c cs ih =>
      obtain ⟨hnext,hbound⟩ := ih (advance enclose c s)
      refine ⟨(advance_mono enclose c s).trans hnext,?_⟩
      intro p hp
      change p ∈ [⟨c,enclose c,issueSerial enclose c s⟩] ++
        entries (seedForest enclose cs (advance enclose c s)).1 at hp
      rcases List.mem_append.mp hp with hp | hp
      · have hp' : p = issue enclose c s := by simpa [issue] using hp
        subst p
        exact (issue_serial_le enclose c s).trans hnext
      · exact hbound p hp

structure State (enclose : SeedCell → Bounds) where
  forest : SourceForest enclose initialSeeds
  serial : ℕ
  splits : ℕ
  totalLower : ℤ
  totalUpper : ℤ

def initialState (enclose : SeedCell → Bounds) : State enclose :=
  let init := seedForest enclose initialSeeds 0
  ⟨init.1,init.2,0,lowerSum (entries init.1),upperSum (entries init.1)⟩

def Invariant {enclose : SeedCell → Bounds} (st : State enclose) : Prop :=
  st.totalLower = lowerSum (entries st.forest) ∧
  st.totalUpper = upperSum (entries st.forest) ∧
  ∀ p ∈ entries st.forest, p.serial ≤ st.serial

theorem initialState_invariant (enclose : SeedCell → Bounds) :
    Invariant (initialState enclose) := by
  exact ⟨rfl,rfl,(seedForest_serial enclose initialSeeds 0).2⟩

/-- Surviving older entries win an uncertainty tie against either newly
inserted child. This uses the proved serial bound plus literal allocation. -/
theorem old_entry_precedes_child {enclose : SeedCell → Bounds} (st : State enclose)
    (hi : Invariant st) (old fresh : Entry) (c : SeedCell)
    (hold : old ∈ entries st.forest)
    (hfresh : fresh ∈ children enclose st.serial c) (ha : active fresh)
    (herr : error old = error fresh) :
    Before old fresh ∧ ¬ Before fresh old := by
  have ho := hi.2.2 old hold
  have hn := active_children_fresh enclose st.serial c fresh hfresh ha
  rw [before_equal_error_iff old fresh herr,
    before_equal_error_iff fresh old herr.symm]
  omega

/-- The original loop's split eligibility, including its >= target test.
This does not assert a target crossing or the historical final counter. -/
def running {enclose : SeedCell → Bounds} (st : State enclose)
    (fixedUpper target : ℚ) (maxSplits : ℕ) : Prop :=
  st.splits < maxSplits ∧ target ≤ fixedUpper + (st.totalUpper : ℚ) / 2^80

inductive Step (enclose : SeedCell → Bounds) (fixedUpper target : ℚ)
    (maxSplits : ℕ) : State enclose → State enclose → Prop where
  | split (st : State enclose) (p : Entry) (rest : List Entry)
      (forest' : SourceForest enclose initialSeeds)
      (gate : running st fixedUpper target maxSplits)
      (pop : popBest (heapContents (entries st.forest)) = some (p,rest))
      (refines : ForestRefines enclose st.serial p st.forest forest') :
      Step enclose fixedUpper target maxSplits st
        ⟨forest',afterChildren enclose st.serial p.cell,st.splits + 1,
          st.totalLower - p.bounds.lower + lowerSum (children enclose st.serial p.cell),
          st.totalUpper - p.bounds.upper + upperSum (children enclose st.serial p.cell)⟩

/-- The literal source assert is the only additional geometric condition
needed to construct the selected next forest. No tree-update witness or
aggregate-update identity is required from an external certificate. -/
theorem step_exists {enclose : SeedCell → Bounds} (st : State enclose)
    (fixedUpper target : ℚ) (maxSplits : ℕ) (p : Entry) (rest : List Entry)
    (gate : running st fixedUpper target maxSplits)
    (pop : popBest (heapContents (entries st.forest)) = some (p,rest))
    (width : p.cell.1 (originalAxis p.cell) + 2 ≤ p.cell.2 (originalAxis p.cell)) :
    ∃ st', Step enclose fixedUpper target maxSplits st st' := by
  have hp : p ∈ entries st.forest :=
    (List.mem_filter.mp (popBest_spec _ _ _ pop).2.1).1
  obtain ⟨forest',refines⟩ := forest_refinement_exists st.forest st.serial p hp width
  exact ⟨_,Step.split st p rest forest' gate pop refines⟩

/-- The central source-driver invariant. Its proof uses the structural leaf
replacement, not an assumed aggregate identity or a per-run certificate. -/
theorem step_preserves_invariant {enclose : SeedCell → Bounds}
    {fixedUpper target : ℚ} {maxSplits : ℕ} {st st' : State enclose}
    (h : Step enclose fixedUpper target maxSplits st st') (hi : Invariant st) :
    Invariant st' := by
  cases h with
  | split st p rest forest' gate pop refines =>
      obtain ⟨hl,hu,hcount⟩ := refine_sum_updates refines
      refine ⟨by simpa only [hi.1] using hl.symm,
        by simpa only [hi.2.1] using hu.symm,?_⟩
      obtain ⟨pre,post,hpre,hpost⟩ := forest_refines_entries refines
      intro q hq
      rw [hpost] at hq
      rcases List.mem_append.mp hq with hq | hq
      · have hqold : q ∈ entries st.forest := by
          rw [hpre]
          exact List.mem_append.mpr (Or.inl hq)
        exact (hi.2.2 q hqold).trans (afterChildren_mono enclose _ _)
      · rcases List.mem_append.mp hq with hq | hq
        · exact children_serial_le enclose _ _ q hq
        · have hqold : q ∈ entries st.forest := by
            rw [hpre]
            exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hq)))
          exact (hi.2.2 q hqold).trans (afterChildren_mono enclose _ _)

inductive Run (enclose : SeedCell → Bounds) (fixedUpper target : ℚ)
    (maxSplits : ℕ) : State enclose → Prop where
  | initial : Run enclose fixedUpper target maxSplits (initialState enclose)
  | next {st st' : State enclose} (prior : Run enclose fixedUpper target maxSplits st)
      (step : Step enclose fixedUpper target maxSplits st st') :
      Run enclose fixedUpper target maxSplits st'

theorem run_invariant {enclose : SeedCell → Bounds} {fixedUpper target : ℚ}
    {maxSplits : ℕ} {st : State enclose}
    (h : Run enclose fixedUpper target maxSplits st) : Invariant st := by
  induction h with
  | initial => exact initialState_invariant enclose
  | next prior step ih => exact step_preserves_invariant step ih

/-- Unlike heap occupancy, this is the complete terminal inventory. -/
theorem run_complete_leaf_count {enclose : SeedCell → Bounds} {fixedUpper target : ℚ}
    {maxSplits : ℕ} {st : State enclose}
    (h : Run enclose fixedUpper target maxSplits st) :
    (entries st.forest).length = 21 + st.splits := by
  induction h with
  | initial =>
      simpa only [initialState,seedForest_entries_length,initialSeeds_eq_records,
        records_length,Nat.add_zero]
  | next prior step ih =>
      cases step with
      | split st p rest forest' gate pop refines =>
          have hc := (refine_sum_updates refines).2.2
          change (entries forest').length = 21 + (st.splits + 1)
          omega

/-- The exact positional upper charges are obtained from all terminal
evaluations. This includes the non-heap leaves and keeps the original order. -/
theorem run_complete_charges {enclose : SeedCell → Bounds} {fixedUpper target : ℚ}
    {maxSplits : ℕ} {st : State enclose}
    (h : Run enclose fixedUpper target maxSplits st) :
    ((entries st.forest).map (fun p => p.bounds.upper)).sum = st.totalUpper ∧
    ((entries st.forest).map (fun p => p.bounds.upper)).length =
      splitCount (completeTree st.forest) + 1 := by
  refine ⟨(run_invariant h).2.1.symm,?_⟩
  have hlen := closedLeaves_length (completeTree st.forest) compactRegion
  rw [completeTree_closedLeaves,List.length_map] at hlen
  simpa only [List.length_map] using hlen

/-- Shape-preserving charge attachment for the actual source-driven state,
using the complete terminal ledger rather than the positive-error heap. -/
def chargeTree {enclose : SeedCell → Bounds} {fixedUpper target : ℚ}
    {maxSplits : ℕ} {st : State enclose}
    (h : Run enclose fixedUpper target maxSplits st) : ChargedCutTree :=
  (attachCharges (completeTree st.forest)
    ((entries st.forest).map (fun p => p.bounds.upper)) (run_complete_charges h).2).val

theorem chargeTree_erase {enclose : SeedCell → Bounds} {fixedUpper target : ℚ}
    {maxSplits : ℕ} {st : State enclose}
    (h : Run enclose fixedUpper target maxSplits st) :
    eraseCharges (chargeTree h) = completeTree st.forest :=
  attachCharges_erase _ _ _

theorem chargeTree_total {enclose : SeedCell → Bounds} {fixedUpper target : ℚ}
    {maxSplits : ℕ} {st : State enclose}
    (h : Run enclose fixedUpper target maxSplits st) :
    totalCharge (chargeTree h) = st.totalUpper := by
  rw [totalCharge_eq_leafCharges_sum]
  unfold chargeTree
  rw [attachCharges_list]
  exact (run_complete_charges h).1

/-- Analytic payment is precisely the remaining per-leaf input. The source,
tree, ordering, length and total-charge identities have already been proved. -/
theorem chargeTree_local_iff {enclose : SeedCell → Bounds} {fixedUpper target : ℚ}
    {maxSplits : ℕ} {st : State enclose}
    (h : Run enclose fixedUpper target maxSplits st) :
    LocalChargeBound (chargeTree h) compactRegion ↔
      List.Forall₂ (fun domain q =>
        (∫ t in domain, compactKernel t) ≤ (q : ℝ) / 2^80)
        ((entries st.forest).map (fun p => rootCell p.cell))
        ((entries st.forest).map (fun p => p.bounds.upper)) := by
  unfold chargeTree
  rw [attachCharges_local_iff,completeTree_closedLeaves]

/-- Exact uncertainty bookkeeping for every original-driver state. This
does not assert that the actual Q80 enclosures are analytically sound.
Primitive lower<=upper consistency alone suffices for the heap identity. -/
theorem run_error_ledger {enclose : SeedCell → Bounds} {fixedUpper target : ℚ}
    {maxSplits : ℕ} {st : State enclose}
    (h : Run enclose fixedUpper target maxSplits st)
    (consistent : ∀ c, (enclose c).lower ≤ (enclose c).upper) :
    st.totalUpper - st.totalLower = errorSum (heapContents (entries st.forest)) := by
  rw [errorSum_heapContents _ (by
    intro p hp
    rw [entry_enclose st.forest p hp]
    exact consistent p.cell),errorSum_eq_difference]
  exact congrArg₂ (fun a b : ℤ => a - b) (run_invariant h).2.1 (run_invariant h).1

end
end ImbalancedChen.P2OriginalPriorityForestLedgerSourceOnly
