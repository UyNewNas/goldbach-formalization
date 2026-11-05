import ImbalancedChen.Part5OriginalH430RequestedSignedStep

/-!
P5.6 / h34: concrete one-generation CHILD-FRONTIER transport.

SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.
An occurrence at generation g+1 expands via the one real winning action.
The resulting path is the OLD path with that edge appended.  Its mark
is exactly the old positive edge-product times the literal edgeWeight.
Every such child belongs to the ORIGINAL generated rootHistory, and
the actual generationValue is the sum of these child table masses.

This is a finite source-transport identity, NOT the missing statement
that these table requests equal the manuscript's arithmetic U3/U4
prime/PP counts, and NOT a new count-licence assumption.
-/

namespace ImbalancedChen.Part5OriginalH430RequestedFrontierTransport

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedAllChoice

/-- Keep the complete parent path; append the literal chosen edge
without quotienting repeated integer products or owner labels. -/
def extend {N : ℕ} (o : Occurrence N) (e : Edge N) : Occurrence N :=
  ⟨o.path ++ [e], nextRequest o.current e, o.remaining - 1⟩

@[simp] theorem extend_current {N : ℕ} (o : Occurrence N) (e : Edge N) :
    (extend o e).current = nextRequest o.current e := rfl

@[simp] theorem extend_remaining {N : ℕ} (o : Occurrence N) (e : Edge N) :
    (extend o e).remaining = o.remaining - 1 := rfl

theorem mark_extend {N : ℕ} (o : Occurrence N) (e : Edge N) :
    mark (extend o e) = mark o * edgeWeight e := by
  simp [mark, extend, List.map_append, List.prod_append]

theorem extend_prepend {N : ℕ} (e f : Edge N) (o : Occurrence N) :
    extend (prepend e o) f = prepend e (extend o f) := by
  cases o
  rfl

theorem extend_origin {N : ℕ} (g : ℕ) (r : Request) (e : Edge N) :
    extend (origin (g + 1) r) e =
      prepend e (origin g (nextRequest r e)) := by
  simp [extend, origin, prepend]

/-- One-step closure of the ACTUAL recursive history.  This is stronger
than simply admitting a geometric Program: the parent and chosen edge
are already members of the selected production list. -/
theorem history_extend_mem {N k g : ℕ} {Q : ℝ} {r : Request}
    {o : Occurrence N} {e : Edge N}
    (ho : o ∈ history N Q k r)
    (hg : o.remaining = g + 1)
    (he : e ∈ children N Q g o.current) :
    extend o e ∈ history N Q k r := by
  induction k generalizing r o with
  | zero =>
      have hroot : o = origin 0 r := by
        simpa only [history, List.mem_singleton] using ho
      subst o
      simp only [origin] at hg
      omega
  | succ k ih =>
      rcases (show o = origin (k + 1) r ∨
          o ∈ (children N Q k r).flatMap
            (fun f => (history N Q k (nextRequest r f)).map (prepend f)) by
          simpa only [history, List.mem_cons] using ho) with hroot | htail
      · subst o
        have hkg : g = k := by
          change k + 1 = g + 1 at hg
          omega
        subst g
        have hchild : extend (origin (k + 1) r) e ∈
            (children N Q k r).flatMap
              (fun f => (history N Q k (nextRequest r f)).map (prepend f)) := by
          apply List.mem_flatMap.mpr
          refine ⟨e, he, ?_⟩
          apply List.mem_map.mpr
          refine ⟨origin k (nextRequest r e), ?_, ?_⟩
          · simp only [history, List.mem_cons, true_or]
          · exact (extend_origin k r e).symm
        simpa only [history, List.mem_cons] using Or.inr hchild
      · obtain ⟨f, hf, hmap⟩ := List.mem_flatMap.mp htail
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmap
        have hlevel : t.remaining = g + 1 := by simpa only [prepend] using hg
        have hedge : e ∈ children N Q g t.current := by
          simpa only [prepend] using he
        have hchild : extend t e ∈ history N Q k (nextRequest r f) :=
          ih ht hlevel hedge
        have htail' : prepend f (extend t e) ∈
            (children N Q k r).flatMap
              (fun q => (history N Q k (nextRequest r q)).map (prepend q)) := by
          apply List.mem_flatMap.mpr
          exact ⟨f, hf, List.mem_map.mpr ⟨extend t e, hchild, rfl⟩⟩
        rw [extend_prepend]
        simpa only [history, List.mem_cons] using Or.inr htail'

/-- Every actually selected immediate child of an indexed g+1
parent is present in the full generated root history at generation g.
The original parent LIST POSITION is preserved in the statement. -/
theorem actual_level_extend_mem {N n : ℕ} {root : Root} {tau : ℝ}
    {p : ℕ} {g : Fin 430} (l : Index N n root tau p g)
    {e : Edge N}
    (he : e ∈ children N (rootQ N n root tau p) g.val
       (levelOccurrence l).current) :
    extend (levelOccurrence l) e ∈ rootHistory N n root tau p ∧
    (extend (levelOccurrence l) e).remaining = g.val ∧
    mark (extend (levelOccurrence l) e) =
      levelMark l * edgeWeight e := by
  have hsource := levelOccurrence_source l
  refine ⟨history_extend_mem hsource.1 hsource.2 he, ?_, ?_⟩
  · simp only [extend_remaining, hsource.2]
    omega
  · exact mark_extend _ _

/-- The descendants preserve the precise ORIGINAL root's Q and integer
word; there is no reassignment of Q at a child or a scalar-owner swap. -/
theorem actual_child_sameQ_word {N n : ℕ} {root : Root} {tau : ℝ}
    {p : ℕ} {g : Fin 430} (l : Index N n root tau p g)
    {e : Edge N}
    (he : e ∈ children N (rootQ N n root tau p) g.val
       (levelOccurrence l).current) :
    (N : ℝ)^((extend (levelOccurrence l) e).current.node.physical.total) =
      rootQ N n root tau p ∧
    P2EnhancedLowerPhysicalNode.word
        (extend (levelOccurrence l) e).current.node.physical =
      (extend (levelOccurrence l) e).current.old.map
        (P2OriginalChildPhysicalNormalization.physicalPrime N) := by
  have h := (actual_level_extend_mem l he).1
  exact ⟨rootHistory_sameQ h, rootHistory_integer_word h⟩


/-- Every generated selected child is present in the ACTUAL next
generation list, not just in a separate geometric catalogue. This is
the forward (no phantom successor) direction; the reverse multiset
bijection and the arithmetic U3/U4 source identity are still OPEN. -/
theorem actual_child_mem_next_level {N n : ℕ} {root : Root} {tau : ℝ}
    {p : ℕ} {g : Fin 430} (l : Index N n root tau p g)
    {e : Edge N}
    (he : e ∈ children N (rootQ N n root tau p) g.val
      (levelOccurrence l).current) :
    extend (levelOccurrence l) e ∈
      levelRequests N n root tau p g.val := by
  have h := actual_level_extend_mem l he
  simpa only [levelRequests, List.mem_filter, decide_eq_true_eq]
    using (And.intro h.1 h.2.1)

/-- The actual downstream table term at each extended occurrence.
No assertion is made that requestValue is an arithmetic prime count. -/
def childTableMass (N : ℕ) (Q : ℝ) (t : Table)
    (o : Occurrence N) (es : List (Edge N)) : ℝ :=
  (es.map (fun e =>
    mark (extend o e) *
      thetaAtom N Q (parentProduct (extend o e).current.old) *
      requestValue t (extend o e).current)).sum

/-- Exact path-weight multiplication and finite-list transport, using
the existing edgeValue and actual nextRequest, no source-count axiom. -/
theorem childTableMass_eq_mark_edgeValue (N : ℕ) (Q : ℝ)
    (t : Table) (o : Occurrence N) (es : List (Edge N)) :
    childTableMass N Q t o es =
      mark o * edgeValue Q t o.current es := by
  induction es with
  | nil => simp [childTableMass, edgeValue]
  | cons e es ih =>
      change
        mark (extend o e) *
          thetaAtom N Q (parentProduct (extend o e).current.old) *
          requestValue t (extend o e).current +
          childTableMass N Q t o es =
        mark o * (
          edgeWeight e * thetaAtom N Q
            (parentProduct (nextRequest o.current e).old) *
            requestValue t (nextRequest o.current e) +
          edgeValue Q t o.current es)
      rw [ih, mark_extend]
      simp only [extend_current]
      ring

/-- Direct children of the ACTUAL g+1 level, indexed by the parent's
original list position. This is the one-step feedback frontier, not
a replacement for the manuscript's prime/PP selected-count family. -/
def nextLevelMass (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l : Index N n root tau p g,
    childTableMass N (rootQ N n root tau p) (iterate g.val)
      (levelOccurrence l)
      (children N (rootQ N n root tau p) g.val (levelOccurrence l).current)

/-- Exact generation-to-child-frontier transport. It preserves all
retained, Buchstab, W1 and W2 multiplicities and positive path marks.
The arithmetic count interpretation of this mass remains to be proved. -/
theorem generationValue_eq_nextLevelMass
    (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) :
    generationValue N n root tau p g =
      nextLevelMass N n root tau p g := by
  unfold generationValue nextLevelMass
  apply Finset.sum_congr rfl
  intro l _
  simpa only [levelMark] using
    (childTableMass_eq_mark_edgeValue N (rootQ N n root tau p)
      (iterate g.val) (levelOccurrence l)
      (children N (rootQ N n root tau p) g.val
        (levelOccurrence l).current)).symm

end
end ImbalancedChen.Part5OriginalH430RequestedFrontierTransport
