import ImbalancedChen.Part5OriginalH430RequestedFrontierTransport

/-!
P5.6 / h34: REVERSE SUPPORT for the actual selected child frontier.

SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.
This proves that every generation-g occurrence in the ORIGINAL recursive
rootHistory, for g < 430, comes from a selected edge of a generation-(g+1)
parent in the SAME history.  It uses the actual tagged path and its
literal predecessor.  Together with the prior forward inclusion it gives
support equivalence for the genuine levelRequests lists.

IMPORTANT: List membership is not list-position multiplicity.  The exact
indexed/multiset frontier equality, the original arithmetic U3/U4 count
source and its root weights, floors and analytic inputs remain OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430RequestedReverseSupport

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedFrontierTransport

/-- The only member of a generated history at its ROOT generation is
the root itself.  This follows from the original path-length identity,
not a uniqueness assumption on integer products or physical labels. -/
theorem history_top_is_origin {N k : ℕ} {Q : ℝ} {r : Request}
    {o : Occurrence N}
    (ho : o ∈ history N Q k r)
    (hk : o.remaining = k) :
    o = origin k r := by
  obtain ⟨_, hlen, hcur⟩ := history_facts ho
  cases o with
  | mk path current remaining =>
      change remaining = k at hk
      change remaining + path.length = k at hlen
      change current = replay r path at hcur
      have hz : path.length = 0 := by omega
      cases path with
      | nil =>
          simp only [replay] at hcur
          subst current
          subst remaining
          rfl
      | cons e es =>
          simp only [List.length_cons] at hz
          omega

/-- An occurrence below the root has a genuine selected last edge and
a parent at precisely the next generation.  The witness is recovered
by induction through the ORIGINAL depth-first recursive history. -/
theorem history_reverse_child {N k g : ℕ} {Q : ℝ} {r : Request}
    {o : Occurrence N}
    (ho : o ∈ history N Q k r)
    (hg : o.remaining = g)
    (hkg : g < k) :
    ∃ u : Occurrence N, ∃ e : Edge N,
      u ∈ history N Q k r ∧
      u.remaining = g + 1 ∧
      e ∈ children N Q g u.current ∧
      extend u e = o := by
  induction k generalizing r o with
  | zero =>
      omega
  | succ k ih =>
      rcases (show o = origin (k + 1) r ∨
          o ∈ (children N Q k r).flatMap
            (fun f => (history N Q k (nextRequest r f)).map (prepend f)) by
          simpa only [history, List.mem_cons] using ho) with hroot | htail
      · subst o
        change k + 1 = g at hg
        omega
      · obtain ⟨f, hf, hmap⟩ := List.mem_flatMap.mp htail
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmap
        have htg : t.remaining = g := by
          simpa only [prepend] using hg
        by_cases htop : g = k
        · subst g
          have hrootChild : t = origin k (nextRequest r f) :=
            history_top_is_origin ht htg
          subst t
          refine ⟨origin (k + 1) r, f, ?_, ?_, ?_, ?_⟩
          · simp only [history, List.mem_cons, true_or]
          · rfl
          · simpa only [origin] using hf
          · exact extend_origin k r f
        · have hlt : g < k := by omega
          obtain ⟨u, e, hu, hug, hue, heq⟩ := ih ht htg hlt
          refine ⟨prepend f u, e, ?_, ?_, ?_, ?_⟩
          · change prepend f u = origin (k + 1) r ∨
              prepend f u ∈ (children N Q k r).flatMap
                (fun q => (history N Q k (nextRequest r q)).map (prepend q))
            exact Or.inr
              (List.mem_flatMap.mpr
                ⟨f, hf, List.mem_map.mpr ⟨u, hu, rfl⟩⟩)
          · simpa only [prepend] using hug
          · simpa only [prepend] using hue
          · simpa only [extend_prepend, heq]

/-- Reverse support against the concrete U3/U4 frozen-root history.
The parent belongs to the actual generation g+1 level and its last
edge comes from the genuine winner selected by iterate g. -/
theorem nextLevel_reverse_support (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (o : Occurrence N)
    (ho : o ∈ levelRequests N n root tau p g.val) :
    ∃ u : Occurrence N,
      u ∈ levelRequests N n root tau p (g.val + 1) ∧
      ∃ e : Edge N,
        e ∈ children N (rootQ N n root tau p) g.val u.current ∧
        extend u e = o := by
  have hsource : o ∈ rootHistory N n root tau p ∧
      o.remaining = g.val := by
    simpa only [levelRequests, List.mem_filter, decide_eq_true_eq] using ho
  obtain ⟨u, e, hu, hug, he, heq⟩ :=
    history_reverse_child (N := N) (k := 430) (g := g.val)
      (Q := rootQ N n root tau p)
      (r := rootRequest N n root tau p) hsource.1 hsource.2 g.isLt
  refine ⟨u, ?_, e, he, heq⟩
  simpa only [levelRequests, List.mem_filter, decide_eq_true_eq]
    using (And.intro hu hug)

/-- Exact SET-SUPPORT characterization of the next-generation list:
both directions use the real original history and literal children.
No multiset quotient or claim of equal list-position multiplicities. -/
theorem nextLevel_support_iff (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (o : Occurrence N) :
    o ∈ levelRequests N n root tau p g.val ↔
      ∃ u : Occurrence N,
        u ∈ levelRequests N n root tau p (g.val + 1) ∧
        ∃ e : Edge N,
          e ∈ children N (rootQ N n root tau p) g.val u.current ∧
          extend u e = o := by
  constructor
  · exact nextLevel_reverse_support N n root tau p g o
  · rintro ⟨u, hu, e, he, rfl⟩
    have hsource : u ∈ rootHistory N n root tau p ∧
        u.remaining = g.val + 1 := by
      simpa only [levelRequests, List.mem_filter, decide_eq_true_eq] using hu
    have hm : extend u e ∈ rootHistory N n root tau p :=
      history_extend_mem hsource.1 hsource.2 he
    have hg : (extend u e).remaining = g.val := by
      simp only [extend_remaining, hsource.2]
      omega
    simpa only [levelRequests, List.mem_filter, decide_eq_true_eq]
      using (And.intro hm hg)

/-- Apply reverse support at an ACTUAL successor LIST POSITION, without
choosing an arbitrary geometric catalog label or deduplicating it. -/
theorem indexed_nextLevel_reverse_support {N n : ℕ}
    {root : Root} {tau : ℝ} {p : ℕ} (g : Fin 430)
    (j : LevelIndex N n root tau p g.val) :
    ∃ u : Occurrence N,
      u ∈ levelRequests N n root tau p (g.val + 1) ∧
      ∃ e : Edge N,
        e ∈ children N (rootQ N n root tau p) g.val u.current ∧
        extend u e = levelOccurrence j := by
  exact nextLevel_reverse_support N n root tau p g (levelOccurrence j)
    (List.get_mem _ _)

end
end ImbalancedChen.Part5OriginalH430RequestedReverseSupport
