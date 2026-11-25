import ImbalancedChen.Part5OriginalH430RequestedReverseSupport

/-!
P5.6 / h34: exact generation-to-generation SELECTED FRONTIER LIST equality.

SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.

Unlike the previous forward/reverse membership lemmas, this module reasons
about the ORIGINAL depth-first history list itself.  The equality is an
equality of lists, not merely of sets of products.  The original order and
every repeated occurrence are preserved.  No count-source or analytic
claim is contained in this list statement.

The single-step frontier uses ONLY the actual selected children with their
original edge tags, mode, prime carrier and edge coefficients.
-/

namespace ImbalancedChen.Part5OriginalH430RequestedFrontierMultiplicity

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedFrontierTransport
open Part5OriginalH430RequestedReverseSupport

/-- Filter the original occurrence list by the literal remaining
generation, retaining its order and all equal-valued occurrences. -/
def at {N : ℕ} (g : ℕ) (xs : List (Occurrence N)) : List (Occurrence N) :=
  xs.filter (fun o => decide (o.remaining = g))

/-- Expand each *list position* through its actual winning children.
No quotient by old word, owner, product or geometric label. -/
def selectedFrontier (N : ℕ) (Q : ℝ) (g : ℕ)
    (xs : List (Occurrence N)) : List (Occurrence N) :=
  xs.flatMap (fun o => (children N Q g o.current).map (extend o))

private theorem at_cons {N : ℕ} (g : ℕ) (o : Occurrence N)
    (xs : List (Occurrence N)) :
    at g (o :: xs) =
      if o.remaining = g then o :: at g xs else at g xs := by
  by_cases h : o.remaining = g <;> simp [at, h]

private theorem at_append {N : ℕ} (g : ℕ)
    (xs ys : List (Occurrence N)) :
    at g (xs ++ ys) = at g xs ++ at g ys := by
  simp [at, List.filter_append]

/-- Filtering commutes with the original prefix injection because
prepend leaves the remaining generation unchanged. -/
private theorem at_map_prepend {N : ℕ} (g : ℕ) (e : Edge N)
    (xs : List (Occurrence N)) :
    at g (xs.map (prepend e)) = (at g xs).map (prepend e) := by
  induction xs with
  | nil => rfl
  | cons o os ih =>
      by_cases h : o.remaining = g
      · simpa [at_cons, prepend, h] using
          congrArg (List.cons (prepend e o)) ih
      · simpa [at_cons, prepend, h] using ih

private theorem at_flatMap {N : ℕ} {α : Type*} (g : ℕ)
    (xs : List α) (f : α → List (Occurrence N)) :
    at g (xs.flatMap f) = xs.flatMap (fun x => at g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, at_append, ih]

private theorem at_nil_of_mem_ne {N : ℕ} (g : ℕ)
    (xs : List (Occurrence N)) :
    (∀ o ∈ xs, o.remaining ≠ g) → at g xs = [] := by
  induction xs with
  | nil => intro _; rfl
  | cons o os ih =>
      intro h
      have ho : o.remaining ≠ g := h o (by simp)
      have hs : ∀ t ∈ os, t.remaining ≠ g := by
        intro t ht
        exact h t (by simp [ht])
      simpa only [at_cons, ho, if_false] using ih hs

private theorem list_flatMap_ext {α β : Type*} (xs : List α)
    (f h : α → List β) :
    (∀ x ∈ xs, f x = h x) → xs.flatMap f = xs.flatMap h := by
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro heq
      have hx : f x = h x := heq x (by simp)
      have hxs : ∀ y ∈ xs, f y = h y := by
        intro y hy
        exact heq y (by simp [hy])
      simp only [List.flatMap_cons, hx, ih hxs]

/-- An occurrence produced with k steps remaining cannot be above k.
This is the original path-length identity, not an added well-formedness
field on an arbitrary tree. -/
theorem history_at_above {N : ℕ} (Q : ℝ) (k : ℕ)
    (r : Request) (g : ℕ) (hkg : k < g) :
    at g (history N Q k r) = [] := by
  apply at_nil_of_mem_ne
  intro o ho
  have hh := (history_facts ho).2.1
  omega

/-- The top generation has exactly the literal root once, including
its starting read mode and empty edge path. -/
theorem history_at_top {N : ℕ} (Q : ℝ) (k : ℕ) (r : Request) :
    at k (history N Q k r) = [origin k r] := by
  cases k with
  | zero => rfl
  | succ k =>
      have htail :
          at (k + 1)
            ((children N Q k r).flatMap
              (fun e => (history N Q k (nextRequest r e)).map (prepend e))) = [] := by
        rw [at_flatMap]
        have hunit (e : Edge N) :
            at (k + 1) ((history N Q k (nextRequest r e)).map (prepend e)) = [] := by
          rw [at_map_prepend]
          rw [history_at_above Q k (nextRequest r e) (k + 1) (by omega)]
          rfl
        induction (children N Q k r) with
        | nil => rfl
        | cons e es ih =>
            simp only [List.flatMap_cons, hunit, List.nil_append, ih]
      change at (k + 1)
        (origin (k + 1) r ::
          (children N Q k r).flatMap
            (fun e => (history N Q k (nextRequest r e)).map (prepend e))) = _
      rw [at_cons]
      have heq : (origin (N := N) (k + 1) r).remaining = k + 1 := rfl
      simp only [heq, if_true, htail]

/-- At a generation strictly below the top, the top root is absent.
The rest is the unchanged depth-first concatenation of its branches. -/
theorem history_at_below {N : ℕ} (Q : ℝ) (k g : ℕ)
    (r : Request) (hg : g < k + 1) :
    at g (history N Q (k + 1) r) =
      (children N Q k r).flatMap (fun e =>
        (at g (history N Q k (nextRequest r e))).map (prepend e)) := by
  have hne : (origin (N := N) (k + 1) r).remaining ≠ g := by
    change k + 1 ≠ g
    omega
  change at g
    (origin (k + 1) r ::
      (children N Q k r).flatMap
        (fun e => (history N Q k (nextRequest r e)).map (prepend e))) = _
  rw [at_cons, if_neg hne, at_flatMap]
  apply list_flatMap_ext
  intro e _
  exact at_map_prepend g e (history N Q k (nextRequest r e))

private theorem selectedFrontier_append (N : ℕ) (Q : ℝ) (g : ℕ)
    (xs ys : List (Occurrence N)) :
    selectedFrontier N Q g (xs ++ ys) =
      selectedFrontier N Q g xs ++ selectedFrontier N Q g ys := by
  simp [selectedFrontier, List.flatMap_append]

private theorem selectedFrontier_flatMap {α : Type*}
    (N : ℕ) (Q : ℝ) (g : ℕ)
    (xs : List α) (f : α → List (Occurrence N)) :
    selectedFrontier N Q g (xs.flatMap f) =
      xs.flatMap (fun x => selectedFrontier N Q g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, selectedFrontier_append, ih]

/-- The actual last-edge extension commutes with the older first edge:
its tagged word is e :: prefix ++ [last], never a product quotient. -/
theorem selectedFrontier_map_prepend {N : ℕ} (Q : ℝ) (g : ℕ)
    (e : Edge N) (xs : List (Occurrence N)) :
    selectedFrontier N Q g (xs.map (prepend e)) =
      (selectedFrontier N Q g xs).map (prepend e) := by
  induction xs with
  | nil => rfl
  | cons o os ih =>
      change
        (children N Q g o.current).map (extend (prepend e o)) ++
          selectedFrontier N Q g (os.map (prepend e)) =
        ((children N Q g o.current).map (extend o) ++
          selectedFrontier N Q g os).map (prepend e)
      rw [ih, List.map_append]
      simp only [List.map_map, extend_prepend]

/-- At the first step, the exact list is the winner's child list
extended from the literal root, not a set of its possible labels. -/
theorem history_first_frontier (N : ℕ) (Q : ℝ)
    (k : ℕ) (r : Request) :
    at k (history N Q (k + 1) r) =
      selectedFrontier N Q k [origin (k + 1) r] := by
  rw [history_at_below Q k k r (by omega)]
  simp only [selectedFrontier, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  induction (children N Q k r) with
  | nil => rfl
  | cons e es ih =>
      simp only [List.flatMap_cons, List.map_cons]
      rw [history_at_top Q k (nextRequest r e)]
      simpa only [List.map_singleton, List.singleton_append, extend_origin]
        using congrArg (List.cons (prepend e (origin k (nextRequest r e)))) ih

/-- Exact LIST equality at arbitrary remaining generation.
No set/extensional membership, list deduplication, external counting
assumption, or arbitrary parent selector occurs in the statement. -/
theorem history_frontier_list (N : ℕ) (Q : ℝ) (g : ℕ) :
    ∀ (k : ℕ) (r : Request), g < k →
      at g (history N Q k r) =
        selectedFrontier N Q g (at (g + 1) (history N Q k r)) := by
  intro k
  induction k with
  | zero =>
      intro r h
      omega
  | succ k ih =>
      intro r hg
      by_cases heq : g = k
      · subst g
        exact history_first_frontier N Q k r
      · have hlt : g < k := by omega
        calc
          at g (history N Q (k + 1) r) =
              (children N Q k r).flatMap (fun e =>
                (at g (history N Q k (nextRequest r e))).map (prepend e)) :=
                  history_at_below Q k g r hg
          _ = (children N Q k r).flatMap (fun e =>
                (selectedFrontier N Q g
                  (at (g + 1) (history N Q k (nextRequest r e)))).map (prepend e)) := by
                  apply list_flatMap_ext
                  intro e _
                  rw [ih (nextRequest r e) hlt]
          _ = (children N Q k r).flatMap (fun e =>
                selectedFrontier N Q g
                  ((at (g + 1) (history N Q k (nextRequest r e))).map (prepend e))) := by
                  apply list_flatMap_ext
                  intro e _
                  rw [selectedFrontier_map_prepend]
          _ = selectedFrontier N Q g
                ((children N Q k r).flatMap (fun e =>
                  (at (g + 1) (history N Q k (nextRequest r e))).map (prepend e))) := by
                  rw [selectedFrontier_flatMap]
          _ = selectedFrontier N Q g
                (at (g + 1) (history N Q (k + 1) r)) := by
                  rw [history_at_below Q k (g + 1) r (by omega)]

/-- Apply the exact list theorem to the literal frozen U3/U4 root.
It preserves every real list position (including repeated occurrences). -/
theorem level_frontier_list (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) :
    levelRequests N n root tau p g.val =
      selectedFrontier N (rootQ N n root tau p) g.val
        (levelRequests N n root tau p (g.val + 1)) := by
  change at g.val
      (history N (rootQ N n root tau p) 430 (rootRequest N n root tau p)) =
    selectedFrontier N (rootQ N n root tau p) g.val
      (at (g.val + 1)
        (history N (rootQ N n root tau p) 430 (rootRequest N n root tau p)))
  exact history_frontier_list N (rootQ N n root tau p)
    g.val 430 (rootRequest N n root tau p) g.isLt

/-- The same equality applied to EACH concrete Occurrence count: no
multiplicity can be silently lost by a support-only reindexing. -/
theorem level_occurrence_count (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (o : Occurrence N) :
    (levelRequests N n root tau p g.val).count o =
      (selectedFrontier N (rootQ N n root tau p) g.val
        (levelRequests N n root tau p (g.val + 1))).count o := by
  rw [level_frontier_list]

/-- Every REAL-valued per-occurrence table or weight can therefore be
summed over the chosen edges with exactly the original repetitions.
This is purely a finite list identity, NOT an arithmetic count bridge. -/
theorem level_sum_exact (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (f : Occurrence N → ℝ) :
    ((levelRequests N n root tau p g.val).map f).sum =
      ((selectedFrontier N (rootQ N n root tau p) g.val
        (levelRequests N n root tau p (g.val + 1))).map f).sum := by
  rw [level_frontier_list]

end
end ImbalancedChen.Part5OriginalH430RequestedFrontierMultiplicity
