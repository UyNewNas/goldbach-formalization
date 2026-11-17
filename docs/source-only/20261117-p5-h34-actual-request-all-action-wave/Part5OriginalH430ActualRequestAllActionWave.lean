import ImbalancedChen.Part5OriginalH430RequestedHistory

/-!
P5.6/h34: finite ALL-ACTION recursion for the ACTUAL selected request tree.

The request generator resolves one literal action at predecessor g. The
wave account below sums EVERY generated list occurrence, including its
positive original edge-product mark, with no quotient by a physical product
or a catalog label. It accounts for the zero-generation seed separately.

This is a structural identity for the true request program, NOT an
inequality for the original U3/U4 count source, a Buchstab analytic estimate,
a retained owner licence, or a 430+11 integral realization.
SOURCE ONLY / UNCOMPILED / full h34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualRequestAllActionWave

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory

/-- A literal full-wave total over ALL generated occurrences.
The test may depend on the remaining generation and the exact Request
(including scalar versus specified-cell mode), but never on an invented
catalogue ownership or a supplied generation map. -/
def waveAccount (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request)
    (V : ℕ → Request → ℝ) : ℝ :=
  ((history N Q g r).map (fun o => mark o * V o.remaining o.current)).sum

/-- The actual terminal generation is a single seed with mark one. -/
theorem wave_zero (N : ℕ) (Q : ℝ) (r : Request)
    (V : ℕ → Request → ℝ) :
    waveAccount N Q 0 r V = V 0 r := by
  simp [waveAccount, history, mark_origin]

private theorem sum_map_flatMap {α β : Type}
    (es : List α) (f : α → List β) (w : β → ℝ) :
    ((es.flatMap f).map w).sum =
      (es.map (fun e => ((f e).map w).sum)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [ih]

private theorem sum_map_scale {α : Type}
    (xs : List α) (c : ℝ) (w : α → ℝ) :
    (xs.map (fun x => c * w x)).sum = c * (xs.map w).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, mul_add]

/-- Exact count of every node in the finite chosen-action expansion.
The first term is the CURRENT node (including at seed generation); the
rest are precisely the selected children, with their literal coefficients.
No unselected bank, Buchstab or retention alternative is added. -/
theorem wave_successor (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request)
    (V : ℕ → Request → ℝ) :
    waveAccount N Q (g+1) r V =
      V (g+1) r +
        ((children N Q g r).map (fun e =>
          edgeWeight e * waveAccount N Q g (nextRequest r e) V)).sum := by
  let es := children N Q g r
  have hbranch (e : Edge N) :
      (((history N Q g (nextRequest r e)).map (prepend e)).map
        (fun o => mark o * V o.remaining o.current)).sum =
      edgeWeight e * waveAccount N Q g (nextRequest r e) V := by
    simp only [List.map_map]
    change ((history N Q g (nextRequest r e)).map
      (fun o => mark (prepend e o) * V o.remaining o.current)).sum = _
    simpa only [mark_prepend, mul_assoc, waveAccount] using
      (sum_map_scale (history N Q g (nextRequest r e))
        (edgeWeight e)
        (fun o => mark o * V o.remaining o.current))
  have hbranches (xs : List (Edge N)) :
      (xs.map (fun e =>
        (((history N Q g (nextRequest r e)).map (prepend e)).map
          (fun o => mark o * V o.remaining o.current)).sum)).sum =
      (xs.map (fun e =>
        edgeWeight e * waveAccount N Q g (nextRequest r e) V)).sum := by
    induction xs with
    | nil => rfl
    | cons e xs ih =>
        simp only [List.map_cons, List.sum_cons, hbranch e, ih]
  calc
    waveAccount N Q (g+1) r V =
      V (g+1) r +
        (((es.flatMap (fun e =>
          (history N Q g (nextRequest r e)).map (prepend e))).map
          (fun o => mark o * V o.remaining o.current)).sum) := by
            simp [waveAccount, history, es, mark_origin]
    _ = V (g+1) r +
        (es.map (fun e =>
          (((history N Q g (nextRequest r e)).map (prepend e)).map
            (fun o => mark o * V o.remaining o.current)).sum)).sum := by
            rw [sum_map_flatMap]
    _ = _ := by rw [hbranches es]

/-- Evaluate the ACTUAL chosen next-step row; this is not the
full-history functional, and not an asymptotic Buchstab comparison. -/
def actualStep (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request)
    (t : Table) : ℝ :=
  edgeValue Q t r (children N Q g r)

/-- No requested child means exactly zero next-step contribution;
the current/seed node is still present in waveAccount. -/
theorem step_exterior_zero (N : ℕ) (Q : ℝ) (g : ℕ)
    (r : Request) (t : Table)
    (h : resolve (g+1) r = none) :
    actualStep N Q g r t = 0 := by
  simp [actualStep, (exterior_children_empty h).1, edgeValue]

/-- A genuinely selected retention reads its SPECIFIED floor cell i,
not a scalar owner or a sum over 200 possible cells. -/
theorem step_retained (N : ℕ) (Q : ℝ) (g : ℕ)
    (r : Request) (t : Table) (i : Fin 200)
    (hs : Selected g r i .retained) :
    actualStep N Q g r t =
      thetaAtom N Q (parentProduct r.old) *
        floorValue (t r.node.upper) i := by
  have hc : children N Q g r = [.retained i] := by
    simp [children, hs.1, hs.2, branchEdges]
  rw [actualStep, hc]
  exact retained_edgeValue N Q t r i

/-- The selected Buchstab choice expands EXACTLY the original strict
prime-child carrier and evaluates the actual successor requests.
Every successor uses scalar mode; no numerical integral is inserted. -/
theorem step_buchstab (N : ℕ) (Q : ℝ) (g : ℕ)
    (r : Request) (t : Table) (i : Fin 200)
    (hs : Selected g r i .buchstab) :
    actualStep N Q g r t =
      ((singleChildren
        (.buchstab r.node.upper r.node.physical.argument)
        N Q r.old r.node.physical.ceiling).toList.map
          (fun p =>
            thetaAtom N Q
              (parentProduct (nextRequest r (.buchstab r.node.upper p)).old) *
            requestValue t (nextRequest r (.buchstab r.node.upper p)))).sum := by
  have hc : children N Q g r =
      (singleChildren (.buchstab r.node.upper r.node.physical.argument)
        N Q r.old r.node.physical.ceiling).toList.map
          (.buchstab r.node.upper) := by
    simp [children, hs.1, hs.2, branchEdges]
  rw [actualStep, hc]
  simp [edgeValue, List.map_map, edgeWeight]

/-- The bank case uses ONLY the resolved original 106-action slot.
It deliberately leaves the old fixed/single/pair coefficients intact. -/
theorem step_bank (N : ℕ) (Q : ℝ) (g : ℕ)
    (r : Request) (t : Table) (i : Fin 200) (k : Fin 106)
    (hs : Selected g r i (.bank k)) :
    actualStep N Q g r t =
      edgeValue Q t r (bankEdges N Q r (actionOfSlot k)) := by
  have hc : children N Q g r =
      bankEdges N Q r (actionOfSlot k) := by
    simp [children, hs.1, hs.2, branchEdges]
  exact congrArg (edgeValue Q t r) hc

/-- The immediate value from the literal selected children is exactly
the finite row evaluation; it does not claim a count or error bound. -/
theorem step_row_value (N : ℕ) (Q : ℝ) (g : ℕ)
    (r : Request) (t : Table) :
    (∑ b : RowAtom,
      edgeRow Q r (children N Q g r) b *
        oldAtomValue (t true) (t false) b) =
    actualStep N Q g r t := by
  exact edgeRow_value Q t r (children N Q g r)

end
end ImbalancedChen.Part5OriginalH430ActualRequestAllActionWave
