import ImbalancedChen.Part5OriginalH430RequestedFrontierMultiplicity

/-!
P5.6 / h34: realization of the exact selected frontier as a weighted
OLD-TABLE list. SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.

The previous frontier theorem is an equality of ordered occurrence lists.
Here its selected-edge contents are evaluated with the actual prior iterate,
the original multiplicative edge marks, the same frozen Q, and the original
thetaAtom / requestValue.  In particular, the `generationValue` Finset
indexed by ACTUAL parent positions equals the unquotiented sum over ALL
occurrences at the next generated request level.

No equality with U3/U4 arithmetic prime/PP counts, root count weights,
selected-count owner, base/seed/floor, or causal430+11 is asserted.
-/

namespace ImbalancedChen.Part5OriginalH430RequestedLevelRealization

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedAllChoice
open Part5OriginalH430RequestedFrontierTransport
open Part5OriginalH430RequestedFrontierMultiplicity

/-- Literal table value of a SINGLE tagged occurrence.  Do not deduplicate
by physical node, integer product, prime word, or geometric catalogue. -/
def realizedCellMass (N : ℕ) (Q : ℝ) (t : Table)
    (o : Occurrence N) : ℝ :=
  mark o * thetaAtom N Q (parentProduct o.current.old) *
    requestValue t o.current

/-- Evaluating one actual selected child list agrees definitionally with
the older childTableMass.  The mark is evaluated on the appended path. -/
theorem child_marked_list_eq_tableMass (N : ℕ) (Q : ℝ)
    (t : Table) (o : Occurrence N) (es : List (Edge N)) :
    (((es.map (extend o)).map (realizedCellMass N Q t)).sum) =
      childTableMass N Q t o es := by
  unfold childTableMass realizedCellMass
  simp only [List.map_map]
  rfl

/-- An EXACT finite LIST identity for every input parent occurrence.
It consumes ONLY selected children and retains repetitions and order.
No positivity, error budget or arithmetic-count license is needed. -/
theorem selectedFrontier_realized_mass (N : ℕ) (Q : ℝ)
    (t : Table) (g : ℕ) (xs : List (Occurrence N)) :
    ((selectedFrontier N Q g xs).map (realizedCellMass N Q t)).sum =
      (xs.map (fun o =>
        mark o * edgeValue Q t o.current (children N Q g o.current))).sum := by
  induction xs with
  | nil => rfl
  | cons o os ih =>
      have hfirst :
          (((children N Q g o.current).map (extend o)).map
            (realizedCellMass N Q t)).sum =
            mark o * edgeValue Q t o.current
              (children N Q g o.current) := by
        rw [child_marked_list_eq_tableMass]
        exact childTableMass_eq_mark_edgeValue N Q t o
          (children N Q g o.current)
      change
        ((((children N Q g o.current).map (extend o)) ++
          selectedFrontier N Q g os).map
            (realizedCellMass N Q t)).sum =
          mark o * edgeValue Q t o.current
            (children N Q g o.current) +
          (os.map (fun u =>
            mark u * edgeValue Q t u.current
              (children N Q g u.current))).sum
      rw [List.map_append, List.sum_append, hfirst, ih]

/-- Finset of exact list POSITIONS and ordinary List.sum give the same
value, including equal-valued repeated entries.  This is not a Set.sum. -/
private theorem list_sum_eq_position_sum {α : Type*}
    (xs : List α) (f : α → ℝ) :
    (xs.map f).sum = ∑ j : Fin xs.length, f (xs.get j) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Fin.sum_univ_succ]
      simpa using congrArg (fun z : ℝ => f x + z) ih

/-- The unquotiented TRUE g-level list has the same old-array marked
value as the actual g+1 parents expanded by their selected winning edges.
Q is that root's frozen Q and the old array is iterate g, without a new
choice of rho, scalar-owner, prime source, or correction coefficient. -/
theorem actual_level_realized_mass_eq_parents (N n : ℕ)
    (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    ((levelRequests N n root tau p g.val).map
      (realizedCellMass N (rootQ N n root tau p)
        (iterate g.val))).sum =
      ((levelRequests N n root tau p (g.val + 1)).map (fun o =>
        mark o * edgeValue (rootQ N n root tau p) (iterate g.val)
          o.current
          (children N (rootQ N n root tau p) g.val o.current))).sum := by
  rw [level_frontier_list]
  exact selectedFrontier_realized_mass N (rootQ N n root tau p)
    (iterate g.val) g.val
    (levelRequests N n root tau p (g.val + 1))

/-- Connect the NEW exact list-value realization to the EXISTING
generationValue with its old level-index and computed edge weights.
This pays a finite reindexing obligation; it does not pay the manuscript's
missing identification with original U3/U4 arithmetic selected-counts. -/
theorem generationValue_eq_actual_level_mass (N n : ℕ)
    (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    generationValue N n root tau p g =
      ((levelRequests N n root tau p g.val).map
        (realizedCellMass N (rootQ N n root tau p)
          (iterate g.val))).sum := by
  rw [actual_level_realized_mass_eq_parents]
  rw [generationValue_eq_nextLevelMass]
  unfold nextLevelMass
  have hparent :
      (∑ j : Index N n root tau p g,
        mark (levelOccurrence j) *
          edgeValue (rootQ N n root tau p) (iterate g.val)
            (levelOccurrence j).current
            (children N (rootQ N n root tau p) g.val
              (levelOccurrence j).current)) =
        ((levelRequests N n root tau p (g.val + 1)).map (fun o =>
          mark o * edgeValue (rootQ N n root tau p) (iterate g.val)
            o.current
            (children N (rootQ N n root tau p) g.val o.current))).sum := by
    simpa only [Index, LevelIndex, levelOccurrence] using
      (list_sum_eq_position_sum
        (levelRequests N n root tau p (g.val + 1))
        (fun o => mark o * edgeValue (rootQ N n root tau p)
          (iterate g.val) o.current
          (children N (rootQ N n root tau p) g.val o.current))).symm
  calc
    (∑ j : Index N n root tau p g,
       childTableMass N (rootQ N n root tau p) (iterate g.val)
         (levelOccurrence j)
         (children N (rootQ N n root tau p) g.val
           (levelOccurrence j).current)) =
      ∑ j : Index N n root tau p g,
        mark (levelOccurrence j) *
          edgeValue (rootQ N n root tau p) (iterate g.val)
            (levelOccurrence j).current
            (children N (rootQ N n root tau p) g.val
              (levelOccurrence j).current) := by
                apply Finset.sum_congr rfl
                intro j _
                exact childTableMass_eq_mark_edgeValue
                  N (rootQ N n root tau p) (iterate g.val)
                  (levelOccurrence j)
                  (children N (rootQ N n root tau p) g.val
                    (levelOccurrence j).current)
    _ = _ := hparent

end
end ImbalancedChen.Part5OriginalH430RequestedLevelRealization
