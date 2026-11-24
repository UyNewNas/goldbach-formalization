import ImbalancedChen.P2OriginalCompactQ80LowerDifference
import ImbalancedChen.P2OriginalCompactQ80JensenBounds
import ImbalancedChen.P2OriginalCompactQ80Selection
import ImbalancedChen.P2OriginalCompactQ80Reachability

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNCHECKED.

The literal original Q80 enclosure is paid on every original source-forest
entry. All analytic candidate ports in Selection are instantiated here by
proved source formulas. No desired factor, mean, leaf, integral or charged
bound is a hypothesis. The actual normalized21 roots and exact midpoint
children provide Geometry; it is not an external per-leaf certificate.

This is a source proof candidate, not an evaluated historical run. The
original table initialization diagnostics, full Python assertion refinement,
run/stop checks and historical endpoint remain separately tracked. In
particular sourceAssertions is the displayed partial inventory, not a claim
that every Python primitive assertion has been formalized.
-/
namespace ImbalancedChen.P2OriginalCompactQ80CompleteSoundnessSourceOnly

noncomputable section
open Set MeasureTheory
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80ArithmeticSourceOnly
open P2OriginalCompactQ80LeafSourceOnly
open P2OriginalCompactQ80ReachabilitySourceOnly
open P2OriginalCompactQ80JensenBoundsSourceOnly
open P2OriginalCompactQ80SelectionSourceOnly
open P2OriginalPrioritySerialQueueSourceOnly
open P2OriginalPriorityForestLedgerSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open P4AOriginalClosedTreeStructuralAggregationSourceOnly
open OriginalThirdCompactPartitionSourceOnly

/-- Both ends of the actual original enclosure, with every source min,
zero exit, ordered/symmetric case and final integer round preserved. -/
theorem enclose_contains_integral (box : RawBox) (g : Geometry box) :
    val (enclose box).lower ≤ (∫ t in rootCell box,compactKernel t) ∧
      (∫ t in rootCell box,compactKernel t) ≤ val (enclose box).upper := by
  apply enclose_contains_from_candidates box g
  · intro t ht
    exact P2OriginalCompactQ80PhiBoundsSourceOnly.lowerDifference_pointwise box g ht
  · intro j hi hj
    exact (jensenDifferenceUpper_sound box g hi j hj).2

/-- The source final assertion follows from actual analytic soundness. -/
theorem enclose_integer_order (box : RawBox) (g : Geometry box) :
    0 ≤ (enclose box).lower ∧ (enclose box).lower ≤ (enclose box).upper := by
  apply enclose_integer_order_from_candidates box g
  · intro t ht
    exact P2OriginalCompactQ80PhiBoundsSourceOnly.lowerDifference_pointwise box g ht
  · intro j hi hj
    exact (jensenDifferenceUpper_sound box g hi j hj).2

/-- The named partial source assertion inventory is discharged; the
separate full primitive-assertion inventory is not silently identified with it. -/
theorem sourceAssertions_of_geometry (box : RawBox) (g : Geometry box) :
    sourceAssertions box := by
  by_cases ho : outside box
  · exact Or.inl ho
  apply Or.inr
  refine ⟨g.muCut,?_⟩
  by_cases hc : thetaInteger ≤ (phiRange box).lo
  · exact Or.inl hc
  apply Or.inr
  refine ⟨g.residual,?_⟩
  by_cases hz : upperBeforeJensen box = 0
  · exact Or.inl hz
  exact Or.inr ⟨fun _ => source_jensenAssertions box g,enclose_integer_order box g⟩

/-- Every actual source entry includes its evaluator value by construction.
There is no arbitrary enclosure, cached estimate or leaf geometry premise. -/
theorem forestEntry_contains_integral (forest : SourceForest enclose initialSeeds)
    (p : Entry) (hp : p ∈ entries forest) :
    val p.bounds.lower ≤ (∫ t in rootCell p.cell,compactKernel t) ∧
      (∫ t in rootCell p.cell,compactKernel t) ≤ val p.bounds.upper := by
  rw [entry_enclose forest p hp]
  exact enclose_contains_integral p.cell
    (forestEntry_geometry forest geometry_mem_initialSeeds p hp)

theorem stateEntry_contains_integral (st : State enclose) (p : Entry)
    (hp : p ∈ entries st.forest) :
    val p.bounds.lower ≤ (∫ t in rootCell p.cell,compactKernel t) ∧
      (∫ t in rootCell p.cell,compactKernel t) ≤ val p.bounds.upper :=
  forestEntry_contains_integral st.forest p hp

theorem stateEntry_integer_order (st : State enclose) (p : Entry)
    (hp : p ∈ entries st.forest) :
    0 ≤ p.bounds.lower ∧ p.bounds.lower ≤ p.bounds.upper := by
  rw [entry_enclose st.forest p hp]
  exact enclose_integer_order p.cell (stateEntry_geometry st p hp)

theorem stateEntry_sourceAssertions (st : State enclose) (p : Entry)
    (hp : p ∈ entries st.forest) : sourceAssertions p.cell :=
  sourceAssertions_of_geometry p.cell (stateEntry_geometry st p hp)

private theorem list_integral_enclosure (xs : List Entry)
    (h : ∀ p ∈ xs,
      val p.bounds.lower ≤ (∫ t in rootCell p.cell,compactKernel t) ∧
        (∫ t in rootCell p.cell,compactKernel t) ≤ val p.bounds.upper) :
    val (lowerSum xs) ≤ ((xs.map (fun p => ∫ t in rootCell p.cell,compactKernel t)).sum) ∧
      ((xs.map (fun p => ∫ t in rootCell p.cell,compactKernel t)).sum) ≤ val (upperSum xs) := by
  revert h
  induction xs with
  | nil => intro h; simp [lowerSum,upperSum,val]
  | cons p ps ih =>
      intro h
      have hp := h p (by simp)
      have ht := ih (fun q hq => h q (by simp [hq]))
      change val (p.bounds.lower+lowerSum ps) ≤
          (∫ t in rootCell p.cell,compactKernel t)+
            (ps.map (fun p => ∫ t in rootCell p.cell,compactKernel t)).sum ∧
        (∫ t in rootCell p.cell,compactKernel t)+
            (ps.map (fun p => ∫ t in rootCell p.cell,compactKernel t)).sum ≤
          val (p.bounds.upper+upperSum ps)
      rw [val_add,val_add]
      exact ⟨add_le_add hp.1 ht.1,add_le_add hp.2 ht.2⟩

/-- The original compact integral is bounded by the complete terminal
integer totals. Exact and empty leaves remain in the source forest. -/
theorem forest_integral_enclosure (forest : SourceForest enclose initialSeeds) :
    val (lowerSum (entries forest)) ≤ originalCompactThirdCorrection ∧
      originalCompactThirdCorrection ≤ val (upperSum (entries forest)) := by
  rw [complete_integral_identity forest]
  exact list_integral_enclosure (entries forest) (forestEntry_contains_integral forest)

/-- Any true source-run state inherits the actual compact interval; the
Run witness supplies only the source history and cached sum invariant. -/
theorem run_integral_enclosure {fixed target : ℚ} {budget : ℕ} {st : State enclose}
    (h : Run enclose fixed target budget st) :
    val st.totalLower ≤ originalCompactThirdCorrection ∧
      originalCompactThirdCorrection ≤ val st.totalUpper := by
  have hi := run_invariant h
  rw [hi.1,hi.2.1]
  exact forest_integral_enclosure st.forest

private theorem list_local_charges (xs : List Entry)
    (h : ∀ p ∈ xs, (∫ t in rootCell p.cell,compactKernel t) ≤ val p.bounds.upper) :
    List.Forall₂ (fun domain q => (∫ t in domain,compactKernel t) ≤ (q : ℝ)/2^80)
      (xs.map (fun p => rootCell p.cell)) (xs.map (fun p => p.bounds.upper)) := by
  revert h
  induction xs with
  | nil => intro h; exact List.Forall₂.nil
  | cons p ps ih =>
      intro h
      apply List.Forall₂.cons
      · simpa only [val,scale] using h p (by simp)
      · exact ih (fun q hq => h q (by simp [hq]))

/-- The exact positional K charge tree is locally paid by the actual Q80
evaluator. Its old per-leaf analytic port is eliminated, not assumed. -/
theorem chargeTree_local {fixed target : ℚ} {budget : ℕ} {st : State enclose}
    (h : Run enclose fixed target budget st) : LocalChargeBound (chargeTree h) compactRegion := by
  apply (chargeTree_local_iff h).2
  exact list_local_charges (entries st.forest)
    (fun p hp => (stateEntry_contains_integral st p hp).2)

/-- Restricting to positive-error heap entries does not drop a nonzero
uncertainty. Consistency is proved only where needed, on the actual forest. -/
theorem run_error_ledger_actual {fixed target : ℚ} {budget : ℕ} {st : State enclose}
    (h : Run enclose fixed target budget st) :
    st.totalUpper-st.totalLower = errorSum (heapContents (entries st.forest)) := by
  rw [errorSum_heapContents _ (fun p hp => (stateEntry_integer_order st p hp).2),
    errorSum_eq_difference]
  exact congrArg₂ (fun a b : ℤ => a-b) (run_invariant h).2.1 (run_invariant h).1

end
end ImbalancedChen.P2OriginalCompactQ80CompleteSoundnessSourceOnly
