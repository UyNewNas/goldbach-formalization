import ImbalancedChen.Part5OriginalH430UpperOverlapPhysicalSlot

/-!
P5.6 / h34 — literal U3/U4 upper-overlap Q and second-Rosser
compatibility, on the ORIGINAL selected quotient (p,q) source.

On the entire original U4 interval, t < 59/250 < 57/224.
The actual U3 sourceResidual is therefore mainResidual, exactly as
for U4, independently of tau. Since BOTH frozen Q definitions apply
the same frozenLevel at the same precision to that total, the two
physical Q values actually coincide on this interval.

We also compare the real root-stage and second-Rosser predicates,
and preserve their genuine chosen factor/physical-slot consequences.
This is stronger than an abstract "if Q agrees" collision test, but
it supplies NO extra full/selected/inherited owner or history capacity.
The original two arithmetic tags must still be paid separately, or
their unpaid excess kept explicit. The frozen root TypedNodes themselves
are NOT claimed equal (their root-type/ceiling data differ).

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430UpperOverlapCommonQ

noncomputable section
open Set
open scoped Classical BigOperators
open Part5UpperTables.OriginalU34
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430OriginalUpperOverlapCount
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430ActualSecondRosserRetention
open Part5OriginalH430TaggedRankTwoFibreCapacity
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430UpperOverlapPhysicalSlot

/-- The actual original U4 upper prime cutoff lies strictly before
U3's *literal* main-to-tail switch; no lower h-start is involved. -/
theorem original_u4_before_true_upper_switch
    (N : ℕ) (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4) :
    physicalPrime N x.1 < tailCutoff := by
  have hp : x.1 ∈ originalBand N .U4 :=
    (Finset.mem_sigma.mp hx).1
  have hb : physicalPrime N x.1 ∈ Icc
      Part5OriginalUpsilon5CausalDictionary.a (59 / 250 : ℝ) := by
    simpa only [rootBand] using (original_band_geometry hN hp)
  exact lt_of_le_of_lt hb.2 (by norm_num [tailCutoff])

/-- On this exact source interval the physical TOTAL level, not just
the H430 query, is identical before any cumulative root freezing. -/
theorem original_upper_source_total_common
    (tau t : ℝ) (ht : t < tailCutoff) :
    (sourceRoot .U3 tau t).physical.total =
      (sourceRoot .U4 tau t).physical.total := by
  simp [sourceRoot, sourceResidual, U3Residual, ht]

/-- The same cumulative frozen level is applied to equal actual
physical totals. The result holds at EVERY unchanged precision. -/
theorem original_upper_frozen_Q_common
    (N precision p : ℕ) (tau : ℝ)
    (ht : physicalPrime N p < tailCutoff) :
    rootQ N precision .U3 tau p =
      rootQ N precision .U4 tau p := by
  change (N : ℝ) ^
      frozenLevel precision
        (sourceRoot .U3 tau (physicalPrime N p)).physical.total =
    (N : ℝ) ^
      frozenLevel precision
        (sourceRoot .U4 tau (physicalPrime N p)).physical.total
  rw [original_upper_source_total_common tau (physicalPrime N p) ht]

/-- The real U4-selected (p,q) fibre has the SAME physical Q under its
U3 and U4 arithmetic tags. The old possibility of different Q is
eliminated precisely on this source interval, not on all U3 roots. -/
theorem original_u4_overlap_real_Q_equal
    (N precision : ℕ) (tau : ℝ) (hN : 2 ≤ N)
    (x : TaggedPair) (hx : x ∈ originalPairs N .U4) :
    rootQ N precision .U3 tau x.1 =
      rootQ N precision .U4 tau x.1 :=
  original_upper_frozen_Q_common N precision x.1 tau
    (original_u4_before_true_upper_switch N hN x hx)

/-- True root-stage selection is tag-independent on the original
U4 overlap, because it reads the same p and now-proved same Q.
No assertion that the original root stage is always admitted. -/
theorem original_u4_overlap_root_stage_iff
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4) :
    selectedOriginalRootStage N cap precision tau z0 lower
        (Sum.inl x) ↔
      selectedOriginalRootStage N cap precision tau z0 lower
        (Sum.inr x) := by
  have hQ := original_u4_overlap_real_Q_equal
    N precision tau hN x hx
  simp [selectedOriginalRootStage, originalPhysicalQ,
    arithmeticPrime, hQ]

/-- Even at the *second* actual Rosser policy gate, eligibility of a
specified prime ell of the original q is identical across tags.
This is not the final full/inherited historical owner. -/
theorem original_u4_overlap_retained_ell_iff
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4) (ell : ℕ) :
    retainedOriginalSecond N cap precision tau z0 lower
        (Sum.inl x) ell ↔
      retainedOriginalSecond N cap precision tau z0 lower
        (Sum.inr x) ell := by
  have hQ := original_u4_overlap_real_Q_equal
    N precision tau hN x hx
  simp [retainedOriginalSecond, originalPhysicalQ,
    arithmeticPrime, hQ]

/-- The complete original q-factor retention predicate is also
the same: arithmetic p,q and the actual second policy are shared. -/
theorem original_u4_overlap_has_retained_iff
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4) :
    hasRetainedOriginalSecond N cap precision tau z0 lower
        (Sum.inl x) ↔
      hasRetainedOriginalSecond N cap precision tau z0 lower
        (Sum.inr x) := by
  have hQ := original_u4_overlap_real_Q_equal
    N precision tau hN x hx
  simp [hasRetainedOriginalSecond, retainedOriginalSecond,
    originalPhysicalQ, arithmeticPrime, arithmeticQuotientPrime, hQ]

/-- The EXISTING actual chosenSecondFactor uses Classical.choose on
the same unfolded existential predicate for the two U4-overlap tags.
Proof irrelevance therefore identifies the chosen ell as well.
The arbitrary q labels are not replaced by their selected factors. -/
theorem original_u4_overlap_chosen_second_equal
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4) :
    chosenSecondFactor N cap precision tau z0 lower
        (Sum.inl x) =
      chosenSecondFactor N cap precision tau z0 lower
        (Sum.inr x) := by
  have hQ := original_u4_overlap_real_Q_equal
    N precision tau hN x hx
  simp [chosenSecondFactor, hasRetainedOriginalSecond,
    retainedOriginalSecond, originalPhysicalQ,
    arithmeticPrime, arithmeticQuotientPrime, hQ]

/-- All actual chosen (Q,p,ell) SLOTS on the original U4 overlap
coincide across tags, even though their arithmetic receipts are
distinct. This still does NOT identify their root request TypedNodes
or give two payments from one first-exit event. -/
theorem original_u4_overlap_actual_slot_equal
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4) :
    physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower (Sum.inl x)) =
      physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower (Sum.inr x)) := by
  apply (original_overlap_chosen_slot_eq_iff
    N cap precision tau z0 lower x).mpr
  exact ⟨original_u4_overlap_real_Q_equal N precision tau hN x hx,
    original_u4_overlap_chosen_second_equal
      N cap precision tau z0 lower hN x hx⟩

/-- Every genuinely retained double-tag U4 pair is a same-slot
collision, not a separate-slot receipt. The condition both tags
survive remains literal: no membership is asserted unconditionally. -/
theorem original_u4_both_retained_all_same_slot
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) :
    samePhysicalSlotOverlap N cap precision tau z0 lower =
      bothTagRetainedOverlap N cap precision tau z0 lower := by
  ext x
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).1
  · intro hx
    have hx4 : x ∈ originalPairs N .U4 :=
      (Finset.mem_filter.mp hx).1
    exact Finset.mem_filter.mpr
      ⟨hx, original_u4_overlap_actual_slot_equal
        N cap precision tau z0 lower hN x hx4⟩

/-- Consequently the distinct physical-slot subledger of ACTUALLY
double-retained original U4 receipts is empty at the pinned phase.
The unpaid same-slot tag multiplicity remains unchanged. -/
theorem original_u4_both_retained_no_distinct_slots
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) :
    distinctPhysicalSlotOverlap N cap precision tau z0 lower = ∅ := by
  simp [distinctPhysicalSlotOverlap,
    original_u4_both_retained_all_same_slot
      N cap precision tau z0 lower hN]

end
end ImbalancedChen.Part5OriginalH430UpperOverlapCommonQ
