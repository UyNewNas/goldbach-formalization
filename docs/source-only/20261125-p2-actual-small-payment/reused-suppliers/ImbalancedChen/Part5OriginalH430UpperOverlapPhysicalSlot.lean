import ImbalancedChen.Part5OriginalH430OriginalUpperOverlapCount
import ImbalancedChen.Part5OriginalH430PhysicalSlotCollisionLedger

/-!
P5.6 / h34 — original U3/U4 overlap at the ACTUAL physical-Q,
retained second-prime slot, and original q/tag multiplicity.

The U4 original (p,q) source also occurs under the U3 tag. These two
arithmetical receipts do NOT automatically name one historical event:
rootQ may depend on the tag, and the genuinely retained second prime
factor chosen from q may also depend on that physical Q.

This packet gives the exact necessary-and-sufficient collision test
for the existing selected rank-two key, restricted to pairs for which
BOTH tags really survive the existing retained-receipt predicate.
When that test holds the actual physical slot map is demonstrably
non-injective on the original retained source. The collision is an
UNPAID capacity obligation, not a second historical event or an
Euler payment. None of the original full/selected/inherited owner,
upper H430 count density, or feedback/base/seed is assumed.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430UpperOverlapPhysicalSlot

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalUpperOverlapCount
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430TaggedRankTwoFibreCapacity
open Part5OriginalH430PhysicalSlotCollisionLedger

/-- The U4 arithmetic intersection for which BOTH distinct U3/U4
receipts survive the literal original root and second Rosser tests.
No generic or tag-blind selected gate is substituted. -/
def bothTagRetainedOverlap
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    Finset TaggedPair :=
  (originalPairs N .U4).filter (fun x =>
    Sum.inl x ∈ retainedReceipts N cap precision tau z0 lower ∧
    Sum.inr x ∈ retainedReceipts N cap precision tau z0 lower)

/-- The subset whose TWO actual chosen (Q,p,ell) slots coincide.
This is not automatically all U4 pairs; the true Q is tag-dependent. -/
def samePhysicalSlotOverlap
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    Finset TaggedPair :=
  (bothTagRetainedOverlap N cap precision tau z0 lower).filter (fun x =>
    physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower (Sum.inl x)) =
    physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower (Sum.inr x)))

/-- Both tags survive, but their true historical physical slots differ. -/
def distinctPhysicalSlotOverlap
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    Finset TaggedPair :=
  bothTagRetainedOverlap N cap precision tau z0 lower \
    samePhysicalSlotOverlap N cap precision tau z0 lower

/-- The original U4 quotient occurrence appears twice in the genuine
U3+U4 arithmetic source, before any historical counting estimate. -/
theorem original_u4_pair_has_two_tags
    (N : ℕ) (hN : 1 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4) :
    (Sum.inl x : TaggedReceiver) ∈ originalTagged N ∧
    (Sum.inr x : TaggedReceiver) ∈ originalTagged N := by
  have h3 : x ∈ originalPairs N .U3 := by
    rw [original_u3_pairs_partition N hN]
    exact Finset.mem_union.mpr (Or.inr hx)
  constructor
  · simp [originalTagged, h3]
  · simp [originalTagged, hx]

/-- Two original labels at fixed (p,q) have precisely these two
actual physical Q parameters. Neither Q is declared equal to the other. -/
theorem original_overlap_two_physical_Q
    (N precision : ℕ) (tau : ℝ) (x : TaggedPair) :
    originalPhysicalQ N precision tau (Sum.inl x) =
        rootQ N precision .U3 tau x.1 ∧
    originalPhysicalQ N precision tau (Sum.inr x) =
        rootQ N precision .U4 tau x.1 := by
  constructor <;> rfl

/-- The EXACT test for two true U3/U4 chosen rank-two slots to be
the same. Both the physical Q and the chosen retained ell must agree.
Equality of the arithmetic (p,q) label alone is not sufficient. -/
theorem original_overlap_chosen_slot_eq_iff
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (x : TaggedPair) :
    physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower (Sum.inl x)) =
      physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower (Sum.inr x)) ↔
    rootQ N precision .U3 tau x.1 = rootQ N precision .U4 tau x.1 ∧
    chosenSecondFactor N cap precision tau z0 lower (Sum.inl x) =
      chosenSecondFactor N cap precision tau z0 lower (Sum.inr x) := by
  rw [chosen_key_physical_source, chosen_key_physical_source]
  simp only [originalPhysicalQ, arithmeticPrime, Prod.mk.injEq,
    and_true, true_and]

/-- Different true root Q parameters PREVENT a single rank-two slot
collision, irrespective of whether the original arithmetic p,q agree. -/
theorem original_overlap_distinct_Q_separates_slots
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (x : TaggedPair)
    (hQ : rootQ N precision .U3 tau x.1 ≠
      rootQ N precision .U4 tau x.1) :
    physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower (Sum.inl x)) ≠
      physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower (Sum.inr x)) := by
  intro hsame
  exact hQ ((original_overlap_chosen_slot_eq_iff
    N cap precision tau z0 lower x).mp hsame).1

/-- This membership test uses the ACTUAL two retained-receipt gates,
physical Q equality, and the true second-prime choice on each side. -/
theorem mem_same_physical_slot_overlap_iff
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (x : TaggedPair) :
    x ∈ samePhysicalSlotOverlap N cap precision tau z0 lower ↔
      x ∈ originalPairs N .U4 ∧
      Sum.inl x ∈ retainedReceipts N cap precision tau z0 lower ∧
      Sum.inr x ∈ retainedReceipts N cap precision tau z0 lower ∧
      rootQ N precision .U3 tau x.1 = rootQ N precision .U4 tau x.1 ∧
      chosenSecondFactor N cap precision tau z0 lower (Sum.inl x) =
        chosenSecondFactor N cap precision tau z0 lower (Sum.inr x) := by
  simp only [samePhysicalSlotOverlap, bothTagRetainedOverlap,
    Finset.mem_filter]
  rw [original_overlap_chosen_slot_eq_iff]
  tauto

/-- A collision pair yields TWO distinct ORIGINAL arithmetic receipts
in the existing true retained set, but the SAME chosen physical slot.
This states the genuine multiplicity obstruction, not its payment. -/
theorem overlap_collision_two_distinct_retained_receipts
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (x : TaggedPair)
    (hx : x ∈ samePhysicalSlotOverlap N cap precision tau z0 lower) :
    (Sum.inl x : TaggedReceiver) ∈
        retainedReceipts N cap precision tau z0 lower ∧
    (Sum.inr x : TaggedReceiver) ∈
        retainedReceipts N cap precision tau z0 lower ∧
    (Sum.inl x : TaggedReceiver) ≠ Sum.inr x ∧
    physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower (Sum.inl x)) =
      physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower (Sum.inr x)) := by
  have h := (Finset.mem_filter.mp hx)
  have hr := (Finset.mem_filter.mp h.1).2
  refine ⟨hr.1, hr.2, ?_, h.2⟩
  intro heq
  cases heq

/-- If even one actual overlap collision survives, the actual
retained-receipt → physical-slot map is NOT injective. Consequently
one distinct historical slot cannot silently pay both U3/U4 tags. -/
theorem actual_chosen_slot_map_not_injective_of_overlap
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (x : TaggedPair)
    (hx : x ∈ samePhysicalSlotOverlap N cap precision tau z0 lower) :
    ¬ Set.InjOn
      (fun z : TaggedReceiver => physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower z))
      (↑(retainedReceipts N cap precision tau z0 lower) : Set TaggedReceiver) := by
  intro hinj
  obtain ⟨hleft, hright, hne, hslot⟩ :=
    overlap_collision_two_distinct_retained_receipts
      N cap precision tau z0 lower x hx
  apply hne
  apply hinj
  · simpa using hleft
  · simpa using hright
  · exact hslot

/-- The original U4 overlap that actually reaches BOTH rank-two
stages splits into real equal-slot collisions and distinct-slot pairs. -/
theorem both_tag_retained_overlap_partition
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    bothTagRetainedOverlap N cap precision tau z0 lower =
      samePhysicalSlotOverlap N cap precision tau z0 lower ∪
      distinctPhysicalSlotOverlap N cap precision tau z0 lower := by
  classical
  ext x
  simp only [samePhysicalSlotOverlap, distinctPhysicalSlotOverlap,
    Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union]
  tauto

/-- The two outcomes are disjoint, so a single original pair cannot
be simultaneously counted as both a collision and a separate slot. -/
theorem overlap_slot_outcomes_disjoint
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    Disjoint (samePhysicalSlotOverlap N cap precision tau z0 lower)
      (distinctPhysicalSlotOverlap N cap precision tau z0 lower) := by
  apply Finset.disjoint_left.mpr
  intro x hc hd
  exact (Finset.mem_sdiff.mp hd).2 hc

/-- This exact count isolates physical overlap collisions without
asserting any positive upper-history payment capacity or filter owner. -/
theorem both_tag_retained_overlap_card
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    (bothTagRetainedOverlap N cap precision tau z0 lower).card =
      (samePhysicalSlotOverlap N cap precision tau z0 lower).card +
      (distinctPhysicalSlotOverlap N cap precision tau z0 lower).card := by
  rw [both_tag_retained_overlap_partition]
  exact Finset.card_union_of_disjoint
    (overlap_slot_outcomes_disjoint N cap precision tau z0 lower)

/-- Unlike the old common-weight doubled-source formula, this identity
keeps DIFFERENT arbitrary signed U3 and U4 weights on overlapping
original (p,q) positions; even negative roots cannot silently merge. -/
theorem original_tag_dependent_signed_overlap
    (N : ℕ) (hN : 1 ≤ N)
    (w3 w4 : TaggedPair → ℝ) :
    (∑ z ∈ originalTagged N, Sum.elim w3 w4 z) =
      (∑ x ∈ upperExclusivePairs N, w3 x) +
      ∑ x ∈ originalPairs N .U4, (w3 x + w4 x) := by
  have htag :
      (∑ z ∈ originalTagged N, Sum.elim w3 w4 z) =
        (∑ x ∈ originalPairs N .U3, w3 x) +
        (∑ x ∈ originalPairs N .U4, w4 x) := by
    simp [originalTagged, Finset.sum_disjSum]
  rw [htag, original_u3_pairs_signed_partition N hN w3]
  rw [Finset.sum_add_distrib]
  ring

end
end ImbalancedChen.Part5OriginalH430UpperOverlapPhysicalSlot
