import ImbalancedChen.Part5OriginalH430UpperOverlapCommonQ

/-!
P5.6 / h34 — exact RETAINED U3/U4 overlap multiplicity.

The fixed upper U4 quotient source is inside U3. Previous source proved
that the actual frozen Q, root-stage predicate, retained second-prime
predicate, chosen ell and (Q,p,ell) slot coincide on that overlap.
This packet proves a stronger consequence at the literal original
retainedReceipts FILTER: one retained U4 quotient forces BOTH arithmetic
tags to survive together. There are no one-sided retained tags on the
true U4 overlap, independently of the precise lower/upper policy Bool.

The full signed retained-source sum consequently contains w3+w4 per
such (p,q), not just one q/slot weight. This is only a source identity:
a common physical slot is not an injective or paid history Fin position.
Actual full/selected/inherited owners, first-excluded capacity and
signed Euler payment remain open.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430UpperRetainedTagPairing

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalUpperOverlapCount
open Part5OriginalH430TaggedRankTwoFibreCapacity
open Part5OriginalH430UpperOverlapPhysicalSlot
open Part5OriginalH430UpperOverlapCommonQ
open Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430ActualSecondRosserRetention

/-- On an actual U4 (p,q) source, the ENTIRE root-plus-second
retention gate agrees across original U3/U4 arithmetic tags.
No upper-history owner or extra capacity is part of this gate. -/
theorem original_u4_overlap_full_retention_gate_iff
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4) :
    (selectedOriginalRootStage N cap precision tau z0 lower (Sum.inl x) ∧
      hasRetainedOriginalSecond N cap precision tau z0 lower (Sum.inl x)) ↔
    (selectedOriginalRootStage N cap precision tau z0 lower (Sum.inr x) ∧
      hasRetainedOriginalSecond N cap precision tau z0 lower (Sum.inr x)) := by
  constructor
  · rintro ⟨hroot, hfactor⟩
    exact ⟨(original_u4_overlap_root_stage_iff
        N cap precision tau z0 lower hN x hx).mp hroot,
      (original_u4_overlap_has_retained_iff
        N cap precision tau z0 lower hN x hx).mp hfactor⟩
  · rintro ⟨hroot, hfactor⟩
    exact ⟨(original_u4_overlap_root_stage_iff
        N cap precision tau z0 lower hN x hx).mpr hroot,
      (original_u4_overlap_has_retained_iff
        N cap precision tau z0 lower hN x hx).mpr hfactor⟩

/-- The literal two filters defining retainedReceipts preserve both
actual labels together. This is stronger than assuming both labels
have separately survived, and uses original U4 membership. -/
theorem original_u4_retained_inl_iff_inr
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4) :
    (Sum.inl x : TaggedReceiver) ∈
        retainedReceipts N cap precision tau z0 lower ↔
      (Sum.inr x : TaggedReceiver) ∈
        retainedReceipts N cap precision tau z0 lower := by
  have htags := original_u4_pair_has_two_tags N (by omega) x hx
  have hgate := original_u4_overlap_full_retention_gate_iff
    N cap precision tau z0 lower hN x hx
  simp only [retainedReceipts, Finset.mem_filter]
  constructor
  · rintro ⟨⟨_, hroot⟩, hfactor⟩
    have h := hgate.mp ⟨hroot, hfactor⟩
    exact ⟨⟨htags.2, h.1⟩, h.2⟩
  · rintro ⟨⟨_, hroot⟩, hfactor⟩
    have h := hgate.mpr ⟨hroot, hfactor⟩
    exact ⟨⟨htags.1, h.1⟩, h.2⟩

/-- The previously conditional both-tag overlap is EXACTLY the
actual left-tag retained U4 source. A lone left-tag survivor is
impossible on the shared upper U4 band. -/
theorem original_u4_both_retained_eq_left_filter
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) :
    bothTagRetainedOverlap N cap precision tau z0 lower =
      (originalPairs N .U4).filter (fun x =>
        (Sum.inl x : TaggedReceiver) ∈
          retainedReceipts N cap precision tau z0 lower) := by
  ext x
  simp only [bothTagRetainedOverlap, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hleft, _⟩
    exact ⟨hx, hleft⟩
  · rintro ⟨hx, hleft⟩
    exact ⟨hx, hleft,
      (original_u4_retained_inl_iff_inr
        N cap precision tau z0 lower hN x hx).mp hleft⟩

/-- One actual retained original U4 quotient gives two DISTINCT
retained arithmetic receipts at the SAME physical rank-two slot,
not two historical owners. In particular the receipt-to-slot map
cannot be injective whenever this original overlap is nonempty. -/
theorem original_u4_one_retained_forces_slot_collision
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    ¬ Set.InjOn
      (fun z : TaggedReceiver =>
        physicalRankTwoSlot N precision tau
          (chosenRankTwoKey N cap precision tau z0 lower z))
      (↑(retainedReceipts N cap precision tau z0 lower) :
        Set TaggedReceiver) := by
  have hboth : x ∈ bothTagRetainedOverlap
      N cap precision tau z0 lower := by
    rw [original_u4_both_retained_eq_left_filter
      N cap precision tau z0 lower hN]
    exact Finset.mem_filter.mpr ⟨hx, hret⟩
  have hs : x ∈ samePhysicalSlotOverlap
      N cap precision tau z0 lower := by
    rw [original_u4_both_retained_all_same_slot
      N cap precision tau z0 lower hN]
    exact hboth
  exact actual_chosen_slot_map_not_injective_of_overlap
    N cap precision tau z0 lower x hs

/-- Exact tagged-source retained sum on the original U3-exclusive
part and the literal shared U4 part. The U4 term is w(inl x)+w(inr x)
whenever its ACTUAL root+second gates pass; no same-weight assumption,
sign cancellation, quotient-prime replacement, or historical payment.

The statement is generic over an additive commutative monoid so that
natural receipt multiplicity and signed real roots use the SAME proof. -/
theorem original_retained_u34_tagged_overlap_weight
    {M : Type*} [AddCommMonoid M]
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (w : TaggedReceiver → M) :
    (∑ z ∈ retainedReceipts N cap precision tau z0 lower, w z) =
    (∑ x ∈ upperExclusivePairs N,
      if selectedOriginalRootStage N cap precision tau z0 lower (Sum.inl x) ∧
        hasRetainedOriginalSecond N cap precision tau z0 lower (Sum.inl x)
      then w (Sum.inl x) else 0) +
    (∑ x ∈ originalPairs N .U4,
      if selectedOriginalRootStage N cap precision tau z0 lower (Sum.inl x) ∧
        hasRetainedOriginalSecond N cap precision tau z0 lower (Sum.inl x)
      then w (Sum.inl x) + w (Sum.inr x) else 0) := by
  classical
  let gate : TaggedReceiver → Prop := fun z =>
    selectedOriginalRootStage N cap precision tau z0 lower z ∧
    hasRetainedOriginalSecond N cap precision tau z0 lower z
  have hfilter :
      retainedReceipts N cap precision tau z0 lower =
        (originalTagged N).filter gate := by
    ext z
    simp [retainedReceipts, gate, and_assoc]
  have htag :
      (∑ z ∈ retainedReceipts N cap precision tau z0 lower, w z) =
        (∑ x ∈ originalPairs N .U3,
          if gate (Sum.inl x) then w (Sum.inl x) else 0) +
        (∑ x ∈ originalPairs N .U4,
          if gate (Sum.inr x) then w (Sum.inr x) else 0) := by
    rw [hfilter, Finset.sum_filter]
    simp [originalTagged, Finset.sum_disjSum]
  rw [htag, original_u3_pairs_signed_partition N (by omega)
    (fun x => if gate (Sum.inl x) then w (Sum.inl x) else 0)]
  calc
    _ = (∑ x ∈ upperExclusivePairs N,
          if gate (Sum.inl x) then w (Sum.inl x) else 0) +
        ∑ x ∈ originalPairs N .U4,
          ((if gate (Sum.inl x) then w (Sum.inl x) else 0) +
           (if gate (Sum.inr x) then w (Sum.inr x) else 0)) := by
      rw [Finset.sum_add_distrib]
      abel
    _ = _ := by
      apply congrArg (fun v : M =>
        (∑ x ∈ upperExclusivePairs N,
          if gate (Sum.inl x) then w (Sum.inl x) else 0) + v)
      apply Finset.sum_congr rfl
      intro x hx
      have heq : gate (Sum.inl x) ↔ gate (Sum.inr x) :=
        original_u4_overlap_full_retention_gate_iff
          N cap precision tau z0 lower hN x hx
      by_cases hg : gate (Sum.inl x)
      · have hr := heq.mp hg
        simp only [if_pos hg, if_pos hr]
      · have hr : ¬ gate (Sum.inr x) := by
          intro hr
          exact hg (heq.mpr hr)
        simp only [if_neg hg, if_neg hr]

end
end ImbalancedChen.Part5OriginalH430UpperRetainedTagPairing
