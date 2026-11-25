import ImbalancedChen.Part5OriginalH430PhysicalSelectedRootQFibres
import ImbalancedChen.Part5OriginalH430HistoricalPolicyGates

/-!
P5.6 / h34: original selected U3/U4 receipts at the ACTUAL
stage-zero first-exit root selection, with physical Q varying by root.

The previous physical-root three-way count classified receipts by the
literal root licence. Here the surviving predicate is identified with
a GENUINE next-selection candidate of the original historical
enumerator, rather than an abstract root mask. The original quotient
q remains in every sigma fibre and in every signed source sum.

This is only the rank-one selection moment. It does NOT identify the
full/selected/inherited count owner, a repeated q receipt with one
root mark, an accepted descendant, or any signed first-excluded
payment. The true cap premise and physical z0/lower flag remain
explicit. SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualRootStageReceipts

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430ActualRootGateCoprime
open Part5OriginalH430OriginalSelectedRootFibres
open Part5OriginalH430OriginalRootCutoffObstruction
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430HistoricalPolicyGates

/-- A genuine historical candidate with its original empty prefix,
positive root mark 1 and real enumerated prime-carrier list.
The physical Q is evaluated at this receiver's tag and selected p.
There is no assumption that each quotient q creates a new candidate. -/
def selectedOriginalRootStage
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) : Prop :=
  ∃ candidate,
    candidate ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
    candidate.selectedPrefix = [arithmeticPrime z] ∧
    ordinaryRosserRetainedPolicy lower
      (originalPhysicalQ N precision tau z)
      candidate.positive candidate.selectedPrefix = true

/-- Exact historical root-stage admission for a REAL original selected
(tag,p,q) receipt. The nondivisibility and prime conditions come from
the original arithmetic source, not a caller-supplied root licence. -/
theorem original_stage_iff_physical_root
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    {z : TaggedReceiver} (hz : z ∈ originalTagged N) :
    selectedOriginalRootStage N cap precision tau z0 lower z ↔
      rootLicensed N z0 (originalPhysicalQ N precision tau z)
        lower z := by
  have hr : z ∈ rawTagged N :=
    original_tagged_subset_raw_unconditional N hz
  have hstage := tagged_root_stage_ordinary_policy_iff
    N cap z0 lower (originalPhysicalQ N precision tau z)
    hzcap hr
  have hlicense := original_physical_licence_iff
    N precision tau z0 lower hz
  have hnot : ¬ arithmeticPrime z ∣ N :=
    raw_root_not_target N hr
  have hnonneg : (0 : ℝ) ≤ (arithmeticPrime z : ℝ) := by
    positivity
  unfold selectedOriginalRootStage
  rw [hstage, hlicense]
  simp [hnot, hnonneg]

/-- The genuine historical stage-zero candidate filter is EXACTLY
the previously proved physical-Q accepted original source. It is
not yet an owner in the full/inherited count or a final count bound. -/
theorem physical_accepted_eq_actual_stage
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    physicalRootAccepted N precision tau z0 lower =
      (originalTagged N).filter
        (selectedOriginalRootStage N cap precision tau z0 lower) := by
  classical
  ext z
  simp only [physicalRootAccepted, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hlicense⟩
    exact ⟨hz, (original_stage_iff_physical_root
      N cap precision tau z0 lower hzcap hz).2 hlicense⟩
  · rintro ⟨hz, hstage⟩
    exact ⟨hz, (original_stage_iff_physical_root
      N cap precision tau z0 lower hzcap hz).1 hstage⟩

/-- Unadmitted original receipts are exactly the physical root-gate
blockers; the statement neither deletes them nor calls them exits. -/
theorem physical_blocked_eq_no_stage
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    physicalRootBlocked N precision tau z0 lower =
      (originalTagged N).filter
        (fun z => ¬ selectedOriginalRootStage
          N cap precision tau z0 lower z) := by
  classical
  ext z
  simp only [physicalRootBlocked, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hnot⟩
    exact ⟨hz, fun hstage => hnot
      ((original_stage_iff_physical_root
        N cap precision tau z0 lower hzcap hz).1 hstage)⟩
  · rintro ⟨hz, hnot⟩
    exact ⟨hz, fun hlicense => hnot
      ((original_stage_iff_physical_root
        N cap precision tau z0 lower hzcap hz).2 hlicense)⟩

/-- The actual stage-zero root candidate is shared by ALL q within
one (U3,p) fibre. Its existence must not be multiplied into distinct
historical root marks merely because the arithmetic q values differ. -/
theorem original_U3_stage_independent_of_quotient
    (N cap precision p q₁ q₂ : ℕ) (tau z0 : ℝ) (lower : Bool) :
    selectedOriginalRootStage N cap precision tau z0 lower
        (Sum.inl (⟨p, q₁⟩ : TaggedPair)) ↔
    selectedOriginalRootStage N cap precision tau z0 lower
        (Sum.inl (⟨p, q₂⟩ : TaggedPair)) := by
  simp [selectedOriginalRootStage, originalPhysicalQ, arithmeticPrime]

/-- Separate U4 tag: its Q need not equal the U3 Q at an overlapping p. -/
theorem original_U4_stage_independent_of_quotient
    (N cap precision p q₁ q₂ : ℕ) (tau z0 : ℝ) (lower : Bool) :
    selectedOriginalRootStage N cap precision tau z0 lower
        (Sum.inr (⟨p, q₁⟩ : TaggedPair)) ↔
    selectedOriginalRootStage N cap precision tau z0 lower
        (Sum.inr (⟨p, q₂⟩ : TaggedPair)) := by
  simp [selectedOriginalRootStage, originalPhysicalQ, arithmeticPrime]

/-- The SAME actual historical root candidate, before any q is chosen.
This is one root predicate, not one independently selected q mark. -/
def originalStageRoot
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : Root) (p : ℕ) : Prop :=
  ∃ candidate,
    candidate ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
    candidate.selectedPrefix = [p] ∧
    ordinaryRosserRetainedPolicy lower (rootQ N precision k tau p)
      candidate.positive candidate.selectedPrefix = true

/-- The root-selection predicate is tested once at the genuine
tag/p-specific Q; the original quotient occurrences remain separate. -/
def originalStageBand
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : Root) : Finset ℕ :=
  (originalBand N k).filter
    (fun p => originalStageRoot N cap precision tau z0 lower k p)

def originalStagePairs
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : Root) : Finset TaggedPair :=
  (originalStageBand N cap precision tau z0 lower k).sigma
    (fun p => originalReceiver N p)

/-- Unlike a root mark=1 substitution, this is a literal equality
of sets of tagged original (p,q) receipts. The band overlap remains
two distinguishable U3/U4 occurrences. -/
theorem selected_stage_eq_original_quotient_fibres
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower) =
      (originalStagePairs N cap precision tau z0 lower .U3).disjSum
        (originalStagePairs N cap precision tau z0 lower .U4) := by
  classical
  ext z
  cases z with
  | inl v =>
      rcases v with ⟨p, q⟩
      simp [originalTagged, originalPairs, originalStagePairs,
        originalStageBand, selectedOriginalRootStage, originalStageRoot,
        originalPhysicalQ, arithmeticPrime]
  | inr v =>
      rcases v with ⟨p, q⟩
      simp [originalTagged, originalPairs, originalStagePairs,
        originalStageBand, selectedOriginalRootStage, originalStageRoot,
        originalPhysicalQ, arithmeticPrime]

/-- Count each originally selected q once per actual tag/p source
fibre, while the root selection itself was performed only once. -/
theorem selected_stage_card_original_fibres
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    ((originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower)).card =
      (∑ p ∈ originalStageBand N cap precision tau z0 lower .U3,
        (originalReceiver N p).card) +
      (∑ p ∈ originalStageBand N cap precision tau z0 lower .U4,
        (originalReceiver N p).card) := by
  rw [selected_stage_eq_original_quotient_fibres]
  simp [originalStagePairs, Finset.card_disjSum, Finset.card_sigma]

/-- Exact arbitrary signed/tag/q-dependent original arithmetic
receipts attached to real stage-zero candidate roots. No sum of one
root-mark weight is substituted for the original q-fibre weight. -/
theorem selected_stage_signed_original_fibres
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower), w z) =
      (∑ p ∈ originalStageBand N cap precision tau z0 lower .U3,
        ∑ q ∈ originalReceiver N p,
          w (Sum.inl (⟨p, q⟩ : TaggedPair))) +
      (∑ p ∈ originalStageBand N cap precision tau z0 lower .U4,
        ∑ q ∈ originalReceiver N p,
          w (Sum.inr (⟨p, q⟩ : TaggedPair))) := by
  rw [selected_stage_eq_original_quotient_fibres]
  simp [originalStagePairs, Finset.sum_disjSum, Finset.sum_sigma]

/-- The real original U3+U4 selected count is exactly stage-zero
historically admitted q receipts PLUS TWO still-unpaid failure lanes.
This is NOT the full/selected/inherited owner or a count-to-Theta bound. -/
theorem actual_original_count_with_historical_root_candidates
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    currentChenUpsilon3 N + currentChenUpsilon4 N =
      (((originalTagged N).filter
        (selectedOriginalRootStage N cap precision tau z0 lower)).card : ℝ) +
      ((rootCutoffBlocked (originalTagged N) z0).card : ℝ) +
      ((physicalPolicyBlocked N precision tau z0 lower).card : ℝ) := by
  rw [← physical_accepted_eq_actual_stage
    N cap precision tau z0 lower hzcap]
  exact actual_physical_selected_count_three_terms
    N precision tau z0 lower

/-- The signed counterpart retains arbitrary individual q/tag
receipts and leaves both unadmitted root-failure sums untouched. -/
theorem actual_original_signed_with_historical_root_candidates
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ originalTagged N, w z) =
      (∑ z ∈ (originalTagged N).filter
        (selectedOriginalRootStage N cap precision tau z0 lower), w z) +
      (∑ z ∈ rootCutoffBlocked (originalTagged N) z0, w z) +
      (∑ z ∈ physicalPolicyBlocked N precision tau z0 lower, w z) := by
  rw [← physical_accepted_eq_actual_stage
    N cap precision tau z0 lower hzcap]
  exact actual_physical_selected_signed_three_terms
    N precision tau z0 lower w

/-- Actual stage-zero historical admission NECESSARILY requires z0
strictly above the selected arithmetic band's N^a starting exponent.
The fixed manuscript's omega remains symbolic and is not chosen here. -/
theorem actual_original_stage_requires_large_presieve
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    (hstage : selectedOriginalRootStage
      N cap precision tau z0 lower z) :
    (N : ℝ) ^ a < z0 := by
  have hlicense := (original_stage_iff_physical_root
    N cap precision tau z0 lower hzcap hz).1 hstage
  have hcut : (arithmeticPrime z : ℝ) < z0 :=
    ((original_physical_licence_iff
      N precision tau z0 lower hz).1 hlicense).1
  exact raw_strict_root_requires_large_presieve N z0
    (original_tagged_subset_raw_unconditional N hz) hcut

end
end ImbalancedChen.Part5OriginalH430ActualRootStageReceipts
