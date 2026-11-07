import ImbalancedChen.Part5OriginalH430QDependentPositionErasure
import ImbalancedChen.Part5OriginalH430OriginalSelectedRootFibres

/-!
P5.6 / h34: a necessary PHYSICAL presieve condition for matching
the ORIGINAL U3/U4 quotient receipts to actual rank-two list positions.

An original selected p is at least N^a, whereas the real history
requires strict p < z0. Thus z0 <= N^a prevents original receipt
admission at the root, even before any post-root selection.
The proof propagates this obstruction through the tagged-q, rank-two
key, physical-Q slot and q-dependent position accounting. It neither
asserts the manuscript's z0 relation nor replaces the outstanding
full/selected/inherited gates and genuine signed Euler owner.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430SmallPresieveReceiptObstruction

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430OriginalSelectedRootFibres
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430TaggedRankTwoFibreCapacity
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430ActualPositionMassGap
open Part5OriginalH430QDependentPositionErasure

/-- The actual physical-Q root source is empty when its strict
first-selection cutoff is no larger than original roughness N^a. -/
theorem physical_accepted_empty_of_small
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hsmall : z0 ≤ (N : ℝ) ^ a) :
    physicalRootAccepted N precision tau z0 lower = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro z hz
  obtain ⟨hsource, hlicensed⟩ := Finset.mem_filter.mp hz
  have hcut : z ∈ rootCutoffBlocked (originalTagged N) z0 := by
    rw [original_selected_all_cutoff_if_small N z0 hsmall]
    exact hsource
  have hnot : ¬ (arithmeticPrime z : ℝ) < z0 :=
    (Finset.mem_filter.mp hcut).2
  have hroot := (selected_root_licensed_iff
    N z0 (originalPhysicalQ N precision tau z) lower hsource).mp hlicensed
  exact hnot hroot.1

/-- Literal historical root candidates, not abstract root marks. -/
theorem original_stage_empty_of_small
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (hsmall : z0 ≤ (N : ℝ) ^ a) :
    (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower) = ∅ := by
  calc
    _ = physicalRootAccepted N precision tau z0 lower :=
      (physical_accepted_eq_actual_stage
        N cap precision tau z0 lower hzcap).symm
    _ = ∅ := physical_accepted_empty_of_small
      N precision tau z0 lower hsmall

/-- All original q/tag receipts requiring a retained second
historical prime are absent at this strict cutoff. -/
theorem retained_receipts_empty_of_small
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (hsmall : z0 ≤ (N : ℝ) ^ a) :
    retainedReceipts N cap precision tau z0 lower = ∅ := by
  simp [retainedReceipts,
    original_stage_empty_of_small N cap precision tau z0 lower hzcap hsmall]

theorem observed_rank_two_keys_empty_of_small
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (hsmall : z0 ≤ (N : ℝ) ^ a) :
    observedRankTwoKeys N cap precision tau z0 lower = ∅ := by
  simp [observedRankTwoKeys,
    retained_receipts_empty_of_small N cap precision tau z0 lower hzcap hsmall]

/-- This says observed original slots vanish, NOT the entire history
frontier at Q: other unrelated positions may still be present. -/
theorem observed_physical_slots_empty_of_small
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (hsmall : z0 ≤ (N : ℝ) ^ a) :
    observedPhysicalSlots N cap precision tau z0 lower = ∅ := by
  simp [observedPhysicalSlots,
    observed_rank_two_keys_empty_of_small
      N cap precision tau z0 lower hzcap hsmall]

theorem observed_receipt_Qs_empty_of_small
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (hsmall : z0 ≤ (N : ℝ) ^ a) :
    observedReceiptQs N cap precision tau z0 lower = ∅ := by
  simp [observedReceiptQs,
    observed_physical_slots_empty_of_small
      N cap precision tau z0 lower hzcap hsmall]

/-- Arbitrary later position filtering cannot create ORIGINAL
q-receipt mass when the observed physical-Q source is empty. -/
theorem kept_mass_zero_of_small
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (hsmall : z0 ≤ (N : ℝ) ^ a)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    keptOriginalRankTwoMass N cap precision tau z0 lower keep = 0 := by
  simp [keptOriginalRankTwoMass,
    observed_receipt_Qs_empty_of_small
      N cap precision tau z0 lower hzcap hsmall]

theorem kept_gap_zero_of_small
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (hsmall : z0 ≤ (N : ℝ) ^ a)
    (w : TaggedReceiver → ℝ)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    keptOriginalRankTwoGap N cap precision tau z0 lower w keep = 0 := by
  simp [keptOriginalRankTwoGap,
    observed_receipt_Qs_empty_of_small
      N cap precision tau z0 lower hzcap hsmall]

theorem erased_arithmetic_zero_of_small
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (hsmall : z0 ≤ (N : ℝ) ^ a)
    (w : TaggedReceiver → ℝ)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    erasedOriginalPositionArithmetic
      N cap precision tau z0 lower w keep = 0 := by
  simp [erasedOriginalPositionArithmetic,
    observed_receipt_Qs_empty_of_small
      N cap precision tau z0 lower hzcap hsmall]

/-- All ORIGINAL tagged U3/U4 q weights remain in six unpaid lanes;
this is an exact signed identity and not a payment inequality. -/
theorem complete_original_source_unpaid_of_small
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (hsmall : z0 ≤ (N : ℝ) ^ a)
    (w : TaggedReceiver → ℝ)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    (∑ z ∈ originalTagged N, w z) =
      originalSixUnpaidReceiptLanes
        N cap precision tau z0 lower w := by
  have h := complete_original_source_with_q_dependent_erasure
    N cap precision tau z0 lower hzcap w keep
  simpa [keptOriginalRankTwoMass, keptOriginalRankTwoGap,
    erasedOriginalPositionArithmetic,
    observed_receipt_Qs_empty_of_small
      N cap precision tau z0 lower hzcap hsmall] using h

/-- The complete six-lane source specializes to precisely the ORIGINAL
cutoff lane. Neither q nor overlapping U3/U4 labels are discarded. -/
theorem six_unpaid_lanes_eq_cutoff_of_small
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (hsmall : z0 ≤ (N : ℝ) ^ a)
    (w : TaggedReceiver → ℝ)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    originalSixUnpaidReceiptLanes N cap precision tau z0 lower w =
      ∑ z ∈ rootCutoffBlocked (originalTagged N) z0, w z := by
  calc
    _ = ∑ z ∈ originalTagged N, w z :=
      (complete_original_source_unpaid_of_small
        N cap precision tau z0 lower hzcap hsmall w keep).symm
    _ = ∑ z ∈ rootCutoffBlocked (originalTagged N) z0, w z := by
      rw [original_selected_all_cutoff_if_small N z0 hsmall]

/-- Literal original U3+U4 count is not a retained historical mass
in the small-presieve regime; all its q/tag appearances stay unpaid. -/
theorem original_U34_count_unpaid_of_small
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (hsmall : z0 ≤ (N : ℝ) ^ a)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    currentChenUpsilon3 N + currentChenUpsilon4 N =
      originalSixUnpaidReceiptLanes
        N cap precision tau z0 lower (fun _ => (1 : ℝ)) := by
  calc
    _ = ((originalTagged N).card : ℝ) :=
      original_U34_eq_tagged_card N
    _ = ∑ z ∈ originalTagged N, (1 : ℝ) := by simp
    _ = _ := complete_original_source_unpaid_of_small
      N cap precision tau z0 lower hzcap hsmall (fun _ => 1) keep

end
end ImbalancedChen.Part5OriginalH430SmallPresieveReceiptObstruction
