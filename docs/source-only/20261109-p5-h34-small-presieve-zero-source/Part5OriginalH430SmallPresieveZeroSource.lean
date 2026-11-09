import ImbalancedChen.Part5OriginalH430U4PostfilterExactCapacity
import ImbalancedChen.Part5OriginalH430QDependentPositionErasure

/-!
P5.6 / h34: the ACTUAL low-presieve zero-source branch.

For z0 <= N^a, the original U3/U4 q/tag receiver roots begin at N^a
and cannot enter the true strict root carrier.  This file transports
the already proved real root-stage obstruction through the genuine
rank-two q/tag-to-prime-factor selection, physical slots, Q fibres,
and the signed complete original-source ledger.  It is a case of
ZERO historical source, not a proof of H430 payment.

In particular all original U3/U4 q/tag receipts must remain in the
literal six unpaid lanes; filtering a non-existent observed history
cannot pay any of them.  This is for arbitrary signed q/tag weights
and for any Q-dependent post-frontier position mask.  It does NOT
assert that the manuscript's chosen presieve falls in this regime.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430SmallPresieveZeroSource

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalSelectedRootFibres
open Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430TaggedRankTwoFibreCapacity
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430QDependentPositionErasure

/-- No ACTUAL stage-zero candidate can originate from the original
U3/U4 q/tag source when its strict presieve cap is <= N^a.
The physical Q may depend on the original tag and root p. -/
theorem small_presieve_original_stage_empty
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (hsmall : z0 ≤ (N : ℝ) ^ a) :
    (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro z hz
  obtain ⟨horig, hstage⟩ := Finset.mem_filter.mp hz
  have hlarge : (N : ℝ) ^ a < z0 :=
    actual_original_stage_requires_large_presieve
      N cap precision tau z0 lower hzcap horig hstage
  exact (not_lt_of_ge hsmall) hlarge

/-- The chosen true second factor is only available AFTER an admitted
original root.  The full retained original q/tag receiver set is empty
in this regime: a quotient cannot bypass the rejected root. -/
theorem small_presieve_retained_receipts_empty
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (hsmall : z0 ≤ (N : ℝ) ^ a) :
    retainedReceipts N cap precision tau z0 lower = ∅ := by
  classical
  unfold retainedReceipts
  rw [small_presieve_original_stage_empty
    N cap precision tau z0 lower hzcap hsmall]
  simp

/-- The actual original tagged (p,ell) keys vanish; their absence
is not an assumption identifying the arithmetic quotient q with ell. -/
theorem small_presieve_observed_keys_empty
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (hsmall : z0 ≤ (N : ℝ) ^ a) :
    observedRankTwoKeys N cap precision tau z0 lower = ∅ := by
  simp [observedRankTwoKeys,
    small_presieve_retained_receipts_empty
      N cap precision tau z0 lower hzcap hsmall]

/-- No observed fixed-physical-Q/p/ell slot survives the original
q/tag source when the actual root cutoff is too small. -/
theorem small_presieve_observed_slots_empty
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (hsmall : z0 ≤ (N : ℝ) ^ a) :
    observedPhysicalSlots N cap precision tau z0 lower = ∅ := by
  simp [observedPhysicalSlots,
    small_presieve_observed_keys_empty
      N cap precision tau z0 lower hzcap hsmall]

/-- The PHYSICAL-Q source index is empty, rather than an arbitrary
shared Q imposed on two original U3/U4 tags. -/
theorem small_presieve_observed_Qs_empty
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (hsmall : z0 ≤ (N : ℝ) ^ a) :
    observedReceiptQs N cap precision tau z0 lower = ∅ := by
  simp [observedReceiptQs,
    small_presieve_observed_slots_empty
      N cap precision tau z0 lower hzcap hsmall]

/-- This is the useful ALL-SOURCE conclusion: for every original
signed q/tag weight and every possibly Q-dependent postfilter, all
original arithmetic receipts remain in the ACTUAL six unpaid lanes.
The kept rank-two history mass, its arithmetic/history mismatch and
deleted original-position source vanish because there is no actual
original-source position at any Q.  It is NOT a zero-source statement
for the entire unrestricted history, nor an upper H430 estimate. -/
theorem small_presieve_complete_original_source_is_unpaid
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (hsmall : z0 ≤ (N : ℝ) ^ a)
    (w : TaggedReceiver → ℝ)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    originalSixUnpaidReceiptLanes
      N cap precision tau z0 lower w =
      ∑ z ∈ originalTagged N, w z := by
  have hsource :=
    complete_original_source_with_q_dependent_erasure
      N cap precision tau z0 lower hzcap w keep
  have hQ : observedReceiptQs N cap precision tau z0 lower = ∅ :=
    small_presieve_observed_Qs_empty
      N cap precision tau z0 lower hzcap hsmall
  simp [keptOriginalRankTwoMass, keptOriginalRankTwoGap,
    erasedOriginalPositionArithmetic, hQ] at hsource
  exact hsource.symm

/-- In particular even a proposed postfilter cannot obtain an
original arithmetic receipt in the actual rank-two source when no
original root was admitted.  The original U3 and U4 count remains
with both arithmetic labels in the literal root-cutoff account. -/
theorem small_presieve_original_count_at_root_cutoff
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (hsmall : z0 ≤ (N : ℝ) ^ a) :
    (retainedReceipts N cap precision tau z0 lower).card = 0 ∧
    currentChenUpsilon3 N + currentChenUpsilon4 N =
      ((rootCutoffBlocked (originalTagged N) z0).card : ℝ) := by
  constructor
  · rw [small_presieve_retained_receipts_empty
      N cap precision tau z0 lower hzcap hsmall]
    rfl
  · exact (original_selected_count_cutoff_if_small
      N z0 hsmall).symm

end
end ImbalancedChen.Part5OriginalH430SmallPresieveZeroSource
