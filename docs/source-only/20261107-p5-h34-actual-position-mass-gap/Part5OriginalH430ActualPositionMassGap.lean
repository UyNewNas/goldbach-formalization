import ImbalancedChen.Part5OriginalH430TruePositionReceiptLedger
import ImbalancedChen.Part5OriginalH430ActualSecondRosserRetention
import ImbalancedChen.FirstExitFrontierInvariants

/-!
P5.6 / h34: exact rank-two LIST-position history mass versus the
ORIGINAL U3/U4 (tag,p,q) arithmetic source. A physical (Q,p,ell)
slot consumes at most one selected Fin position for that Q. At the
chosen index we now recover the literal recursion's sign and mass,
rather than merely its selected prefix.

The complete original source is carried through all six explicit
UNPAID lanes (cross-tag slot collision, extra q, failed second
Rosser, no eligible second prime, root cutoff, root policy).
The new seventh signed gap is the difference between the ORIGINAL
q/tag-dependent representative weight and the actual rank-two state
mass at the indexed position. It is not set to zero and is not
claimed to have a favorable sign.

A retained rank-two state is NOT a first-excluded signed Euler event:
the Euler suffix, actual full/selected/inherited owner, stage, seed,
root weights, and count-to-history inequality remain OPEN.
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430ActualPositionMassGap

noncomputable section
open scoped Classical BigOperators

open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430ActualSecondRosserRetention
open Part5OriginalH430TaggedRankTwoFibreCapacity
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430TruePositionReceiptLedger

/-- Recover the REAL selected rank-two state's parity and product
mass at the chosen finite LIST index of an observed physical slot.
The second coordinate is an actual prime ell dividing the original
integer quotient; it is not the quotient q itself. -/
theorem observed_fixed_q_position_true_sign_mass
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (s : SlotAtQ N cap precision tau z0 lower Q) :
    (actualPhysicalRankTwoList N cap z0 Q lower)[
      fixedQSlotPositionMap N cap precision tau z0 lower Q s].positive = true ∧
    (actualPhysicalRankTwoList N cap z0 Q lower)[
      fixedQSlotPositionMap N cap precision tau z0 lower Q s].mass =
      (1 / ((s.1.2.2 : ℝ) - 1)) * (1 / ((s.1.2.1 : ℝ) - 1)) := by
  let i := fixedQSlotPositionMap N cap precision tau z0 lower Q s
  let d := (actualPhysicalRankTwoList N cap z0 Q lower)[i]
  have hd : d ∈ actualPhysicalRankTwoList N cap z0 Q lower := by
    exact List.getElem_mem
  have hfront : d ∈ firstExitDepthFrontier 2
      (ordinaryRosserRetainedPolicy lower Q)
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0) := by
    simpa only [actualPhysicalRankTwoList] using hd
  have hp : d.selectedPrefix = [s.1.2.2, s.1.2.1] :=
    fixed_q_slot_position_prefix
      N cap precision tau z0 lower Q s.1 s.2
  have hsign := mem_firstExitDepthFrontier_positive_eq_evenListLength
    2 (ordinaryRosserRetainedPolicy lower Q)
    (fun r : ℕ => 1 / ((r : ℝ) - 1))
    (roughPrimeUniverse N cap 0 z0) d hfront
  have hmass := mem_firstExitDepthFrontier_mass_eq_selected_prod
    2 (ordinaryRosserRetainedPolicy lower Q)
    (fun r : ℕ => 1 / ((r : ℝ) - 1))
    (roughPrimeUniverse N cap 0 z0) d hfront
  constructor
  · change d.positive = true
    rw [hsign, hp]
    rfl
  · change d.mass =
        (1 / ((s.1.2.2 : ℝ) - 1)) * (1 / ((s.1.2.1 : ℝ) - 1))
    rw [hmass, hp]
    simp

/-- Count the literal rank-two historical state mass ONCE per
observed actual Fin position, not once per q/tag receipt.
No unobserved frontier position is charged. -/
def observedRankTwoMassAtPosition
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) : ℝ :=
  ∑ s : SlotAtQ N cap precision tau z0 lower Q,
    if fixedQSlotPositionMap N cap precision tau z0 lower Q s = i
    then (actualPhysicalRankTwoList N cap z0 Q lower)[i].mass else 0

/-- Reindex a TRUE list position mass to the actual distinct
physical (p,ell) slots for this one Q. It is not a source q-count
identity, Euler-suffix payment, or owner after selected filtering. -/
theorem observed_rank_two_mass_by_distinct_slots
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ) :
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      observedRankTwoMassAtPosition N cap precision tau z0 lower Q i) =
      ∑ s : SlotAtQ N cap precision tau z0 lower Q,
        (1 / ((s.1.2.2 : ℝ) - 1)) *
        (1 / ((s.1.2.1 : ℝ) - 1)) := by
  classical
  simp only [observedRankTwoMassAtPosition]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hmass := (observed_fixed_q_position_true_sign_mass
    N cap precision tau z0 lower Q s).2
  simpa using hmass

/-- Exact signed gap between the original q/tag representative
arithmetic weight and the literal rank-two HISTORY MASS of its
chosen index. The gap has no assumed sign or bound. -/
def originalRankTwoPositionMassGap
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) : ℝ :=
  originalWeightAtActualPosition N cap precision tau z0 lower w Q i -
    observedRankTwoMassAtPosition N cap precision tau z0 lower Q i

/-- All six rejected or collision terms, as the ORIGINAL signed
q-dependent source weights. They are not discarded or paid. -/
def originalSixUnpaidReceiptLanes
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) : ℝ :=
  (∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
    ∑ key ∈
      (physicalSlotTaggedFibre N cap precision tau z0 lower slot).erase
        (physicalSlotRepresentative N cap precision tau z0 lower slot),
      w (keyRepresentative N cap precision tau z0 lower key)) +
  (∑ key ∈ observedRankTwoKeys N cap precision tau z0 lower,
    ∑ z ∈
      (keyReceiptFibre N cap precision tau z0 lower key).erase
        (keyRepresentative N cap precision tau z0 lower key),
      w z) +
  (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
    if hasPostRootPrimeFactor z ∧
        ¬ hasRetainedOriginalSecond N cap precision tau z0 lower z
    then w z else 0) +
  (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
    if ¬ hasPostRootPrimeFactor z then w z else 0) +
  (∑ z ∈ rootCutoffBlocked (originalTagged N) z0, w z) +
  (∑ z ∈ physicalPolicyBlocked N precision tau z0 lower, w z)

/-- The COMPLETE original U3/U4 source now reaches actual bounded
rank-two LIST indices at every genuine physical Q. All six surplus/
rejection lanes remain explicitly in the exact signed formula.
This is source bookkeeping, not h34 count-to-history payment. -/
theorem complete_original_source_at_actual_positions
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ originalTagged N, w z) =
      (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          originalWeightAtActualPosition
            N cap precision tau z0 lower w Q i) +
      originalSixUnpaidReceiptLanes N cap precision tau z0 lower w := by
  have h := original_count_source_five_unpaid_lanes
    N cap precision tau z0 lower hzcap w
  have hfirst :
      (∑ z ∈ (originalTagged N).filter
        (selectedOriginalRootStage N cap precision tau z0 lower),
        if hasRetainedOriginalSecond N cap precision tau z0 lower z
        then w z else 0) =
      (∑ z ∈ retainedReceipts N cap precision tau z0 lower, w z) := by
    simp only [retainedReceipts, Finset.sum_filter]
  rw [hfirst,
    retained_receipts_actual_position_signed_ledger
      N cap precision tau z0 lower w] at h
  unfold originalSixUnpaidReceiptLanes
  convert h using 1 <;> ring

/-- For each true Q, arithmetic position weight is EXACTLY the
observed historical state mass plus a signed UNPAID mismatch.
This is never used to infer a favorable payment inequality. -/
theorem per_q_original_receipt_vs_history_mass
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ) :
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      originalWeightAtActualPosition N cap precision tau z0 lower w Q i) =
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      observedRankTwoMassAtPosition N cap precision tau z0 lower Q i) +
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      originalRankTwoPositionMassGap
        N cap precision tau z0 lower w Q i) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold originalRankTwoPositionMassGap
  ring

/-- The COMPLETE original signed arithmetic source splits into:
(1) REAL positive rank-two history masses on observed Fin indices,
(2) the exact signed arithmetic-minus-history mismatch at those
indices, (3) every still-UNPAID original source collision/rejection
lane. An even retained history is NOT a signed first-excluded event.
This equality is NOT the h34 count-to-history inequality. -/
theorem complete_original_source_true_mass_and_all_debts
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ originalTagged N, w z) =
      (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          observedRankTwoMassAtPosition
            N cap precision tau z0 lower Q i) +
      (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          originalRankTwoPositionMassGap
            N cap precision tau z0 lower w Q i) +
      originalSixUnpaidReceiptLanes N cap precision tau z0 lower w := by
  have hsource := complete_original_source_at_actual_positions
    N cap precision tau z0 lower hzcap w
  have hsum :
      (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          originalWeightAtActualPosition
            N cap precision tau z0 lower w Q i) =
      (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          observedRankTwoMassAtPosition
            N cap precision tau z0 lower Q i) +
      (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          originalRankTwoPositionMassGap
            N cap precision tau z0 lower w Q i) := by
    calc
      _ = ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
          ((∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
            observedRankTwoMassAtPosition N cap precision tau z0 lower Q i) +
           (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
            originalRankTwoPositionMassGap
              N cap precision tau z0 lower w Q i)) := by
            apply Finset.sum_congr rfl
            intro Q hQ
            exact per_q_original_receipt_vs_history_mass
              N cap precision tau z0 lower w Q
      _ = _ := Finset.sum_add_distrib
  rw [hsum] at hsource
  convert hsource using 1 <;> ring

end
end ImbalancedChen.Part5OriginalH430ActualPositionMassGap
