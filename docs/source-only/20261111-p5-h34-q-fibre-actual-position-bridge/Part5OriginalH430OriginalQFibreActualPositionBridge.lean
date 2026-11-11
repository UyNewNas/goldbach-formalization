import ImbalancedChen.Part5OriginalH430OriginalQFibrePhysicalDebt
import ImbalancedChen.Part5OriginalH430QDependentPositionErasure

/-!
P5.6 / h34 — put the q-fibre-multiplied ACTUAL physical CLOSED-CELL
gap onto the previously constructed genuine rank-two Fin positions.

The original (tag,p,q) receipt is counted independently, whereas
one observed physical (Q,p,ell) slot gets only one position in its
own Q-frontier.  The difference is NOT set to zero: the exact
position-weight-minus-history-mass mismatch and all six original
collision/rejection lanes remain visible.

At the genuine ordinary complete-prefix Rosser gate, the weight
of ERADICATED observed slots is exactly zero.  This is a real
filter fact, not full/selected/inherited filter compatibility.
No sign, smallness, owner, root 7/2 or count-to-history payment
is assumed for the remaining mismatch or six lanes.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430OriginalQFibreActualPositionBridge

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalPrimeBandPhysicalGap
open Part5OriginalH430OriginalQFibrePhysicalDebt
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430ActualPositionMassGap
open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430QDependentPositionErasure

/-- The literal physical gap for each original (tag,p,q) receipt,
with its own U3/U4 physical Q and generation.  It is independent of
q within a fibre but the receipt is NOT dropped or identified. -/
def taggedPhysicalGapWeight (N n : ℕ) (tau : ℝ)
    (depth : Root → ℕ → Fin 430) : TaggedReceiver → ℝ
  | .inl v => actualRootPhysicalClosedCellGap
      N n .U3 tau v.1 (depth .U3 v.1)
  | .inr v => actualRootPhysicalClosedCellGap
      N n .U4 tau v.1 (depth .U4 v.1)

/-- The previously established q-fibre multiple is EXACTLY a sum
over the original tagged q arithmetic source, not over p alone. -/
theorem original_q_fibre_gap_eq_tagged_actual_weight
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430) :
    originalQFibrePhysicalGap N n tau depth =
      ∑ z ∈ originalTagged N,
        taggedPhysicalGapWeight N n tau depth z := by
  rw [← original_q_fibre_physical_gap_is_tagged]
  rfl

/-- For the ACTUAL ordinary complete-prefix Rosser test, no
observed original arithmetic representative weight is erased.
Unobserved indices may fail the gate but carry zero source weight.
This is NOT the manuscript's full/selected/inherited test. -/
theorem actual_full_prefix_erases_no_observed_arithmetic
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    erasedOriginalPositionArithmetic
      N cap precision tau z0 lower w
      (fun Q => actualFullPrefixGate lower Q) = 0 := by
  classical
  unfold erasedOriginalPositionArithmetic
  apply Finset.sum_eq_zero
  intro Q hQ
  have hpartition := actual_position_signed_partition
    N cap z0 Q lower (actualFullPrefixGate lower Q)
      (originalWeightAtActualPosition
        N cap precision tau z0 lower w Q)
  have hall := actual_position_rep_weight_sum
    N cap precision tau z0 lower w Q
  have hkept := actual_prefix_keeps_position_rep_weights
    N cap precision tau z0 lower w Q
  linarith only [hpartition, hall, hkept]

/-- The REAL q-fibre physical gap reaches actual bounded rank-two
LIST positions, each at its own observed physical Q.  All erased
position weights and all six original receipt lanes are retained.
The positional gap measures the arithmetic-vs-history mismatch
rather than replacing actual q multiplicity with a state mark. -/
theorem original_q_fibre_gap_at_actual_positions
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (depth : Root → ℕ → Fin 430)
    (hzcap : z0 ≤ (cap : ℝ))
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    originalQFibrePhysicalGap N n tau depth =
      (keptOriginalRankTwoMass N cap precision tau z0 lower keep +
        keptOriginalRankTwoGap N cap precision tau z0 lower
          (taggedPhysicalGapWeight N n tau depth) keep) +
      erasedOriginalPositionArithmetic N cap precision tau z0 lower
        (taggedPhysicalGapWeight N n tau depth) keep +
      originalSixUnpaidReceiptLanes N cap precision tau z0 lower
        (taggedPhysicalGapWeight N n tau depth) := by
  rw [original_q_fibre_gap_eq_tagged_actual_weight]
  exact complete_original_source_with_q_dependent_erasure
    N cap precision tau z0 lower hzcap
      (taggedPhysicalGapWeight N n tau depth) keep

/-- At the actual complete-prefix gate the erased-position source
is PROVED zero, leaving the genuine historical mass, the unpaid
positional arithmetic/history mismatch, and the six unpaid lanes.
This does not identify the original full/selected/inherited filters. -/
theorem original_q_fibre_gap_at_actual_full_prefix
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (depth : Root → ℕ → Fin 430)
    (hzcap : z0 ≤ (cap : ℝ)) :
    originalQFibrePhysicalGap N n tau depth =
      (keptOriginalRankTwoMass N cap precision tau z0 lower
          (fun Q => actualFullPrefixGate lower Q) +
        keptOriginalRankTwoGap N cap precision tau z0 lower
          (taggedPhysicalGapWeight N n tau depth)
          (fun Q => actualFullPrefixGate lower Q)) +
      originalSixUnpaidReceiptLanes N cap precision tau z0 lower
        (taggedPhysicalGapWeight N n tau depth) := by
  have h := original_q_fibre_gap_at_actual_positions
    N n cap precision tau z0 lower depth hzcap
    (fun Q => actualFullPrefixGate lower Q)
  rw [actual_full_prefix_erases_no_observed_arithmetic
    N cap precision tau z0 lower
      (taggedPhysicalGapWeight N n tau depth)] at h
  simpa only [add_zero] using h

/-- A real upper bound on the SUM of all actual-position terms,
including the still-unpaid mismatch and all six rejection lanes.
The prior q-multiplied source and selected-row debts remain on
the right and have NOT been established as small or paid. -/
theorem original_q_fibre_actual_full_prefix_abs_bound
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (depth : Root → ℕ → Fin 430)
    (hzcap : z0 ≤ (cap : ℝ)) :
    |(keptOriginalRankTwoMass N cap precision tau z0 lower
          (fun Q => actualFullPrefixGate lower Q) +
        keptOriginalRankTwoGap N cap precision tau z0 lower
          (taggedPhysicalGapWeight N n tau depth)
          (fun Q => actualFullPrefixGate lower Q)) +
      originalSixUnpaidReceiptLanes N cap precision tau z0 lower
        (taggedPhysicalGapWeight N n tau depth)| ≤
      originalQFibrePhysicalSourceDebt N n tau depth +
        originalQFibreSelectedRowError N n tau depth := by
  have hbound := original_q_fibre_physical_gap_abs_bound
    N n tau depth
  rw [original_q_fibre_gap_at_actual_full_prefix
    N n cap precision tau z0 lower depth hzcap] at hbound
  exact hbound

end
end ImbalancedChen.Part5OriginalH430OriginalQFibreActualPositionBridge
