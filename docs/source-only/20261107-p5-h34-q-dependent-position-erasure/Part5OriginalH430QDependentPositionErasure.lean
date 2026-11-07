import ImbalancedChen.Part5OriginalH430ActualPositionMassGap
import ImbalancedChen.Part5OriginalH430FixedQPositionFilterLedger

/-!
P5.6 / h34: exact ORIGINAL U3/U4 arithmetic-source accounting under a
Q-DEPENDENT Boolean test of the REAL rank-two frontier LIST positions.

This packet does NOT assume that the supplied test equals the manuscript's
full/selected/inherited owner gate: that binding is an outstanding INTERNAL
proof. It does prove a useful non-loss statement before that binding:
every deleted historical position contributes its ORIGINAL q/tag
arithmetic source weight to an explicit unpaid term. The kept part
retains the mismatch between that arithmetic weight and the actual
recursive history mass. Different physical Q values have separate
lists and may have different tests.

All claims below are exact signed finite identities, not directional
payment estimates. An actual positive rank-two history is NOT the
first-excluded signed Euler event with its remaining Euler product.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430QDependentPositionErasure

noncomputable section
open scoped Classical BigOperators

open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430ActualPositionMassGap

/-- Actual finite LIST indices not passing the requested post-frontier
test at this specific physical Q. Positions, not state values, are
counted; duplicate states at different indices are not conflated. -/
def erasedActualPositions (N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (keep : FirstExitDepthState ℕ → Bool) :
    Finset (Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :=
  Finset.univ.filter (fun i =>
    keep ((actualPhysicalRankTwoList N cap z0 Q lower)[i]) = false)

theorem actual_position_filter_partition (N cap : ℕ)
    (z0 Q : ℝ) (lower : Bool)
    (keep : FirstExitDepthState ℕ → Bool) :
    keptPositions N cap z0 Q lower keep ∪
      erasedActualPositions N cap z0 Q lower keep = Finset.univ := by
  classical
  ext i
  simp only [Finset.mem_union, keptPositions, erasedActualPositions,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases h : keep ((actualPhysicalRankTwoList N cap z0 Q lower)[i]) <;>
    simp [h]

theorem actual_position_filter_disjoint (N cap : ℕ)
    (z0 Q : ℝ) (lower : Bool)
    (keep : FirstExitDepthState ℕ → Bool) :
    Disjoint (keptPositions N cap z0 Q lower keep)
      (erasedActualPositions N cap z0 Q lower keep) := by
  apply Finset.disjoint_left.mpr
  intro i hi hn
  have hyes := (Finset.mem_filter.mp hi).2
  have hno := (Finset.mem_filter.mp hn).2
  rw [hyes] at hno
  cases hno

/-- Every TRUE list occurrence belongs to exactly one side of this
finite position test. This does not quotient list occurrences. -/
theorem actual_position_signed_partition (N cap : ℕ)
    (z0 Q : ℝ) (lower : Bool)
    (keep : FirstExitDepthState ℕ → Bool)
    (v : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length → ℝ) :
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length, v i) =
      (∑ i ∈ keptPositions N cap z0 Q lower keep, v i) +
      (∑ i ∈ erasedActualPositions N cap z0 Q lower keep, v i) := by
  classical
  calc
    _ = ∑ i ∈ keptPositions N cap z0 Q lower keep ∪
        erasedActualPositions N cap z0 Q lower keep, v i := by
          rw [actual_position_filter_partition]
    _ = _ := Finset.sum_union
      (actual_position_filter_disjoint N cap z0 Q lower keep)

/-- At surviving actual positions the ORIGINAL representative
arithmetic weight equals true historical mass plus the exact signed
mismatch. No sign condition on the mismatch is used. -/
theorem kept_position_original_weight_mass_gap
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ)
    (keep : FirstExitDepthState ℕ → Bool) :
    (∑ i ∈ keptPositions N cap z0 Q lower keep,
      originalWeightAtActualPosition
        N cap precision tau z0 lower w Q i) =
      (∑ i ∈ keptPositions N cap z0 Q lower keep,
        observedRankTwoMassAtPosition
          N cap precision tau z0 lower Q i) +
      (∑ i ∈ keptPositions N cap z0 Q lower keep,
        originalRankTwoPositionMassGap
          N cap precision tau z0 lower w Q i) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold originalRankTwoPositionMassGap
  ring

/-- Exact one-Q position accounting: all arithmetic weights rejected
by the post-frontier test remain UNPAID, even if the tested state's
ordinary Rosser prefix passed at the earlier selection stage. -/
theorem fixed_q_original_weight_kept_mass_plus_unpaid
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ)
    (keep : FirstExitDepthState ℕ → Bool) :
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      originalWeightAtActualPosition
        N cap precision tau z0 lower w Q i) =
      ((∑ i ∈ keptPositions N cap z0 Q lower keep,
          observedRankTwoMassAtPosition
            N cap precision tau z0 lower Q i) +
        (∑ i ∈ keptPositions N cap z0 Q lower keep,
          originalRankTwoPositionMassGap
            N cap precision tau z0 lower w Q i)) +
      (∑ i ∈ erasedActualPositions N cap z0 Q lower keep,
        originalWeightAtActualPosition
          N cap precision tau z0 lower w Q i) := by
  rw [actual_position_signed_partition N cap z0 Q lower keep
    (originalWeightAtActualPosition N cap precision tau z0 lower w Q)]
  rw [kept_position_original_weight_mass_gap
    N cap precision tau z0 lower w Q keep]

/-- Actual kept historical masses, summed ONLY at observed source
positions and separately for each ORIGINAL physical Q. The stage
test may depend on Q, as it must for genuine policy matching. -/
def keptOriginalRankTwoMass
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    ∑ i ∈ keptPositions N cap z0 Q lower (keep Q),
      observedRankTwoMassAtPosition N cap precision tau z0 lower Q i

/-- Arithmetic-minus-history signed gap at exactly the retained
actual physical-Q positions; no favorable sign is assumed. -/
def keptOriginalRankTwoGap
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    ∑ i ∈ keptPositions N cap z0 Q lower (keep Q),
      originalRankTwoPositionMassGap
        N cap precision tau z0 lower w Q i

/-- Every erased observed position is carried with its full
original tag/q representative weight, not its frontier mass. -/
def erasedOriginalPositionArithmetic
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    ∑ i ∈ erasedActualPositions N cap z0 Q lower (keep Q),
      originalWeightAtActualPosition
        N cap precision tau z0 lower w Q i

/-- The FULL literal original tagged U3/U4 q-source, including every
original q occurrence, is the retained actual rank-two historical
mass, its still-unpaid arithmetic/history gap, the deleted-source
weights, and the PREVIOUS SIX explicit q/tag/rejection lanes.

This result does NOT identify keep with manuscript full/selected/
inherited predicates. It also gives no inequality paying the seven
unpaid components and no signed first-excluded Euler correction. -/
theorem complete_original_source_with_q_dependent_erasure
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (w : TaggedReceiver → ℝ)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    (∑ z ∈ originalTagged N, w z) =
      (keptOriginalRankTwoMass N cap precision tau z0 lower keep +
       keptOriginalRankTwoGap N cap precision tau z0 lower w keep) +
      erasedOriginalPositionArithmetic
        N cap precision tau z0 lower w keep +
      originalSixUnpaidReceiptLanes
        N cap precision tau z0 lower w := by
  have hsource := complete_original_source_at_actual_positions
    N cap precision tau z0 lower hzcap w
  have hsplit :
      (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          originalWeightAtActualPosition
            N cap precision tau z0 lower w Q i) =
        (keptOriginalRankTwoMass N cap precision tau z0 lower keep +
         keptOriginalRankTwoGap N cap precision tau z0 lower w keep) +
        erasedOriginalPositionArithmetic
          N cap precision tau z0 lower w keep := by
    calc
      _ = ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
            (((∑ i ∈ keptPositions N cap z0 Q lower (keep Q),
                observedRankTwoMassAtPosition
                  N cap precision tau z0 lower Q i) +
              (∑ i ∈ keptPositions N cap z0 Q lower (keep Q),
                originalRankTwoPositionMassGap
                  N cap precision tau z0 lower w Q i)) +
             (∑ i ∈ erasedActualPositions N cap z0 Q lower (keep Q),
               originalWeightAtActualPosition
                 N cap precision tau z0 lower w Q i)) := by
            apply Finset.sum_congr rfl
            intro Q hQ
            exact fixed_q_original_weight_kept_mass_plus_unpaid
              N cap precision tau z0 lower w Q (keep Q)
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        rfl
  rw [hsplit] at hsource
  exact hsource

end
end ImbalancedChen.Part5OriginalH430QDependentPositionErasure
