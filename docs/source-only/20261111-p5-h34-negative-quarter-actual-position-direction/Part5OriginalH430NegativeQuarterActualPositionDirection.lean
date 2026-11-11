import ImbalancedChen.Part5OriginalH430UnitPositionMassDirection
import ImbalancedChen.Part5OriginalH430OriginalUpperOverlapCount

/-!
P5.6/h34 — the ACTUAL original negative Chen quarter at the genuine
rank-two physical Fin positions, with the correct inequality direction.

The preceding unit-weight calculation gave
  historical mass + six unpaid lanes <= Upsilon3 + Upsilon4.
That inequality MUST NOT be multiplied by -1/4 without reversing it.
The original negative quarter is -(Upsilon3+Upsilon4)/4, with BOTH
U3 and U4 tags retained on the overlap.

Here the same actual source and actual observed position mass are
used, not an invented row norm, owner, zero-error hypothesis or an
additional external analytic input. The signed discrepancy has an
extra -5/4 times the observed mass. This makes the NEGATIVE-quarter
position discrepancy nonpositive; however the resulting count
inequality is an UPPER bound on the negative subtraction, not the
LOWER bound needed by the final Chen objective.

Full/selected/inherited ownership, six unpaid lanes, root 7/2,
Q80 closed-cell induction, signed Euler payment, PP/same-rho,
outer Theta/count and the common 430+11 refinement remain OPEN.

SOURCE_ONLY / CANDIDATE_UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430NegativeQuarterActualPositionDirection

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalUpperOverlapCount
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430ActualPositionMassGap
open Part5OriginalH430QDependentPositionErasure
open Part5OriginalH430OriginalQFibreActualPositionBridge
open Part5OriginalH430UnitPositionMassDirection

/-- The original Chen coefficient on EACH tagged U3 and U4
arithmetic receiver, including both tags at U4 overlap. -/
def originalNegativeQuarterReceipt (_ : TaggedReceiver) : ℝ :=
  -(1 / 4 : ℝ)

/-- This is the literal original upper-count negative quarter,
not a negative quarter of a deduplicated physical history list. -/
theorem original_negative_quarter_is_tagged_source (N : ℕ) :
    (∑ z ∈ originalTagged N, originalNegativeQuarterReceipt z) =
      originalU34SignedQuarter N := by
  rw [originalU34SignedQuarter, original_U34_eq_tagged_card]
  simp only [originalNegativeQuarterReceipt, Finset.sum_const,
    nsmul_eq_mul]
  ring

/-- At one ACTUAL observed fixed-Q Fin index the original negative
quarter scales the ARITHMETIC representative weight. It does not
scale the frontier state's historical mass. -/
theorem original_negative_quarter_position_arithmetic
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :
    originalWeightAtActualPosition
      N cap precision tau z0 lower originalNegativeQuarterReceipt Q i =
      -(1 / 4 : ℝ) *
        originalWeightAtActualPosition
          N cap precision tau z0 lower (fun _ => (1 : ℝ)) Q i := by
  classical
  unfold originalWeightAtActualPosition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h :
      fixedQSlotPositionMap N cap precision tau z0 lower Q s = i
  · simp [h, slotRepresentativeArithmeticWeight,
      originalNegativeQuarterReceipt]
  · simp [h]

/-- The signed quarter gap is NOT -1/4 times the unit gap.
The historical mass must also be paid by an additional -5/4. -/
theorem original_negative_quarter_position_gap_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :
    originalRankTwoPositionMassGap N cap precision tau z0 lower
        originalNegativeQuarterReceipt Q i =
      -(1 / 4 : ℝ) *
        originalRankTwoPositionMassGap N cap precision tau z0 lower
          (fun _ => (1 : ℝ)) Q i -
      (5 / 4 : ℝ) *
        observedRankTwoMassAtPosition
          N cap precision tau z0 lower Q i := by
  unfold originalRankTwoPositionMassGap
  rw [original_negative_quarter_position_arithmetic]
  ring

/-- Nonnegative ACTUAL rank-two history mass. This uses the true
observed source's two prime letters, not a hypothesis that arbitrary
states or selected-count owners have positive weights. -/
theorem original_observed_position_mass_nonneg
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :
    0 ≤ observedRankTwoMassAtPosition
      N cap precision tau z0 lower Q i := by
  classical
  unfold observedRankTwoMassAtPosition
  apply Finset.sum_nonneg
  intro s hs
  by_cases h :
      fixedQSlotPositionMap N cap precision tau z0 lower Q s = i
  · have hslot : s.1 ∈ observedPhysicalSlots N cap precision tau z0 lower :=
      (Finset.mem_filter.mp s.2).1
    have hpr := observed_original_physical_slot_primes
      N cap precision tau z0 lower s.1 hslot
    have hp : (0 : ℝ) ≤ (s.1.2.1 : ℝ) - 1 := by
      have hp2 : (2 : ℝ) ≤ (s.1.2.1 : ℝ) := by
        exact_mod_cast hpr.1.two_le
      linarith
    have he : (0 : ℝ) ≤ (s.1.2.2 : ℝ) - 1 := by
      have he2 : (2 : ℝ) ≤ (s.1.2.2 : ℝ) := by
        exact_mod_cast hpr.2.two_le
      linarith
    have hmass : 0 ≤
        (actualPhysicalRankTwoList N cap z0 Q lower)[
          fixedQSlotPositionMap N cap precision tau z0 lower Q s].mass := by
      rw [(observed_fixed_q_position_true_sign_mass
        N cap precision tau z0 lower Q s).2]
      exact mul_nonneg
        (div_nonneg (by norm_num) he)
        (div_nonneg (by norm_num) hp)
    simpa [h] using hmass
  · simp [h]

/-- The original negative-quarter arithmetic-minus-history gap
has the OPPOSITE useful direction from the unit-weight gap. -/
theorem original_negative_quarter_position_gap_upper
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :
    originalRankTwoPositionMassGap N cap precision tau z0 lower
        originalNegativeQuarterReceipt Q i ≤
      -(5 / 4 : ℝ) *
        observedRankTwoMassAtPosition
          N cap precision tau z0 lower Q i := by
  rw [original_negative_quarter_position_gap_exact]
  have hu := unit_original_position_mass_gap_nonneg
    N cap precision tau z0 lower Q i
  linarith

/-- At every genuine position the negative-quarter gap is <= 0.
No sign for the six collision/rejection lanes is inferred here. -/
theorem original_negative_quarter_position_gap_nonpos
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :
    originalRankTwoPositionMassGap N cap precision tau z0 lower
      originalNegativeQuarterReceipt Q i ≤ 0 := by
  have hg := original_negative_quarter_position_gap_upper
    N cap precision tau z0 lower Q i
  have hm := original_observed_position_mass_nonneg
    N cap precision tau z0 lower Q i
  linarith

/-- The genuine Q-dependent retained-position ledger preserves the
-5/4 mass charge. No full/selected/inherited filter equality is used. -/
theorem original_negative_quarter_kept_gap_upper
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    keptOriginalRankTwoGap N cap precision tau z0 lower
        originalNegativeQuarterReceipt keep ≤
      -(5 / 4 : ℝ) *
        keptOriginalRankTwoMass N cap precision tau z0 lower keep := by
  unfold keptOriginalRankTwoGap keptOriginalRankTwoMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Q hQ
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact original_negative_quarter_position_gap_upper
    N cap precision tau z0 lower Q i

/-- SPECIALIZE the already established full ORIGINAL q/tag receipt
ledger to the manuscript's literal negative-quarter coefficient.
The ordinary full-prefix gate only is proved; the six lanes stay. -/
theorem original_negative_quarter_actual_full_prefix_ledger
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    originalU34SignedQuarter N =
      (keptOriginalRankTwoMass N cap precision tau z0 lower
          (fun Q => actualFullPrefixGate lower Q) +
       keptOriginalRankTwoGap N cap precision tau z0 lower
          originalNegativeQuarterReceipt
          (fun Q => actualFullPrefixGate lower Q)) +
      originalSixUnpaidReceiptLanes N cap precision tau z0 lower
        originalNegativeQuarterReceipt := by
  rw [← original_negative_quarter_is_tagged_source N]
  have hs := complete_original_source_with_q_dependent_erasure
    N cap precision tau z0 lower hzcap
    originalNegativeQuarterReceipt
    (fun Q => actualFullPrefixGate lower Q)
  rw [actual_full_prefix_erases_no_observed_arithmetic
    N cap precision tau z0 lower originalNegativeQuarterReceipt] at hs
  simpa only [add_zero] using hs

/-- A valid UPPER bound for the NEGATIVE subtraction, still carrying
all six unpaid signed rejection lanes. It cannot be reversed into the
LOWER inequality required in the Chen lower-bound argument. -/
theorem original_negative_quarter_upper_with_unpaid_lanes
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    originalU34SignedQuarter N ≤
      -(1 / 4 : ℝ) *
        keptOriginalRankTwoMass N cap precision tau z0 lower
          (fun Q => actualFullPrefixGate lower Q) +
      originalSixUnpaidReceiptLanes N cap precision tau z0 lower
        originalNegativeQuarterReceipt := by
  rw [original_negative_quarter_actual_full_prefix_ledger
    N cap precision tau z0 lower hzcap]
  have hg := original_negative_quarter_kept_gap_upper
    N cap precision tau z0 lower
    (fun Q => actualFullPrefixGate lower Q)
  linarith

end
end ImbalancedChen.Part5OriginalH430NegativeQuarterActualPositionDirection
