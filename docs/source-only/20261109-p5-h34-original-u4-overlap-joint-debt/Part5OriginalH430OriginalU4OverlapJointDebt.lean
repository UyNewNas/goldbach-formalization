import ImbalancedChen.Part5OriginalH430ActualOccupiedMass
import ImbalancedChen.Part5OriginalH430OriginalUpperOverlapCount

/-!
P5.6/h34: original U4 overlapping tagged arithmetic debt, retaining
BOTH distinct genuinely resolved marked sources.

The previous original upper overlap packet proved that U4 is a subset
of U3 and every original U4 quotient has TWO arithmetic labels.
The newer actual occupied source packet bounded one tag at a time,
but its U3+U4 sum did not expose the precise overlap deficit.

Here the two tags keep separate root Q, resolved levels, literal
positive Phi and q receiver. Their unpaid positive parts cannot in
general be replaced by a single tagged debt or by a single history mark.
The lower bound is a NECESSARY accounting constraint, not an H430
upper estimate, historical payment, or identified selected owner.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430OriginalU4OverlapJointDebt

noncomputable section

open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430ActualResolvedMarkedPushforward
open Part5OriginalH430TrueCountMarkedGap
open Part5OriginalH430ActualUnpaidOrdinaryEnvelope
open Part5OriginalH430ActualOccupiedMass
open Part5OriginalH430OriginalUpperOverlapCount
open P2EnhancedTwentyOneSameQWeighted

/-- The SAME original quotient-receiver count for each of the two
U4-overlap tags, but the two genuine marked sources are different
root-indexed objects. Even if their physical Q values happen to
coincide, the two actual resolved histories are not identified. -/
def actualOriginalOverlapJointDebt
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430)
    (p : ℕ) : ℝ :=
  max
    (2 * ((originalReceiver N p).card : ℝ) -
      5 * (Phi N (rootQ N n .U3 tau p)
             (activeProductSupport N n .U3 tau p (depth .U3 p))
             (activeProductSigma N n .U3 tau p (depth .U3 p)) (11/5) +
           Phi N (rootQ N n .U4 tau p)
             (activeProductSupport N n .U4 tau p (depth .U4 p))
             (activeProductSigma N n .U4 tau p (depth .U4 p)) (11/5))) 0

/-- The arithmetic cost of BOTH original tags is at least the
positive part of their combined unmarked-minus-marked difference.
No q/product correspondence, missing owner, or payment estimate is
assumed. The two original real Phi sources are used as they stand. -/
theorem original_overlap_joint_debt_le_two_tag_unpaid
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430)
    (p : ℕ) :
    actualOriginalOverlapJointDebt N n tau depth p ≤
      actualUnpaidAt N n .U3 tau p (depth .U3 p) +
      actualUnpaidAt N n .U4 tau p (depth .U4 p) := by
  dsimp [actualOriginalOverlapJointDebt, actualUnpaidAt,
    unpaidOriginalMarkedGap, originalMarkedDiscrepancy]
  apply max_le
  · have h3 := le_max_left
      (((originalReceiver N p).card : ℝ) -
        5 * Phi N (rootQ N n .U3 tau p)
          (activeProductSupport N n .U3 tau p (depth .U3 p))
          (activeProductSigma N n .U3 tau p (depth .U3 p)) (11/5))
      (0 : ℝ)
    have h4 := le_max_left
      (((originalReceiver N p).card : ℝ) -
        5 * Phi N (rootQ N n .U4 tau p)
          (activeProductSupport N n .U4 tau p (depth .U4 p))
          (activeProductSigma N n .U4 tau p (depth .U4 p)) (11/5))
      (0 : ℝ)
    linarith
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

/-- The ORIGINAL U3-exclusive q-fibres are charged only once.
Each genuine U4-overlap root contributes one *joint necessary* debt
which keeps both tagged real Phi sources and both original q counts.
Nothing here is asserted to be the actual full/selected owner. -/
def actualOriginalOverlapLowerEnvelope
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430) : ℝ :=
  (∑ p ∈ upperExclusiveBand N,
    actualUnpaidAt N n .U3 tau p (depth .U3 p)) +
  (∑ p ∈ originalBand N .U4,
    actualOriginalOverlapJointDebt N n tau depth p)

/-- Exact U3-exclusive/U4-overlap decomposition of the ORIGINAL
two-tag actual unpaid ledger. The U4 overlap keeps both tagged
histories, so it contributes TWO terms, not one. -/
theorem actual_U34_unpaid_exact_original_overlap
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430)
    (hN : 1 ≤ N) :
    actualU34Unpaid N n tau depth =
      (∑ p ∈ upperExclusiveBand N,
        actualUnpaidAt N n .U3 tau p (depth .U3 p)) +
      (∑ p ∈ originalBand N .U4,
        (actualUnpaidAt N n .U3 tau p (depth .U3 p) +
         actualUnpaidAt N n .U4 tau p (depth .U4 p))) := by
  have hd : Disjoint (upperExclusiveBand N) (originalBand N .U4) := by
    apply Finset.disjoint_left.mpr
    intro p hp h4
    exact (Finset.mem_sdiff.mp hp).2 h4
  unfold actualU34Unpaid
  rw [original_u3_band_partition N hN, Finset.sum_union hd]
  simp only [Finset.sum_add_distrib]
  ac_rfl

/-- An unconditional NECESSARY quantitative bound, now stated for
the actual original U3+U4 summed q debt: on every U4 root, the
combined two-tag deficit must be accounted for. This is a LOWER
bound for the unpaid debt, not the desired small upper bound. -/
theorem actual_U34_overlap_lower_envelope_le_unpaid
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430)
    (hN : 1 ≤ N) :
    actualOriginalOverlapLowerEnvelope N n tau depth ≤
      actualU34Unpaid N n tau depth := by
  rw [actual_U34_unpaid_exact_original_overlap N n tau depth hN]
  unfold actualOriginalOverlapLowerEnvelope
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro p hp
  exact original_overlap_joint_debt_le_two_tag_unpaid N n tau depth p

end
end ImbalancedChen.Part5OriginalH430OriginalU4OverlapJointDebt
