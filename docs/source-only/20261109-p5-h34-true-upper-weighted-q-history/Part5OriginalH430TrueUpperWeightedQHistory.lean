import ImbalancedChen.Part5OriginalH430QFibreWeightedTrueLookup
import ImbalancedChen.Part5OriginalH430QDependentPositionErasure

/-!
P5.6 / h34: transport the LITERAL upper U3/U4 H430 lookup, including
independent q/tag-dependent weights, to the already constructed ACTUAL
physical-Q rank-two Fin-position history and its unpaid source lanes.

The upper kernel is the pinned OriginalU34 U3/U4 H430Coefficient;
this does not substitute a lower h-start, H248, a unit arithmetic
weight, or a generic owner coefficient.  The ordinary historical
mass, the arithmetic-minus-mass mismatch, every erased original
position and ALL six unpaid original receipt lanes remain separate.

The resulting equalities are signed finite SOURCE identities.  They
do NOT pay the gap, identify the manuscript full/selected/inherited
owner, construct an actual selected-count upper bound, or prove the
feedback-to-integral limit.  The U4 equality retains both original
q/tag weights at the same actual p and same H430 coefficient.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / COMPLETE H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430TrueUpperWeightedQHistory

noncomputable section
open Set
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5UpperTables.OriginalU34
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalUpperOverlapCount
open Part5OriginalH430QFibreWeightedTrueLookup
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430ActualPositionMassGap
open Part5OriginalH430QDependentPositionErasure

/-- The ACTUAL U3/U4 upper H430 coefficient at each original tagged
arithmetic (p,q) receipt, retaining independent arbitrary signed q
weights on the two tags.  A q/tag receipt is NOT a history Fin index. -/
def trueUpperH430TaggedReceiptWeight
    (N : ℕ) (w3 w4 : TaggedPair → ℝ) : TaggedReceiver → ℝ :=
  Sum.elim
    (fun x => w3 x * U3H430Coefficient (primeCoordinate N x.1))
    (fun x => w4 x * U4H430Coefficient (primeCoordinate N x.1))

/-- The concrete tagged source is definitionally the PREVIOUS true
upper H430 lookup, rather than a new proxy to be bounded later. -/
theorem original_true_upper_tagged_sum_eq_lookup
    (N : ℕ) (w3 w4 : TaggedPair → ℝ) :
    (∑ z ∈ originalTagged N,
      trueUpperH430TaggedReceiptWeight N w3 w4 z) =
      originalWeightedTrueH430Lookup N w3 w4 := rfl

/-- On every original U4 (p,q), the two DISTINCT arithmetic tags
read the same true upper H430 main-branch coefficient, while their
independent q-dependent weights are added rather than discarded.
This does not equate their historical root Q or resolved paths. -/
theorem original_u4_two_tag_true_upper_weight
    (N : ℕ) (hN : 2 ≤ N)
    (w3 w4 : TaggedPair → ℝ)
    {x : TaggedPair} (hx : x ∈ originalPairs N .U4) :
    trueUpperH430TaggedReceiptWeight N w3 w4 (Sum.inl x) +
      trueUpperH430TaggedReceiptWeight N w3 w4 (Sum.inr x) =
      (w3 x + w4 x) *
        U4H430Coefficient (primeCoordinate N x.1) := by
  have hp : x.1 ∈ originalBand N .U4 :=
    (Finset.mem_sigma.mp hx).1
  have ht : primeCoordinate N x.1 ∈ Ico a (59 / 250 : ℝ) :=
    primeCoordinate_mem hN (by simpa only [originalBand] using hp)
  have heq := U3_eq_main_on_U4 ht
  change w3 x * U3H430Coefficient (primeCoordinate N x.1) +
      w4 x * U4H430Coefficient (primeCoordinate N x.1) =
    (w3 x + w4 x) * U4H430Coefficient (primeCoordinate N x.1)
  rw [heq]
  ring

/-- The exact true upper U3/U4 H430 q-fibre cost has a source-side
decomposition on each real physical Q.  Surviving TRUE list positions
carry their genuine history mass PLUS a signed q-arithmetic mismatch.
Erased positions keep their original arithmetic weight; the six
original rejection/collision lanes remain in full.  The Q-dependent
Boolean test is NOT presumed to equal selected/inherited ownership. -/
theorem original_true_upper_H430_qfibres_to_actual_kept_history
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (hzcap : z0 ≤ (cap : ℝ))
    (w3 w4 : TaggedPair → ℝ)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    (∑ p ∈ upperExclusiveBand N,
        U3H430Coefficient (primeCoordinate N p) *
          originalQFibreWeight N w3 p) +
      (∑ p ∈ originalBand N .U4,
        U4H430Coefficient (primeCoordinate N p) *
          (originalQFibreWeight N w3 p +
           originalQFibreWeight N w4 p)) =
      (keptOriginalRankTwoMass N cap precision tau z0 lower keep +
       keptOriginalRankTwoGap N cap precision tau z0 lower
         (trueUpperH430TaggedReceiptWeight N w3 w4) keep) +
      erasedOriginalPositionArithmetic N cap precision tau z0 lower
        (trueUpperH430TaggedReceiptWeight N w3 w4) keep +
      originalSixUnpaidReceiptLanes N cap precision tau z0 lower
        (trueUpperH430TaggedReceiptWeight N w3 w4) := by
  calc
    _ = originalWeightedTrueH430Lookup N w3 w4 :=
      (original_weighted_true_H430_by_q_fibres N hN w3 w4).symm
    _ = ∑ z ∈ originalTagged N,
        trueUpperH430TaggedReceiptWeight N w3 w4 z :=
      (original_true_upper_tagged_sum_eq_lookup N w3 w4).symm
    _ = _ :=
      complete_original_source_with_q_dependent_erasure
        N cap precision tau z0 lower hzcap
        (trueUpperH430TaggedReceiptWeight N w3 w4) keep

/-- WITHOUT a later stage mask, all observed original U3/U4 H430
source weights can be localized to actual positive rank-two masses
and the EXACT original arithmetic/history gap plus all six unpaid
lanes.  No comparison with the signed first-excluded Euler suffix is
made; that is a different historical object. -/
theorem original_true_upper_H430_lookup_to_actual_unfiltered_history
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (w3 w4 : TaggedPair → ℝ) :
    originalWeightedTrueH430Lookup N w3 w4 =
      (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          observedRankTwoMassAtPosition
            N cap precision tau z0 lower Q i) +
      (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          originalRankTwoPositionMassGap N cap precision tau z0 lower
            (trueUpperH430TaggedReceiptWeight N w3 w4) Q i) +
      originalSixUnpaidReceiptLanes N cap precision tau z0 lower
        (trueUpperH430TaggedReceiptWeight N w3 w4) := by
  calc
    _ = (∑ z ∈ originalTagged N,
      trueUpperH430TaggedReceiptWeight N w3 w4 z) :=
      (original_true_upper_tagged_sum_eq_lookup N w3 w4).symm
    _ = _ := complete_original_source_true_mass_and_all_debts
      N cap precision tau z0 lower hzcap
      (trueUpperH430TaggedReceiptWeight N w3 w4)

/-- Literal Chen negative-quarter sign applied to the true H430
q-fibre cost.  It distributes over the actual kept mass, the exact
signed mismatch, erased original source, and six unpaid lanes.
Nothing on the right may be dropped without a directional estimate. -/
theorem original_true_upper_H430_negative_quarter_ledger
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (hzcap : z0 ≤ (cap : ℝ))
    (w3 w4 : TaggedPair → ℝ)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    -(1 / 4 : ℝ) *
      ((∑ p ∈ upperExclusiveBand N,
          U3H430Coefficient (primeCoordinate N p) *
            originalQFibreWeight N w3 p) +
       (∑ p ∈ originalBand N .U4,
          U4H430Coefficient (primeCoordinate N p) *
            (originalQFibreWeight N w3 p +
             originalQFibreWeight N w4 p))) =
      -(1 / 4 : ℝ) *
        (keptOriginalRankTwoMass N cap precision tau z0 lower keep +
         keptOriginalRankTwoGap N cap precision tau z0 lower
           (trueUpperH430TaggedReceiptWeight N w3 w4) keep) -
      (1 / 4 : ℝ) *
        erasedOriginalPositionArithmetic N cap precision tau z0 lower
          (trueUpperH430TaggedReceiptWeight N w3 w4) keep -
      (1 / 4 : ℝ) *
        originalSixUnpaidReceiptLanes N cap precision tau z0 lower
          (trueUpperH430TaggedReceiptWeight N w3 w4) := by
  rw [original_true_upper_H430_qfibres_to_actual_kept_history
    N cap precision tau z0 lower hN hzcap w3 w4 keep]
  ring

end
end ImbalancedChen.Part5OriginalH430TrueUpperWeightedQHistory
