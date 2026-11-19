import ImbalancedChen.P4AOriginalFull87WeightedCentreCancellation
import ImbalancedChen.P4AOriginalFull87ReflectedPrefixAbel
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Actual frozen, ordered RAW/LICENSED carrier-error invoice.  The preceding
packet eliminated the weighted upper centre correction on ONE complete
Rosser modulus.  This packet transports that exact identity, without
deduplicating sixth occurrences or replacing the original fifth sign, to
the already existing frozen physical stopped identity.  It produces an
EXACT, endpoint-specific nonnegative primitive-discrepancy bill.  There
is no distribution theorem, asymptotic H_N payment or surrogate source.
-/

namespace ImbalancedChen.P4AOriginalFull87CarrierGlobalJumpInvoice
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87WeightedCentreCancellation
  (originalRoomCarrierJumpCorrection
   original_room_abel_eq_carrier_jump_correction)
open P4AOriginalFull87ReflectedPrefixAbel
  (originalRoomAbelCorrection actualRoomBetaWeight
   originalSignedAbelPrimeEvent frozenSurvivorSignedAbelPrimeRoom
   physical_after_lower_eq_original_reflected_abel)
open P4AOriginalFull87CentreIntervalBridge
  (originalCarrierIntervalDiscrepancy)
open P4AOriginalFull87AnchoredJumpPrimitivePrefix
  (originalFullRoomLowerGate)
open P4AOriginalFull87ActualPrimitiveRosserRoom
  (actualPrimitiveRosserRoom)
open P4AOriginalFull87FifthSixthStoppedEvents
  (FifthSixthStoppedEvent)
open P4AOriginalFull87RankFourStoppedLocalization
  (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice
  (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FrozenSurvivorInvoice
  (keepFrozenUpperSurvivor)
open P4AOriginalFull87EighthPrimeMeanLedger
  (receiverTest)
open P4AOriginalFull87EarlyStopPhysicalGap
  (rawStopped licensedStopped)
open P4AOriginalFull87FifthSignedPrimitive
  (actualFixedSignedFifthTail)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect
  (lowerHalfReceiver)

private theorem list_sum_add {α : Type*} (xs : List α)
    (f g : α → ℝ) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

private theorem list_abs_sum_le {α : Type*} (xs : List α)
    (f : α → ℝ) :
    |(xs.map f).sum| ≤ (xs.map (fun x => |f x|)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have h := abs_add_le (f x) ((xs.map f).sum)
      have h' := add_le_add_left ih |f x|
      simpa only [List.map_cons, List.sum_cons] using le_trans h h'

private theorem list_map_sum_le {α : Type*} (xs : List α)
    (f g : α → ℝ) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      apply add_le_add (h x (by simp))
      apply ih
      intro y hy
      exact h y (by simp [hy])

/-- Reference mean attached to EACH original complete sixth modulus.
Not declared to be a correct prime density. -/
def originalCarrierMeanEvent (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (mean : ℕ → ℝ) : FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      let v : ℝ := (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          (mean (p :: fifth.selectedAfter).prod *
            (∑ a ∈ actualPrimitiveRosserRoom N cap w L X
              fifth.selectedAfter p, actualSmallRosserPlus N cap w L a)))).sum
      match fifth.kind with
      | .rawOnly => v
      | .licensedOnly => -v
      | .both => 0
  | .sixthFromBoth _ _ => 0

/-- Signed error on precisely the same fifth and ordered sixth source.
The centre-prime correction has already been cancelled, not budgeted. -/
def originalCarrierJumpEvent (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (mean : ℕ → ℝ) : FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      let v : ℝ := (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          originalRoomCarrierJumpCorrection N cap w L X
            fifth.selectedAfter p mean)).sum
      match fifth.kind with
      | .rawOnly => v
      | .licensedOnly => -v
      | .both => 0
  | .sixthFromBoth _ _ => 0

/-- The local exact-jump invoice only uses the original beta differences
and actual primitive carrier discrepancies at their original endpoints. -/
def originalCarrierJumpExactBill (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
    |actualRoomBetaWeight N cap w L X pre p t -
      actualRoomBetaWeight N cap w L X pre p (t + 1)| *
    |originalCarrierIntervalDiscrepancy N pre p mean
      (originalFullRoomLowerGate N X pre p) (t + 1)|

/-- One original stopped event's nonnegative invoice. Repeated ordered
sixth occurrences are retained; BOTH/inherited terms stay exactly zero. -/
def originalCarrierJumpEventBill (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (mean : ℕ → ℝ) : FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      let v : ℝ := (fifth.remainingAfter.map (fun p =>
        |signedTreeCoefficient true fifth.massAfter| *
          originalCarrierJumpExactBill N cap w L X
            fifth.selectedAfter p mean)).sum
      match fifth.kind with
      | .rawOnly | .licensedOnly => v
      | .both => 0
  | .sixthFromBoth _ _ => 0

/-- Finite exact separation: original signed Abel prime event is
the per-modulus reference part PLUS its primitive jump correction. -/
theorem original_event_abel_eq_mean_add_carrier
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (mean : ℕ → ℝ)
    (ev : FifthSixthStoppedEvent ℕ) :
    originalSignedAbelPrimeEvent N cap w L X mean ev =
      originalCarrierMeanEvent N cap w L X mean ev +
      originalCarrierJumpEvent N cap w L X mean ev := by
  classical
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [originalSignedAbelPrimeEvent,
        originalCarrierMeanEvent, originalCarrierJumpEvent]
  | fifthExclusive fifth =>
      let c : ℝ := signedTreeCoefficient true fifth.massAfter
      let F : ℕ → ℝ := fun p =>
        mean (p :: fifth.selectedAfter).prod *
          (∑ a ∈ actualPrimitiveRosserRoom N cap w L X
            fifth.selectedAfter p, actualSmallRosserPlus N cap w L a)
      let G : ℕ → ℝ := fun p =>
        originalRoomCarrierJumpCorrection N cap w L X
          fifth.selectedAfter p mean
      have hrewrite :
          (fifth.remainingAfter.map (fun p =>
            c * (F p + originalRoomAbelCorrection N cap w L X
              fifth.selectedAfter p mean))).sum =
          (fifth.remainingAfter.map (fun p => c * (F p + G p))).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro p hp
        rw [original_room_abel_eq_carrier_jump_correction]
      have hsum :
          (fifth.remainingAfter.map (fun p => c * (F p + G p))).sum =
          (fifth.remainingAfter.map (fun p => c * F p)).sum +
          (fifth.remainingAfter.map (fun p => c * G p)).sum := by
        calc
          _ = (fifth.remainingAfter.map
                (fun p => c * F p + c * G p)).sum := by
                  apply congrArg List.sum
                  apply List.map_congr_left
                  intro p hp
                  ring
          _ = _ := list_sum_add fifth.remainingAfter
            (fun p => c * F p) (fun p => c * G p)
      have h := hrewrite.trans hsum
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [originalSignedAbelPrimeEvent,
            originalCarrierMeanEvent, originalCarrierJumpEvent,
            hk, c, F, G] using h
      | licensedOnly =>
          have hneg :
              -((fifth.remainingAfter.map (fun p =>
                c * (F p + originalRoomAbelCorrection N cap w L X
                  fifth.selectedAfter p mean))).sum) =
              -((fifth.remainingAfter.map (fun p => c * F p)).sum) +
              -((fifth.remainingAfter.map (fun p => c * G p)).sum) := by
            rw [h]
            ring
          simpa [originalSignedAbelPrimeEvent,
            originalCarrierMeanEvent, originalCarrierJumpEvent,
            hk, c, F, G] using hneg
      | both =>
          simp [originalSignedAbelPrimeEvent,
            originalCarrierMeanEvent, originalCarrierJumpEvent, hk]

/-- Finite triangle inequality at the true Rosser beta jump positions.
No E bound or distribution hypothesis is invoked. -/
theorem original_carrier_jump_abs_le_exact_bill
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p : ℕ) (mean : ℕ → ℝ) :
    |originalRoomCarrierJumpCorrection N cap w L X pre p mean| ≤
      originalCarrierJumpExactBill N cap w L X pre p mean := by
  unfold originalRoomCarrierJumpCorrection originalCarrierJumpExactBill
  calc
    |∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
      (actualRoomBetaWeight N cap w L X pre p t -
       actualRoomBetaWeight N cap w L X pre p (t + 1)) *
      originalCarrierIntervalDiscrepancy N pre p mean
        (originalFullRoomLowerGate N X pre p) (t + 1)| ≤
      ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
        |(actualRoomBetaWeight N cap w L X pre p t -
           actualRoomBetaWeight N cap w L X pre p (t + 1)) *
          originalCarrierIntervalDiscrepancy N pre p mean
            (originalFullRoomLowerGate N X pre p) (t + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp_rw [abs_mul]

/-- Absolute invoice for the real original event signs, not for a newly
selected fifth subtree. -/
theorem original_carrier_jump_event_abs_le_bill
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (mean : ℕ → ℝ)
    (ev : FifthSixthStoppedEvent ℕ) :
    |originalCarrierJumpEvent N cap w L X mean ev| ≤
      originalCarrierJumpEventBill N cap w L X mean ev := by
  classical
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [originalCarrierJumpEvent, originalCarrierJumpEventBill]
  | fifthExclusive fifth =>
      let c : ℝ := signedTreeCoefficient true fifth.massAfter
      let G : ℕ → ℝ := fun p =>
        originalRoomCarrierJumpCorrection N cap w L X
          fifth.selectedAfter p mean
      let B : ℕ → ℝ := fun p =>
        originalCarrierJumpExactBill N cap w L X
          fifth.selectedAfter p mean
      have hbound :
          |(fifth.remainingAfter.map (fun p => c * G p)).sum| ≤
          (fifth.remainingAfter.map (fun p => |c| * B p)).sum := by
        calc
          _ ≤ (fifth.remainingAfter.map (fun p => |c * G p|)).sum :=
            list_abs_sum_le fifth.remainingAfter (fun p => c * G p)
          _ ≤ (fifth.remainingAfter.map (fun p => |c| * B p)).sum := by
            apply list_map_sum_le
            intro p hp
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left
              (original_carrier_jump_abs_le_exact_bill N cap w L X
                fifth.selectedAfter p mean) (abs_nonneg c)
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [originalCarrierJumpEvent,
            originalCarrierJumpEventBill, hk, c, G, B] using hbound
      | licensedOnly =>
          simpa [originalCarrierJumpEvent,
            originalCarrierJumpEventBill, hk, c, G, B, abs_neg] using hbound
      | both =>
          simp [originalCarrierJumpEvent, originalCarrierJumpEventBill, hk]

/-- The SAME original frozen state/event lists for both components.
No list-to-Finset conversion and no new branch-specific mask. -/
def frozenSurvivorCarrierMeanRoom
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (originalCarrierMeanEvent N cap w
        ((N : ℝ) ^ epsilon) X mean)).sum)).sum

def frozenSurvivorCarrierJumpRoom
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (originalCarrierJumpEvent N cap w
        ((N : ℝ) ^ epsilon) X mean)).sum)).sum

def frozenSurvivorCarrierJumpInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (originalCarrierJumpEventBill N cap w
        ((N : ℝ) ^ epsilon) X mean)).sum)).sum

/-- Exact physical split with the original fifth sign and every actual
sixth occurrence; the external mean remains an arbitrary parameter. -/
theorem frozen_abel_eq_mean_plus_carrier_jump
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ) :
    frozenSurvivorSignedAbelPrimeRoom
      delta n e q om N cap w epsilon X mean =
      frozenSurvivorCarrierMeanRoom
        delta n e q om N cap w epsilon X mean +
      frozenSurvivorCarrierJumpRoom
        delta n e q om N cap w epsilon X mean := by
  let states := sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))
  let events := fun state =>
    (actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
      (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X)
  let A := originalSignedAbelPrimeEvent
    N cap w ((N : ℝ) ^ epsilon) X mean
  let M := originalCarrierMeanEvent
    N cap w ((N : ℝ) ^ epsilon) X mean
  let J := originalCarrierJumpEvent
    N cap w ((N : ℝ) ^ epsilon) X mean
  change (states.map (fun s => ((events s).map A).sum)).sum =
    (states.map (fun s => ((events s).map M).sum)).sum +
    (states.map (fun s => ((events s).map J).sum)).sum
  calc
    _ = (states.map (fun s =>
        ((events s).map (fun ev => M ev + J ev)).sum)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro state hs
          apply congrArg List.sum
          apply List.map_congr_left
          intro ev hev
          exact original_event_abel_eq_mean_add_carrier
            N cap w ((N : ℝ) ^ epsilon) X mean ev
    _ = (states.map (fun s =>
        ((events s).map M).sum + ((events s).map J).sum)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro state hs
          exact list_sum_add (events state) M J
    _ = _ := list_sum_add states
      (fun s => ((events s).map M).sum)
      (fun s => ((events s).map J).sum)

/-- Exact finite error bill: absolute values are introduced ONCE after
the original raw/licensed tags and fifth/sixth occurrence sums. -/
theorem frozen_carrier_jump_abs_le_exact_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ) :
    |frozenSurvivorCarrierJumpRoom
      delta n e q om N cap w epsilon X mean| ≤
      frozenSurvivorCarrierJumpInvoice
        delta n e q om N cap w epsilon X mean := by
  let states := sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))
  let events := fun state =>
    (actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
      (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X)
  let J := originalCarrierJumpEvent
    N cap w ((N : ℝ) ^ epsilon) X mean
  let B := originalCarrierJumpEventBill
    N cap w ((N : ℝ) ^ epsilon) X mean
  change |(states.map (fun s => ((events s).map J).sum)).sum| ≤
    (states.map (fun s => ((events s).map B).sum)).sum
  calc
    _ ≤ (states.map (fun s => |((events s).map J).sum|)).sum :=
      list_abs_sum_le states (fun s => ((events s).map J).sum)
    _ ≤ (states.map (fun s =>
        ((events s).map (fun ev => |J ev|)).sum)).sum := by
          apply list_map_sum_le
          intro state hs
          exact list_abs_sum_le (events state) J
    _ ≤ (states.map (fun s => ((events s).map B).sum)).sum := by
          apply list_map_sum_le
          intro state hs
          apply list_map_sum_le
          intro ev hev
          exact original_carrier_jump_event_abs_le_bill
            N cap w ((N : ℝ) ^ epsilon) X mean ev

/-- Physical stopped RAW-LICENSED difference, lower removed exactly
once, differs from the actual carrier mean by at most the actual
endpoint-specific primitive AP invoice. No analytic estimate is hidden. -/
theorem physical_after_lower_error_le_exact_carrier_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    |((rawStopped e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
         ((N : ℝ) ^ epsilon) X (receiverTest N) -
       licensedStopped delta n e q om N cap w
         ((N : ℝ) ^ ((19 : ℝ) / 96))
         ((N : ℝ) ^ epsilon) X (receiverTest N)) -
      actualFixedSignedFifthTail delta n e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X (lowerHalfReceiver N)) -
      frozenSurvivorCarrierMeanRoom
        delta n e q om N cap w epsilon X mean| ≤
    frozenSurvivorCarrierJumpInvoice
      delta n e q om N cap w epsilon X mean := by
  rw [physical_after_lower_eq_original_reflected_abel
    delta n e q om N cap w epsilon X mean he hN heps hX]
  rw [frozen_abel_eq_mean_plus_carrier_jump]
  simpa only [add_sub_cancel_left] using
    frozen_carrier_jump_abs_le_exact_invoice
      delta n e q om N cap w epsilon X mean

end
end ImbalancedChen.P4AOriginalFull87CarrierGlobalJumpInvoice
