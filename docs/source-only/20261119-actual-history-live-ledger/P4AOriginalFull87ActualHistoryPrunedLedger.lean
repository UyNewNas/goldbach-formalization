import ImbalancedChen.P4AOriginalFull87FifthHistoryCeilingPrune
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Exact, unconditional deletion of the fifth-history fibres already proved zero
by the ORIGINAL strict power gate and the ORIGINAL PLUS-Rosser active level.
The source is the real sharedRankFour / actualFifthSixthWithoutBoth event list;
only fifthExclusive RAW-only and LICENSED-only zero terms are filtered.
BOTH and sixthFromBoth are kept intact, not assigned an invented mask.
No signed monotonicity, smooth PP admission or second error payment is claimed.
-/

namespace ImbalancedChen.P4AOriginalFull87ActualHistoryPrunedLedger
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87FifthHistoryCeilingPrune
  (original_fifth_ordered_upper_zero_of_history_ceiling)
open P4AOriginalFull87StoppedGlobalPrimeLedger
  (upperPrimeFibreEventValue actualStoppedUpperPrimeCoefficient
   actual_fixed_stopped_upper_primewise_strict_half)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent FifthAdmissionClass)
open P4AOriginalFull87FifthSixthStoppedEvents
  (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice
  (actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization
  (sharedRankFour)
open P4AOriginalFull87EighthPrimeMeanLedger
  (receiverTest)
open P4AOriginalFull87FifthSignedPrimitive
  (actualFixedSignedFifthTail)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect
  (upperHalfReceiver)

/-- An EXACT zero-term deletion selector, applied AFTER the actual event
list has been generated. For inherited / BOTH events it is always true.
No new condition enters either original RAW or LICENSED producer. -/
def keepOriginalUpperHistory (L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → Bool
  | .fifthExclusive fifth =>
      match fifth.kind with
      | .rawOnly | .licensedOnly =>
          decide (X ^ 5 < (Nat.ceil L - 1) ^ 5 * fifth.selectedAfter.prod ^ 6)
      | .both => true
  | .sixthFromBoth _ _ => true

/-- A rejected event has ZERO literal upper-prime fibre, including its
original signed mass and every ordered sixth occurrence. -/
theorem rejected_event_has_zero_upper_value
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (ev : FifthSixthStoppedEvent ℕ)
    (hreject : keepOriginalUpperHistory L X ev = false) :
    upperPrimeFibreEventValue N cap w L X P ev = 0 := by
  cases ev with
  | fifthExclusive fifth =>
      cases hk : fifth.kind with
      | rawOnly =>
          by_cases hroom :
              X ^ 5 < (Nat.ceil L - 1) ^ 5 * fifth.selectedAfter.prod ^ 6
          · simp [keepOriginalUpperHistory, hk, hroom] at hreject
          · have hno :
                (Nat.ceil L - 1) ^ 5 * fifth.selectedAfter.prod ^ 6 ≤ X ^ 5 :=
              Nat.le_of_not_gt hroom
            have hz := original_fifth_ordered_upper_zero_of_history_ceiling
              N cap w L X P fifth hno
            simp [upperPrimeFibreEventValue, hk, hz]
      | both =>
          simp [keepOriginalUpperHistory, hk] at hreject
      | licensedOnly =>
          by_cases hroom :
              X ^ 5 < (Nat.ceil L - 1) ^ 5 * fifth.selectedAfter.prod ^ 6
          · simp [keepOriginalUpperHistory, hk, hroom] at hreject
          · have hno :
                (Nat.ceil L - 1) ^ 5 * fifth.selectedAfter.prod ^ 6 ≤ X ^ 5 :=
              Nat.le_of_not_gt hroom
            have hz := original_fifth_ordered_upper_zero_of_history_ceiling
              N cap w L X P fifth hno
            simp [upperPrimeFibreEventValue, hk, hz]
  | sixthFromBoth _ _ =>
      simp [keepOriginalUpperHistory] at hreject

/-- Finite zero deletion holds on LISTS, not Finsets: repeated source
occurrences retain their original multiplicity, relative order and sign. -/
private theorem ordered_sum_eq_filter_of_rejected_zero
    {α : Type*} (xs : List α) (keep : α → Bool) (f : α → ℝ)
    (hzero : ∀ x, keep x = false → f x = 0) :
    (xs.map f).sum = ((xs.filter keep).map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases hk : keep x with
      | false =>
          have hx : f x = 0 := hzero x hk
          simpa [List.filter, hk, hx] using ih
      | true =>
          simpa [List.filter, hk] using
            congrArg (fun y : ℝ => f x + y) ih

/-- The same original dynamic parents and receiver-generated events,
only with independently certified ZERO upper fifth-exclusive terms omitted.
No arbitrary event witness, target-equivalent structure field, or new branch
policy is introduced. -/
def actualStoppedUpperPrimeHistoryLiveCoefficient
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state).filter (keepOriginalUpperHistory L X)).map
      (upperPrimeFibreEventValue N cap w L X P)).sum)).sum

/-- Unconditional equality at one physical prime P, NOT a bound.
The actual producer is evaluated once and only proved-zero contributions
are deleted. The entire original signed ledger is otherwise unchanged. -/
theorem actual_stopped_upper_coefficient_eq_history_live
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ) :
    actualStoppedUpperPrimeCoefficient delta n e q om N cap w z L X P =
      actualStoppedUpperPrimeHistoryLiveCoefficient
        delta n e q om N cap w z L X P := by
  unfold actualStoppedUpperPrimeCoefficient
    actualStoppedUpperPrimeHistoryLiveCoefficient
  apply congrArg List.sum
  apply List.map_congr_left
  intro state _
  exact ordered_sum_eq_filter_of_rejected_zero
    (actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state)
    (keepOriginalUpperHistory L X)
    (upperPrimeFibreEventValue N cap w L X P)
    (fun ev he => rejected_event_has_zero_upper_value N cap w L X P ev he)

/-- Exact source-preserving pruning in the actual stopped upper HALF.
The strict 2*P<N bound and the original prime prefix remain unchanged.
This is not an asymptotic gain and no reserve is paid here. -/
theorem actual_fixed_stopped_upper_eq_history_live_primewise
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
        (upperHalfReceiver N) =
      ∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
        actualStoppedUpperPrimeHistoryLiveCoefficient
          delta n e q om N cap w z L X P := by
  rw [actual_fixed_stopped_upper_primewise_strict_half]
  apply Finset.sum_congr rfl
  intro P _
  exact actual_stopped_upper_coefficient_eq_history_live
    delta n e q om N cap w z L X P

end
end ImbalancedChen.P4AOriginalFull87ActualHistoryPrunedLedger
