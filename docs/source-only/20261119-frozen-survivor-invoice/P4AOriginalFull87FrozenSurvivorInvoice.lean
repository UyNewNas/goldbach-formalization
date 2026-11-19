import ImbalancedChen.P4AOriginalFull87UpperFixedHistoryBand
import ImbalancedChen.P4AOriginalFull87ActualUpperCeilingZ
import ImbalancedChen.P4AOriginalFull87StoppedGlobalPrimeLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The literal frozen upper history band is now consumed at the ORIGINAL
sharedRankFour stopped physical producer, NOT just at one fifth event.
We filter only fifthExclusive one-sided events whose original upper-prime
contribution is proved zero; BOTH and sixthFromBoth are always retained.
The exact ordered source, signed mass, Rosser quotient, complete modulus,
and strict 2*P<N are unchanged.

The new finite absolute invoice is for the *surviving actual terms* and
is NOT an H_N estimate. No smooth PP is called on an arithmetic mask.
-/

namespace ImbalancedChen.P4AOriginalFull87FrozenSurvivorInvoice
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87UpperFixedHistoryBand
  (actual_fifth_upper_prime_zero_below_frozen_band)
open P4AOriginalFull87ActualUpperCeilingZ
  (keepOriginalUpperHistoryWithZ
   actual_rejected_upper_history_with_z_zero)
open P4AOriginalFull87StoppedGlobalPrimeLedger
  (upperPrimeFibreEventValue actualStoppedUpperPrimeCoefficient
   actual_physical_stopped_delta_primewise_and_lower)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87FifthSignedPrimitive (actualFixedSignedFifthTail)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect (lowerHalfReceiver)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)

/-- An accounting selector AFTER the original event list is produced.
It combines the earlier exact integer power/ceiling-z zero tests with
the frozen 9601/12000 test. Not a RAW/LICENSED policy modification. -/
def keepFrozenUpperSurvivor (N : ℕ) (z L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → Bool
  | .fifthExclusive fifth =>
      match fifth.kind with
      | .rawOnly | .licensedOnly =>
          keepOriginalUpperHistoryWithZ N z L X (.fifthExclusive fifth) &&
          decide ((N : ℝ) ^ ((9601 : ℝ) / 12000) <
            2 * (fifth.selectedAfter.prod : ℝ))
      | .both => true
  | .sixthFromBoth _ _ => true

/-- Every excluded occurrence of the REAL receiver-generated List is
zero as an original upper-prime coefficient, for the literal frozen
z=N^(19/96), L=N^epsilon. Neither the generic upstream parameter
binding nor an analytic payment is inferred. -/
theorem actual_rejected_frozen_survivor_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X P : ℕ)
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96)))
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth delta n e q om
      N cap w ((N : ℝ) ^ epsilon) X (receiverTest N) state)
    (hreject : keepFrozenUpperSurvivor N
      ((N : ℝ) ^ ((19 : ℝ) / 96)) ((N : ℝ) ^ epsilon) X ev = false) :
    upperPrimeFibreEventValue N cap w ((N : ℝ) ^ epsilon) X P ev = 0 := by
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [keepFrozenUpperSurvivor] at hreject
  | fifthExclusive fifth =>
      cases hk : fifth.kind with
      | both =>
          simp [keepFrozenUpperSurvivor, hk] at hreject
      | rawOnly =>
          by_cases hb : (N : ℝ) ^ ((9601 : ℝ) / 12000) <
              2 * (fifth.selectedAfter.prod : ℝ)
          · have hold : keepOriginalUpperHistoryWithZ N
                ((N : ℝ) ^ ((19 : ℝ) / 96)) ((N : ℝ) ^ epsilon)
                X (.fifthExclusive fifth) = false := by
              cases hOld : keepOriginalUpperHistoryWithZ N
                  ((N : ℝ) ^ ((19 : ℝ) / 96))
                  ((N : ℝ) ^ epsilon) X (.fifthExclusive fifth) with
              | false => rfl
              | true =>
                  simp [keepFrozenUpperSurvivor, hk, hb, hOld] at hreject
            exact actual_rejected_upper_history_with_z_zero
              delta n e q om N cap w
              ((N : ℝ) ^ ((19 : ℝ) / 96)) ((N : ℝ) ^ epsilon)
              X P state hstate (.fifthExclusive fifth) hev hold
          · exact actual_fifth_upper_prime_zero_below_frozen_band
              delta n e q om N cap w epsilon X P hN heps
              state hstate fifth hev (le_of_not_gt hb)
      | licensedOnly =>
          by_cases hb : (N : ℝ) ^ ((9601 : ℝ) / 12000) <
              2 * (fifth.selectedAfter.prod : ℝ)
          · have hold : keepOriginalUpperHistoryWithZ N
                ((N : ℝ) ^ ((19 : ℝ) / 96)) ((N : ℝ) ^ epsilon)
                X (.fifthExclusive fifth) = false := by
              cases hOld : keepOriginalUpperHistoryWithZ N
                  ((N : ℝ) ^ ((19 : ℝ) / 96))
                  ((N : ℝ) ^ epsilon) X (.fifthExclusive fifth) with
              | false => rfl
              | true =>
                  simp [keepFrozenUpperSurvivor, hk, hb, hOld] at hreject
            exact actual_rejected_upper_history_with_z_zero
              delta n e q om N cap w
              ((N : ℝ) ^ ((19 : ℝ) / 96)) ((N : ℝ) ^ epsilon)
              X P state hstate (.fifthExclusive fifth) hev hold
          · exact actual_fifth_upper_prime_zero_below_frozen_band
              delta n e q om N cap w epsilon X P hN heps
              state hstate fifth hev (le_of_not_gt hb)

/-- Lossless list filtering when every deleted item is zero. This does
not identify equal values, reorder events or change occurrence counts. -/
private theorem ordered_sum_remove_zero {α : Type*}
    (xs : List α) (keep : α → Bool) (f : α → ℝ)
    (hz : ∀ x ∈ xs, keep x = false → f x = 0) :
    (xs.map f).sum = ((xs.filter keep).map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : ∀ y ∈ xs, keep y = false → f y = 0 := by
        intro y hy hk
        exact hz y (by simp [hy]) hk
      cases hk : keep x with
      | false =>
          have hx : f x = 0 := hz x (by simp) hk
          simpa [List.filter, hk, hx] using ih htail
      | true =>
          simpa [List.filter, hk] using
            congrArg (fun t : ℝ => f x + t) (ih htail)

/-- Same literal sharedRankFour parent, same receiverTest list, same
fifth sign, and same ordered sixth occurrences. Only proven-zero
one-sided events are removed from this accounting view. -/
def frozenSurvivorUpperPrimeCoefficient
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X P : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N
          ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (upperPrimeFibreEventValue N cap w ((N : ℝ) ^ epsilon) X P)).sum)).sum

/-- The original upper coefficient is EXACTLY the same after the
third certified-zero test, on actual producer occurrences. -/
theorem actual_upper_prime_eq_frozen_survivor_coefficient
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X P : ℕ)
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ)) :
    actualStoppedUpperPrimeCoefficient delta n e q om
      N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
      ((N : ℝ) ^ epsilon) X P =
    frozenSurvivorUpperPrimeCoefficient
      delta n e q om N cap w epsilon X P := by
  unfold actualStoppedUpperPrimeCoefficient
    frozenSurvivorUpperPrimeCoefficient
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hstate
  exact ordered_sum_remove_zero
    (actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state)
    (keepFrozenUpperSurvivor N
      ((N : ℝ) ^ ((19 : ℝ) / 96))
      ((N : ℝ) ^ epsilon) X)
    (upperPrimeFibreEventValue N cap w ((N : ℝ) ^ epsilon) X P)
    (fun ev hev hr =>
      actual_rejected_frozen_survivor_zero
        delta n e q om N cap w epsilon X P hN heps
        state hstate ev hev hr)

/-- Physical RAW-LICENSED stopped difference, at the literal frozen
rough upper z and L. The lower receiver remains UNCHANGED, with NO
new mask and NO extra centre or reserve subtraction. -/
theorem actual_physical_stopped_eq_frozen_survivors_plus_lower
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    rawStopped e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X (receiverTest N) -
      licensedStopped delta n e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X (receiverTest N) =
      (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
        frozenSurvivorUpperPrimeCoefficient
          delta n e q om N cap w epsilon X P) +
      actualFixedSignedFifthTail delta n e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X (lowerHalfReceiver N) := by
  have hgeneric :=
    actual_physical_stopped_delta_primewise_and_lower
      delta n e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
      he hN epsilon heps X hX
  have hupper :
      (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
        actualStoppedUpperPrimeCoefficient delta n e q om N cap w
          ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X P) =
      ∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
        frozenSurvivorUpperPrimeCoefficient
          delta n e q om N cap w epsilon X P := by
    apply Finset.sum_congr rfl
    intro P _
    exact actual_upper_prime_eq_frozen_survivor_coefficient
      delta n e q om N cap w epsilon X P hN heps
  rw [hgeneric, hupper]

/-- Ordinary finite triangle inequality for the original ordered List. -/
private theorem abs_ordered_sum_le {α : Type*}
    (xs : List α) (f : α → ℝ) :
    |(xs.map f).sum| ≤ (xs.map (fun x => |f x|)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add _ _).trans (add_le_add_left ih _)

/-- Two nested original occurrence lists, with NO Finset conversion
on either parent or event axis. -/
private theorem abs_nested_ordered_sum_le {α β : Type*}
    (xs : List α) (ys : α → List β) (f : α → β → ℝ) :
    |(xs.map (fun x => ((ys x).map (f x)).sum)).sum| ≤
      (xs.map (fun x =>
        ((ys x).map (fun y => |f x y|)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add _ _).trans
        (add_le_add (abs_ordered_sum_le (ys x) (f x)) ih)

/-- A single finite outstanding UPPER invoice, restricted to the
actually surviving original one-sided fifth events. It is NOT a new
physical payment: its RHS is still an unevaluated signed-source norm. -/
def frozenSurvivorUpperAbsoluteInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) : ℝ :=
  ∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
    ((sharedRankFour e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
      (((actualFifthSixthWithoutBoth delta n e q om N cap w
        ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
          (keepFrozenUpperSurvivor N
            ((N : ℝ) ^ ((19 : ℝ) / 96))
            ((N : ℝ) ^ epsilon) X)).map (fun ev =>
          |upperPrimeFibreEventValue N cap w
            ((N : ℝ) ^ epsilon) X P ev|)).sum)).sum

/-- This upper arithmetic bill is bounded by one literal absolute
invoice over the SAME source. No H_N smallness or smooth PP is inferred. -/
theorem abs_frozen_survivor_upper_prime_sum_le_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) :
    |∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
      frozenSurvivorUpperPrimeCoefficient
        delta n e q om N cap w epsilon X P| ≤
    frozenSurvivorUpperAbsoluteInvoice
      delta n e q om N cap w epsilon X := by
  have hterm (P : ℕ) :
      |frozenSurvivorUpperPrimeCoefficient
        delta n e q om N cap w epsilon X P| ≤
      ((sharedRankFour e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
        (((actualFifthSixthWithoutBoth delta n e q om N cap w
          ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
            (keepFrozenUpperSurvivor N
              ((N : ℝ) ^ ((19 : ℝ) / 96))
              ((N : ℝ) ^ epsilon) X)).map (fun ev =>
            |upperPrimeFibreEventValue N cap w
              ((N : ℝ) ^ epsilon) X P ev|)).sum)).sum := by
    unfold frozenSurvivorUpperPrimeCoefficient
    exact abs_nested_ordered_sum_le
      (sharedRankFour e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96)))
      (fun state =>
        (actualFifthSixthWithoutBoth delta n e q om N cap w
          ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
            (keepFrozenUpperSurvivor N
              ((N : ℝ) ^ ((19 : ℝ) / 96))
              ((N : ℝ) ^ epsilon) X))
      (fun _ ev =>
        upperPrimeFibreEventValue N cap w ((N : ℝ) ^ epsilon) X P ev)
  unfold frozenSurvivorUpperAbsoluteInvoice
  calc
    _ ≤ ∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
          |frozenSurvivorUpperPrimeCoefficient
            delta n e q om N cap w epsilon X P| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro P _
      exact hterm P

/-- A physical residual invoice with its LOWER source explicitly
subtracted ONCE, so no upper/lower double billing is licensed.
The remaining numerical o(H_N) task is still open. -/
theorem abs_physical_stopped_after_lower_le_frozen_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    |(rawStopped e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X (receiverTest N) -
        licensedStopped delta n e q om N cap w
          ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X (receiverTest N)) -
      actualFixedSignedFifthTail delta n e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X (lowerHalfReceiver N)| ≤
    frozenSurvivorUpperAbsoluteInvoice
      delta n e q om N cap w epsilon X := by
  rw [actual_physical_stopped_eq_frozen_survivors_plus_lower
    delta n e q om N cap w epsilon X he hN heps hX]
  have hc :
      ((∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
        frozenSurvivorUpperPrimeCoefficient
          delta n e q om N cap w epsilon X P) +
        actualFixedSignedFifthTail delta n e q om N cap w
          ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X (lowerHalfReceiver N)) -
        actualFixedSignedFifthTail delta n e q om N cap w
          ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X (lowerHalfReceiver N) =
      (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
        frozenSurvivorUpperPrimeCoefficient
          delta n e q om N cap w epsilon X P) := by ring
  rw [hc]
  exact abs_frozen_survivor_upper_prime_sum_le_invoice
    delta n e q om N cap w epsilon X

end
end ImbalancedChen.P4AOriginalFull87FrozenSurvivorInvoice
