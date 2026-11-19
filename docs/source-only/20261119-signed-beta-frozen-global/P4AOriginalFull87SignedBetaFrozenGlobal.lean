import ImbalancedChen.P4AOriginalFull87SignedBetaMissingRoom
import ImbalancedChen.P4AOriginalFull87FrozenSurvivorInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Push the actual fifth-exclusive signed beta identity through the ORIGINAL
RAW-only/LICENSED-only event signs, then the ORIGINAL frozen ordered
sharedRankFour states and post-generated fifth/sixth survivor events.
The missing signed Rosser room is NOT small by construction.
-/ 
namespace ImbalancedChen.P4AOriginalFull87SignedBetaFrozenGlobal
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SignedBetaMissingRoom
  (unoccupiedOriginalUpperBetaQuotients
   actual_parent_fifth_signed_beta_room_partition)
open P4AOriginalFull87ActualPrimitiveRosserRoom (actualPrimitiveRosserRoom)
open P4AOriginalFull87StoppedGlobalPrimeLedger
  (upperPrimeFibreTerm upperPrimeFibreEventValue
   upper_prime_fibre_event_zero_outside_half)
open P4AOriginalFull87FrozenSurvivorInvoice
  (keepFrozenUpperSurvivor frozenSurvivorUpperPrimeCoefficient
   actual_physical_stopped_eq_frozen_survivors_plus_lower)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87FifthSignedPrimitive (actualFixedSignedFifthTail)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect (lowerHalfReceiver)

/-- Literal PLUS-beta room, signed by the actual fifth-admission tag.
Both and inherited sixth are zero here only as in upperPrimeFibreEventValue. -/
def originalSignedFullBetaEvent
    (N cap : ℕ) (w L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      let v : ℝ := (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          (∑ a ∈ actualPrimitiveRosserRoom N cap w L X
            fifth.selectedAfter p, actualSmallRosserPlus N cap w L a))).sum
      match fifth.kind with
      | .rawOnly => v
      | .licensedOnly => -v
      | .both => 0
  | .sixthFromBoth _ _ => 0

/-- Literal unoccupied signed PLUS-beta room on the same event. -/
def originalSignedMissingBetaEvent
    (N cap : ℕ) (w L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      let v : ℝ := (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          (∑ a ∈ unoccupiedOriginalUpperBetaQuotients N cap w L X
            fifth.selectedAfter p, actualSmallRosserPlus N cap w L a))).sum
      match fifth.kind with
      | .rawOnly => v
      | .licensedOnly => -v
      | .both => 0
  | .sixthFromBoth _ _ => 0

private theorem prime_list_swap {α : Type*}
    (S : Finset ℕ) (xs : List α) (f : ℕ → α → ℝ) :
    (∑ P ∈ S, (xs.map (fun x => f P x)).sum) =
    (xs.map (fun x => ∑ P ∈ S, f P x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

private theorem list_sum_difference {α : Type*}
    (xs : List α) (f g h : α → ℝ)
    (heq : ∀ x ∈ xs, f x = g x - h x) :
    (xs.map f).sum = (xs.map g).sum - (xs.map h).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := heq x (by simp)
      have ht : ∀ y ∈ xs, f y = g y - h y := by
        intro y hy
        exact heq y (by simp [hy])
      simp only [List.map_cons, List.sum_cons]
      rw [hx, ih ht]
      ring

/-- The actual fifth ordered sixth List commutes with the same prime
Finset; no occurrence is converted into a Finset. -/
private theorem fifth_prime_swap
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) :
    (∑ P ∈ chenPrimePrefix N,
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
        upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)).sum) =
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
      (∑ P ∈ chenPrimePrefix N,
        upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p))).sum := by
  calc
    _ = (fifth.remainingAfter.map (fun p =>
          ∑ P ∈ chenPrimePrefix N,
            signedTreeCoefficient true fifth.massAfter *
              upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)).sum :=
      prime_list_swap (chenPrimePrefix N) fifth.remainingAfter
        (fun P p => signedTreeCoefficient true fifth.massAfter *
          upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)
    _ = _ := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro p _
      rw [Finset.mul_sum]

/-- Prime-sum form of the preceding actual-parent fifth proof. -/
private theorem actual_fifth_prime_difference
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hev : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w
        L X (receiverTest N) state) :
    (∑ P ∈ chenPrimePrefix N,
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
        upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)).sum) =
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        (∑ a ∈ actualPrimitiveRosserRoom N cap w L X
          fifth.selectedAfter p, actualSmallRosserPlus N cap w L a))).sum -
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        (∑ a ∈ unoccupiedOriginalUpperBetaQuotients N cap w L X
          fifth.selectedAfter p, actualSmallRosserPlus N cap w L a))).sum := by
  rw [fifth_prime_swap]
  exact actual_parent_fifth_signed_beta_room_partition
    delta n e q om N cap w z L X state hs fifth hev

/-- Genuine tagged original event: RAW takes plus, LICENSED minus.
No invented fifth branch is used for inherited sixth. -/
theorem actual_event_signed_beta_full_sub_missing
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth delta n e q om
      N cap w L X (receiverTest N) state) :
    (∑ P ∈ chenPrimePrefix N,
      upperPrimeFibreEventValue N cap w L X P ev) =
    originalSignedFullBetaEvent N cap w L X ev -
    originalSignedMissingBetaEvent N cap w L X ev := by
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [upperPrimeFibreEventValue,
        originalSignedFullBetaEvent, originalSignedMissingBetaEvent]
  | fifthExclusive fifth =>
      have h := actual_fifth_prime_difference
        delta n e q om N cap w z L X state hs fifth hev
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [upperPrimeFibreEventValue, originalSignedFullBetaEvent,
            originalSignedMissingBetaEvent, hk] using h
      | licensedOnly =>
          have hneg :
              (∑ P ∈ chenPrimePrefix N,
                -((fifth.remainingAfter.map (fun p =>
                  signedTreeCoefficient true fifth.massAfter *
                  upperPrimeFibreTerm N cap w L X P
                    fifth.selectedAfter p)).sum)) =
              -((fifth.remainingAfter.map (fun p =>
                signedTreeCoefficient true fifth.massAfter *
                (∑ a ∈ actualPrimitiveRosserRoom N cap w L X
                  fifth.selectedAfter p,
                  actualSmallRosserPlus N cap w L a))).sum) -
              -((fifth.remainingAfter.map (fun p =>
                signedTreeCoefficient true fifth.massAfter *
                (∑ a ∈ unoccupiedOriginalUpperBetaQuotients N cap w L X
                  fifth.selectedAfter p,
                  actualSmallRosserPlus N cap w L a))).sum) := by
            rw [Finset.sum_neg_distrib, h]
            ring
          simpa [upperPrimeFibreEventValue, originalSignedFullBetaEvent,
            originalSignedMissingBetaEvent, hk] using hneg
      | both =>
          simp [upperPrimeFibreEventValue, originalSignedFullBetaEvent,
            originalSignedMissingBetaEvent, hk]

private theorem strict_upper_event_sum
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (ev : FifthSixthStoppedEvent ℕ) :
    (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
      upperPrimeFibreEventValue N cap w L X P ev) =
    ∑ P ∈ chenPrimePrefix N,
      upperPrimeFibreEventValue N cap w L X P ev := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P _
  by_cases hh : 2 * P < N
  · simp [hh]
  · simp [hh, upper_prime_fibre_event_zero_outside_half
      N cap w L X P hh ev]

/-- Same actual frozen parent and post-generated event selector. -/
def frozenSurvivorSignedFullBetaRoom
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (originalSignedFullBetaEvent N cap w ((N : ℝ) ^ epsilon) X)).sum)).sum

/-- Signed unoccupied complement on identical original occurrences. -/
def frozenSurvivorSignedMissingBetaRoom
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (originalSignedMissingBetaEvent N cap w ((N : ℝ) ^ epsilon) X)).sum)).sum

/-- Exact signed frozen global prime difference, on actual parent and
event Lists, not a replacement producer or an asymptotic estimate. -/
theorem frozen_survivor_signed_prime_eq_full_sub_missing
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) :
    (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
      frozenSurvivorUpperPrimeCoefficient
        delta n e q om N cap w epsilon X P) =
    frozenSurvivorSignedFullBetaRoom delta n e q om N cap w epsilon X -
    frozenSurvivorSignedMissingBetaRoom delta n e q om N cap w epsilon X := by
  let S : Finset ℕ := (chenPrimePrefix N).filter (fun P => 2 * P < N)
  let states :=
    sharedRankFour e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
  let events := fun state =>
    (actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)
  let room := originalSignedFullBetaEvent N cap w ((N : ℝ) ^ epsilon) X
  let missing := originalSignedMissingBetaEvent N cap w ((N : ℝ) ^ epsilon) X
  have hevent (state : FirstExitDepthState ℕ)
      (hs : state ∈ states) (ev : FifthSixthStoppedEvent ℕ)
      (hev : ev ∈ events state) :
      (∑ P ∈ S,
        upperPrimeFibreEventValue N cap w ((N : ℝ) ^ epsilon) X P ev) =
      room ev - missing ev := by
    rw [strict_upper_event_sum]
    exact actual_event_signed_beta_full_sub_missing
      delta n e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
      ((N : ℝ) ^ epsilon) X state hs ev
      (List.mem_of_mem_filter hev)
  have hper (state : FirstExitDepthState ℕ) (hs : state ∈ states) :
      (∑ P ∈ S, ((events state).map (fun ev =>
        upperPrimeFibreEventValue N cap w
          ((N : ℝ) ^ epsilon) X P ev)).sum) =
      ((events state).map room).sum -
      ((events state).map missing).sum := by
    rw [prime_list_swap S (events state)
      (fun P ev => upperPrimeFibreEventValue N cap w
        ((N : ℝ) ^ epsilon) X P ev)]
    exact list_sum_difference (events state)
      (fun ev => ∑ P ∈ S, upperPrimeFibreEventValue N cap w
        ((N : ℝ) ^ epsilon) X P ev)
      room missing (hevent state hs)
  change
    (∑ P ∈ S, (states.map (fun state =>
      ((events state).map (fun ev =>
        upperPrimeFibreEventValue N cap w
          ((N : ℝ) ^ epsilon) X P ev)).sum)).sum) =
    (states.map (fun state => ((events state).map room).sum)).sum -
    (states.map (fun state => ((events state).map missing).sum)).sum
  calc
    _ = (states.map (fun state =>
          ∑ P ∈ S, ((events state).map (fun ev =>
            upperPrimeFibreEventValue N cap w
              ((N : ℝ) ^ epsilon) X P ev)).sum)).sum :=
      prime_list_swap S states (fun P state =>
        ((events state).map (fun ev =>
          upperPrimeFibreEventValue N cap w
            ((N : ℝ) ^ epsilon) X P ev)).sum)
    _ = (states.map (fun state =>
          ((events state).map room).sum -
          ((events state).map missing).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro state hs
      exact hper state hs
    _ = _ := list_sum_difference states
      (fun state => ((events state).map room).sum -
        ((events state).map missing).sum)
      (fun state => ((events state).map room).sum)
      (fun state => ((events state).map missing).sum)
      (fun state _ => rfl)

/-- A single lower subtraction, with the real physical RAW-LICENSED
source. There is no additional reserve and no signed-saving claim. -/
theorem physical_stopped_after_lower_eq_signed_beta_difference
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    (rawStopped e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
      ((N : ℝ) ^ epsilon) X (receiverTest N) -
     licensedStopped delta n e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))
      ((N : ℝ) ^ epsilon) X (receiverTest N)) -
     actualFixedSignedFifthTail delta n e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))
      ((N : ℝ) ^ epsilon) X (lowerHalfReceiver N) =
    frozenSurvivorSignedFullBetaRoom delta n e q om N cap w epsilon X -
    frozenSurvivorSignedMissingBetaRoom delta n e q om N cap w epsilon X := by
  rw [actual_physical_stopped_eq_frozen_survivors_plus_lower
    delta n e q om N cap w epsilon X he hN heps hX]
  rw [show
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
        delta n e q om N cap w epsilon X P) by ring]
  exact frozen_survivor_signed_prime_eq_full_sub_missing
    delta n e q om N cap w epsilon X

end
end ImbalancedChen.P4AOriginalFull87SignedBetaFrozenGlobal
