import ImbalancedChen.P4AOriginalFull87FullUpperQuotientRoom
import ImbalancedChen.P4AOriginalFull87FrozenSurvivorInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Bridge the ORIGINAL full (SHORT+LONG) upper integer quotient room to the
EXISTING frozen-survivor physical absolute invoice. Both original event
axes stay as Lists: sharedRankFour histories, actualFifthSixthWithoutBoth
events, and each fifth.remainingAfter list. No new producer filter and no
change to RAW/LICENSED policy, beta, occurrence multiplicity or sign.

The bound is finite arithmetic. It is NOT o(H_N), not a PP invocation,
not a new paid reserve and not a compilation certificate.
-/

namespace ImbalancedChen.P4AOriginalFull87SurvivorFullRoomBridge
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87FullUpperQuotientRoom
  (fullUpperQuotientRoom original_full_upper_prime_abs_sum_le_room)
open P4AOriginalFull87FrozenSurvivorInvoice
  (keepFrozenUpperSurvivor frozenSurvivorUpperAbsoluteInvoice
   abs_physical_stopped_after_lower_le_frozen_invoice)
open P4AOriginalFull87StoppedGlobalPrimeLedger
  (upperPrimeFibreTerm upperPrimeFibreEventValue)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect (lowerHalfReceiver)
open P4AOriginalFull87FifthSignedPrimitive (actualFixedSignedFifthTail)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)

/-- Interchange the original prime Finset and an ordered List, without
deduplicating any List occurrence. -/
private theorem prime_list_swap {α : Type*}
    (S : Finset ℕ) (xs : List α) (f : ℕ → α → ℝ) :
    (∑ P ∈ S, (xs.map (fun x => f P x)).sum) =
      (xs.map (fun x => ∑ P ∈ S, f P x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

/-- The two ACTUAL List axes are interchanged with the prime Finset.
Neither list becomes a Finset, so repeated histories/events remain. -/
private theorem prime_two_lists_swap {α β : Type*}
    (S : Finset ℕ) (xs : List α) (ys : α → List β)
    (f : ℕ → α → β → ℝ) :
    (∑ P ∈ S,
      (xs.map (fun x => ((ys x).map (fun y => f P x y)).sum)).sum) =
    (xs.map (fun x =>
      ((ys x).map (fun y => ∑ P ∈ S, f P x y)).sum)).sum := by
  calc
    _ = (xs.map (fun x =>
        ∑ P ∈ S, ((ys x).map (fun y => f P x y)).sum)).sum :=
      prime_list_swap S xs
        (fun P x => ((ys x).map (fun y => f P x y)).sum)
    _ = _ := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro x hx
      exact prime_list_swap S (ys x) (fun P y => f P x y)

/-- Monotonicity of the sum over an ordered List, with all copies. -/
private theorem ordered_map_sum_le {α : Type*}
    (xs : List α) (f g : α → ℝ)
    (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      apply add_le_add
      · exact h x (by simp)
      · apply ih
        intro y hy
        exact h y (by simp [hy])

/-- An actual fifth sign is fixed across its sixth occurrences.
Only the original triangle inequality and the SAME prime carrier
bounds enter. No cap or signed-saving monotonicity is used. -/
private theorem abs_weighted_ordered_prime_sum_le {α : Type*}
    (xs : List α) (S : Finset ℕ) (c : ℝ)
    (f : α → ℕ → ℝ) (room : α → ℝ)
    (hroom : ∀ x ∈ xs, (∑ P ∈ S, |f x P|) ≤ room x) :
    (∑ P ∈ S, |(xs.map (fun x => c * f x P)).sum|) ≤
      |c| * (xs.map room).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : ∀ y ∈ xs, (∑ P ∈ S, |f y P|) ≤ room y := by
        intro y hy
        exact hroom y (by simp [hy])
      have htriangle (P : ℕ) :
          |c * f x P + (xs.map (fun y => c * f y P)).sum| ≤
            |c| * |f x P| +
              |(xs.map (fun y => c * f y P)).sum| := by
        simpa only [abs_mul] using
          (abs_add (c * f x P)
            ((xs.map (fun y => c * f y P)).sum))
      calc
        (∑ P ∈ S,
          |((x :: xs).map (fun y => c * f y P)).sum|) =
          ∑ P ∈ S,
            |c * f x P + (xs.map (fun y => c * f y P)).sum| := by
              simp only [List.map_cons, List.sum_cons]
        _ ≤ ∑ P ∈ S,
          (|c| * |f x P| +
            |(xs.map (fun y => c * f y P)).sum|) := by
              apply Finset.sum_le_sum
              intro P hP
              exact htriangle P
        _ = |c| * (∑ P ∈ S, |f x P|) +
            (∑ P ∈ S, |(xs.map (fun y => c * f y P)).sum|) := by
              simp only [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ |c| * room x + |c| * (xs.map room).sum :=
          add_le_add
            (mul_le_mul_of_nonneg_left (hroom x (by simp)) (abs_nonneg c))
            (ih htail)
        _ = |c| * ((x :: xs).map room).sum := by
          simp only [List.map_cons, List.sum_cons, mul_add]

/-- A cost for one existing stopped event. BOTH and inherited-sixth
constructors are literally zero in upperPrimeFibreEventValue and pay 0.
A one-sided fifth event keeps its exact fifth mass and the ordered list
of complete six-factor modulus rooms. -/
def frozenSurvivorFullRoomEventBill (N X : ℕ) (L : ℝ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      match fifth.kind with
      | .rawOnly | .licensedOnly =>
          |signedTreeCoefficient true fifth.massAfter| *
            (fifth.remainingAfter.map (fun p =>
              ((fullUpperQuotientRoom
                N X L fifth.selectedAfter p).card : ℝ))).sum
      | .both => 0
  | .sixthFromBoth _ _ => 0

/-- On the ORIGINAL strict upper prime carrier, the old two-sided
quotient-room bound applies without adding a prime-distribution lemma.
Every nonzero upperPrimeFibreTerm already satisfies 2P<N. -/
private theorem original_strict_prime_abs_le_full_room
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
      |upperPrimeFibreTerm N cap w L X P pre p|) ≤
      ((fullUpperQuotientRoom N X L pre p).card : ℝ) := by
  have hs :
      (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
        |upperPrimeFibreTerm N cap w L X P pre p|) =
      (∑ P ∈ chenPrimePrefix N,
        |upperPrimeFibreTerm N cap w L X P pre p|) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hh : 2 * P < N
    · simp [hh]
    · simp [hh, upperPrimeFibreTerm]
  rw [hs]
  exact original_full_upper_prime_abs_sum_le_room
    N cap w L X pre p

/-- Cost of one ORIGINAL fifth/sixth event, before any summation over
real sharedRankFour parents. Raw and licensed signs remain attached to
the same stopped fifth. Inherited BOTH is not erroneously masked. -/
theorem original_upper_event_prime_abs_le_full_room
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (ev : FifthSixthStoppedEvent ℕ) :
    (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
      |upperPrimeFibreEventValue N cap w L X P ev|) ≤
      frozenSurvivorFullRoomEventBill N X L ev := by
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [upperPrimeFibreEventValue, frozenSurvivorFullRoomEventBill]
  | fifthExclusive fifth =>
      have hweight :
          (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
            |(fifth.remainingAfter.map (fun p =>
              signedTreeCoefficient true fifth.massAfter *
                upperPrimeFibreTerm N cap w L X P
                  fifth.selectedAfter p)).sum|) ≤
          |signedTreeCoefficient true fifth.massAfter| *
            (fifth.remainingAfter.map (fun p =>
              ((fullUpperQuotientRoom N X L
                fifth.selectedAfter p).card : ℝ))).sum := by
        exact abs_weighted_ordered_prime_sum_le
          fifth.remainingAfter
          ((chenPrimePrefix N).filter (fun P => 2 * P < N))
          (signedTreeCoefficient true fifth.massAfter)
          (fun p P => upperPrimeFibreTerm N cap w L X P
            fifth.selectedAfter p)
          (fun p => ((fullUpperQuotientRoom N X L
            fifth.selectedAfter p).card : ℝ))
          (fun p hp => original_strict_prime_abs_le_full_room
            N cap w L X fifth.selectedAfter p)
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [upperPrimeFibreEventValue,
            frozenSurvivorFullRoomEventBill, hk] using hweight
      | licensedOnly =>
          simpa [upperPrimeFibreEventValue,
            frozenSurvivorFullRoomEventBill, hk, abs_neg] using hweight
      | both =>
          simp [upperPrimeFibreEventValue,
            frozenSurvivorFullRoomEventBill, hk]

/-- SAME actual producer and survivor selector as the preceding
physical invoice. No new mask on RAW/LICENSED and no List-to-Finset
conversion along either event axis. This finite nonnegative room bill
REPLACES, rather than supplements, the upper absolute invoice. -/
def frozenSurvivorUpperFullRoomInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N
          ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (frozenSurvivorFullRoomEventBill N X ((N : ℝ) ^ epsilon))).sum)).sum

/-- The existing surviving physical absolute bill is controlled
by the full two-sided quotient-room bill, with exact same parents,
fifth signs, ordered sixth occurrences and actual strict prime prefix.
No analytical estimate of the right-hand side is claimed. -/
theorem frozen_survivor_upper_abs_invoice_le_full_room
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) :
    frozenSurvivorUpperAbsoluteInvoice
      delta n e q om N cap w epsilon X ≤
    frozenSurvivorUpperFullRoomInvoice
      delta n e q om N cap w epsilon X := by
  let S : Finset ℕ :=
    (chenPrimePrefix N).filter (fun P => 2 * P < N)
  let states :=
    sharedRankFour e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
  let events := fun state =>
    (actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N
          ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)
  change
    (∑ P ∈ S, (states.map (fun state =>
      ((events state).map (fun ev =>
        |upperPrimeFibreEventValue N cap w
          ((N : ℝ) ^ epsilon) X P ev|)).sum)).sum) ≤
    (states.map (fun state =>
      ((events state).map
        (frozenSurvivorFullRoomEventBill
          N X ((N : ℝ) ^ epsilon))).sum)).sum
  rw [prime_two_lists_swap S states events
    (fun P _ ev =>
      |upperPrimeFibreEventValue N cap w
        ((N : ℝ) ^ epsilon) X P ev|)]
  apply ordered_map_sum_le
  intro state hstate
  apply ordered_map_sum_le
  intro ev hev
  exact original_upper_event_prime_abs_le_full_room
    N cap w ((N : ℝ) ^ epsilon) X ev

/-- Consequence for the REAL stopped RAW-minus-LICENSED difference.
The lower-half receiver is subtracted ONCE; this replaces the older
upper absolute bill, and does not imply any o(H_N) reserve payment. -/
theorem abs_physical_stopped_after_lower_le_full_room_invoice
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
    frozenSurvivorUpperFullRoomInvoice
      delta n e q om N cap w epsilon X := by
  exact (abs_physical_stopped_after_lower_le_frozen_invoice
    delta n e q om N cap w epsilon X he hN heps hX).trans
      (frozen_survivor_upper_abs_invoice_le_full_room
        delta n e q om N cap w epsilon X)

end
end ImbalancedChen.P4AOriginalFull87SurvivorFullRoomBridge
