import ImbalancedChen.P4AOriginalFull87CentreLeafPrimitiveInvoice
import ImbalancedChen.P4AOriginalFull87SurvivorFullRoomBridge
import ImbalancedChen.P4AOriginalFull87FullUpperQuotientRoom
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Refine the real rough fifth/sixth upper quotient interval with the ACTUAL
PLUS Rosser index filter and coprimality of the entire six-factor modulus.
The absolute global budget uses the same rank-four producer, same ordered
event and suffix lists, same signed coefficient and same frozen survivor
selector. No analytic asymptotic, PP, or reserve payment is claimed.
-/

namespace ImbalancedChen.P4AOriginalFull87ActualPrimitiveRosserRoom
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87FullUpperQuotientRoom
  (fullUpperQuotientRoom original_full_upper_nonzero_in_quotient_room
   original_full_upper_prime_fibre_abs_le_one)
open P4AOriginalFull87StoppedUpperHalfCoprimeUnmask
  (original_full_modulus_coprime_target)
open P4AOriginalFull87StoppedGlobalPrimeLedger
  (upperPrimeFibreTerm upperPrimeFibreEventValue)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_event_joined_history_original_rough)
open P4AOriginalFull87PlusBetaPowerFilter (largeFifthRosserIndices)
open P4AOriginalFull87SurvivorFullRoomBridge
  (frozenSurvivorUpperFullRoomInvoice)
open P4AOriginalFull87FrozenSurvivorInvoice
  (keepFrozenUpperSurvivor frozenSurvivorUpperAbsoluteInvoice
   abs_physical_stopped_after_lower_le_frozen_invoice)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect (lowerHalfReceiver)
open P4AOriginalFull87FifthSignedPrimitive (actualFixedSignedFifthTail)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)

/-- Full upper integer interval restricted by *the real* PLUS Rosser
admission and coprimality of the COMPLETE six-factor arithmetic modulus. -/
def actualPrimitiveRosserRoom (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) : Finset ℕ :=
  (fullUpperQuotientRoom N X L pre p).filter (fun a =>
    a ∈ largeFifthRosserIndices N cap w X pre ∧
      Nat.Coprime (a * (p :: pre).prod) N)

theorem actual_primitive_room_subset_full
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    actualPrimitiveRosserRoom N cap w L X pre p ⊆
      fullUpperQuotientRoom N X L pre p := by
  exact Finset.filter_subset _ _

private theorem full_upper_nonzero_gate
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hnon : upperPrimeFibreTerm N cap w L X P pre p ≠ 0) :
    2 * P < N ∧ X < N - P ∧
      (N - P) / (p :: pre).prod ∈
        largeFifthRosserIndices N cap w X pre ∧
      ((N - P) / (p :: pre).prod) * (p :: pre).prod = N - P := by
  unfold upperPrimeFibreTerm at hnon
  split_ifs at hnon with hgate
  · exact hgate
  · contradiction

/-- This necessary condition is obtained from the actual rough history,
not assumed of an arbitrary unsigned integer room. -/
theorem original_rough_upper_nonzero_in_primitive_room
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hrough : ∀ r ∈ p :: pre, r ∈ roughPrimeUniverse N cap w z)
    (hnon : upperPrimeFibreTerm N cap w L X P pre p ≠ 0) :
    (N - P) / (p :: pre).prod ∈
      actualPrimitiveRosserRoom N cap w L X pre p := by
  have hg := full_upper_nonzero_gate N cap w L X P pre p hnon
  have hc : Nat.Coprime
      (((N - P) / (p :: pre).prod) * (p :: pre).prod) N :=
    original_full_modulus_coprime_target N cap w z X pre p
      ((N - P) / (p :: pre).prod) hg.2.2.1 hrough
  exact Finset.mem_filter.mpr
    ⟨original_full_upper_nonzero_in_quotient_room
       N cap w L X P pre p hnon, hg.2.2.1, hc⟩

/-- For fixed genuine fifth history and sixth occurrence, P is
injectively represented by its exact integer quotient a=(N-P)/b. -/
theorem original_rough_upper_prime_abs_sum_le_primitive_room
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hrough : ∀ r ∈ p :: pre, r ∈ roughPrimeUniverse N cap w z) :
    (∑ P ∈ chenPrimePrefix N,
      |upperPrimeFibreTerm N cap w L X P pre p|) ≤
      ((actualPrimitiveRosserRoom N cap w L X pre p).card : ℝ) := by
  classical
  let b := (p :: pre).prod
  let W : Finset ℕ := (chenPrimePrefix N).filter
    (fun P => upperPrimeFibreTerm N cap w L X P pre p ≠ 0)
  let f : ℕ → ℕ := fun P => (N - P) / b
  have hinj : Set.InjOn f W := by
    intro P hP Q hQ heq
    have hp := full_upper_nonzero_gate N cap w L X P pre p
      (Finset.mem_filter.mp hP).2
    have hq := full_upper_nonzero_gate N cap w L X Q pre p
      (Finset.mem_filter.mp hQ).2
    have hsame : N - P = N - Q := by
      calc
        N - P = f P * b := hp.2.2.2.symm
        _ = f Q * b := congrArg (fun t : ℕ => t * b) heq
        _ = N - Q := hq.2.2.2
    omega
  have hsubset : W.image f ⊆
      actualPrimitiveRosserRoom N cap w L X pre p := by
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp ha
    exact original_rough_upper_nonzero_in_primitive_room
      N cap w z L X P pre p hrough (Finset.mem_filter.mp hP).2
  have hsupport :
      (∑ P ∈ chenPrimePrefix N,
        |upperPrimeFibreTerm N cap w L X P pre p|) =
      ∑ P ∈ W, |upperPrimeFibreTerm N cap w L X P pre p| := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hz : upperPrimeFibreTerm N cap w L X P pre p = 0
    · simp [hz]
    · simp [hz]
  rw [hsupport]
  calc
    (∑ P ∈ W, |upperPrimeFibreTerm N cap w L X P pre p|) ≤
        ∑ P ∈ W, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro P _
      exact original_full_upper_prime_fibre_abs_le_one
        N cap w L X P pre p
    _ = (W.card : ℝ) := by simp
    _ = ((W.image f).card : ℝ) := by
      rw [Finset.card_image_of_injOn hinj]
    _ ≤ ((actualPrimitiveRosserRoom N cap w L X pre p).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset

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

/-- One original stopped event's primitive PLUS-Rosser absolute room
budget. Keep the fifth mass and every sixth occurrence, including repeats. -/
def actualPrimitiveRosserEventBill
    (N cap : ℕ) (w L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      match fifth.kind with
      | .rawOnly | .licensedOnly =>
          |signedTreeCoefficient true fifth.massAfter| *
            (fifth.remainingAfter.map (fun p =>
              ((actualPrimitiveRosserRoom N cap w L X
                fifth.selectedAfter p).card : ℝ))).sum
      | .both => 0
  | .sixthFromBoth _ _ => 0

/-- Same actual stopped receiver source, not a surrogate producer. -/
theorem original_actual_upper_event_abs_le_primitive_room
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth delta n e q om N cap w
      L X (receiverTest N) state) :
    (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
      |upperPrimeFibreEventValue N cap w L X P ev|) ≤
      actualPrimitiveRosserEventBill N cap w L X ev := by
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [upperPrimeFibreEventValue, actualPrimitiveRosserEventBill]
  | fifthExclusive fifth =>
      have hjoined : fifth.selectedAfter.reverse ++ fifth.remainingAfter <+
          roughPrimeUniverse N cap w z := by
        simpa [P4AOriginalFull87OrderedSixthSuffix.eventSelected,
          P4AOriginalFull87ActualSixthSuffix.eventSixthSuffix] using
          (actual_event_joined_history_original_rough delta n e q om
            N cap w z L X (receiverTest N) state hstate
            (.fifthExclusive fifth) hev)
      have hroom (p : ℕ) (hp : p ∈ fifth.remainingAfter) :
          (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
            |upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p|) ≤
          ((actualPrimitiveRosserRoom N cap w L X fifth.selectedAfter p).card : ℝ) := by
        have hrough : ∀ r ∈ p :: fifth.selectedAfter,
            r ∈ roughPrimeUniverse N cap w z := by
          intro r hr
          rcases List.mem_cons.mp hr with hpr | hpre
          · subst r
            exact hjoined.subset (List.mem_append.mpr (Or.inr hp))
          · have hrev : r ∈ fifth.selectedAfter.reverse := by
              simpa using hpre
            exact hjoined.subset (List.mem_append.mpr (Or.inl hrev))
        have hall := original_rough_upper_prime_abs_sum_le_primitive_room
          N cap w z L X fifth.selectedAfter p hrough
        have hstrict :
            (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
              |upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p|) =
            (∑ P ∈ chenPrimePrefix N,
              |upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p|) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro P hP
          by_cases hh : 2 * P < N
          · simp [hh]
          · simp [hh, upperPrimeFibreTerm]
        rw [hstrict]
        exact hall
      have hweight := abs_weighted_ordered_prime_sum_le
        fifth.remainingAfter
        ((chenPrimePrefix N).filter (fun P => 2 * P < N))
        (signedTreeCoefficient true fifth.massAfter)
        (fun p P => upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)
        (fun p => ((actualPrimitiveRosserRoom N cap w L X
          fifth.selectedAfter p).card : ℝ)) hroom
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [upperPrimeFibreEventValue, actualPrimitiveRosserEventBill,
            hk] using hweight
      | licensedOnly =>
          simpa [upperPrimeFibreEventValue, actualPrimitiveRosserEventBill,
            hk, abs_neg] using hweight
      | both =>
          simp [upperPrimeFibreEventValue, actualPrimitiveRosserEventBill, hk]

/-- Original rank-four states and event Lists, unchanged survivor selector. -/
def frozenSurvivorActualPrimitiveRosserRoomInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N
          ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (actualPrimitiveRosserEventBill N cap w ((N : ℝ) ^ epsilon) X)).sum)).sum

theorem frozen_survivor_upper_abs_invoice_le_actual_primitive_room
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) :
    frozenSurvivorUpperAbsoluteInvoice
      delta n e q om N cap w epsilon X ≤
    frozenSurvivorActualPrimitiveRosserRoomInvoice
      delta n e q om N cap w epsilon X := by
  let S : Finset ℕ := (chenPrimePrefix N).filter (fun P => 2 * P < N)
  let states := sharedRankFour e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
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
        (actualPrimitiveRosserEventBill N cap w
          ((N : ℝ) ^ epsilon) X)).sum)).sum
  rw [prime_two_lists_swap S states events
    (fun P _ ev =>
      |upperPrimeFibreEventValue N cap w
        ((N : ℝ) ^ epsilon) X P ev|)]
  apply ordered_map_sum_le
  intro state hstate
  apply ordered_map_sum_le
  intro ev hev
  exact original_actual_upper_event_abs_le_primitive_room
    delta n e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
    ((N : ℝ) ^ epsilon) X state hstate ev
    (List.mem_of_mem_filter hev)

/-- The subroom is non-increasing at every ordered fifth/sixth event. -/
theorem actual_primitive_event_bill_le_full_room
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (ev : FifthSixthStoppedEvent ℕ) :
    actualPrimitiveRosserEventBill N cap w L X ev ≤
      P4AOriginalFull87SurvivorFullRoomBridge.frozenSurvivorFullRoomEventBill
        N X L ev := by
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [actualPrimitiveRosserEventBill,
        P4AOriginalFull87SurvivorFullRoomBridge.frozenSurvivorFullRoomEventBill]
  | fifthExclusive fifth =>
      have hsum :
          (fifth.remainingAfter.map (fun p =>
            ((actualPrimitiveRosserRoom N cap w L X
              fifth.selectedAfter p).card : ℝ))).sum ≤
          (fifth.remainingAfter.map (fun p =>
            ((fullUpperQuotientRoom N X L
              fifth.selectedAfter p).card : ℝ))).sum := by
        apply ordered_map_sum_le
        intro p hp
        exact_mod_cast Finset.card_le_card
          (actual_primitive_room_subset_full N cap w L X fifth.selectedAfter p)
      have hweighted := mul_le_mul_of_nonneg_left hsum
        (abs_nonneg (signedTreeCoefficient true fifth.massAfter))
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [actualPrimitiveRosserEventBill,
            P4AOriginalFull87SurvivorFullRoomBridge.frozenSurvivorFullRoomEventBill,
            hk] using hweighted
      | licensedOnly =>
          simpa [actualPrimitiveRosserEventBill,
            P4AOriginalFull87SurvivorFullRoomBridge.frozenSurvivorFullRoomEventBill,
            hk] using hweighted
      | both =>
          simp [actualPrimitiveRosserEventBill,
            P4AOriginalFull87SurvivorFullRoomBridge.frozenSurvivorFullRoomEventBill, hk]

/-- Actual absolute room bound is a refinement, not a second charge. -/
theorem frozen_survivor_actual_primitive_room_le_full_room
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) :
    frozenSurvivorActualPrimitiveRosserRoomInvoice
      delta n e q om N cap w epsilon X ≤
    frozenSurvivorUpperFullRoomInvoice
      delta n e q om N cap w epsilon X := by
  unfold frozenSurvivorActualPrimitiveRosserRoomInvoice
    frozenSurvivorUpperFullRoomInvoice
  apply ordered_map_sum_le
  intro state hstate
  apply ordered_map_sum_le
  intro ev hev
  exact actual_primitive_event_bill_le_full_room
    N cap w ((N : ℝ) ^ epsilon) X ev

/-- Original RAW-LICENSED physical bill, subtracting lower exactly once. -/
theorem abs_physical_stopped_after_lower_le_actual_primitive_room
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
    frozenSurvivorActualPrimitiveRosserRoomInvoice
      delta n e q om N cap w epsilon X := by
  exact (abs_physical_stopped_after_lower_le_frozen_invoice
    delta n e q om N cap w epsilon X he hN heps hX).trans
    (frozen_survivor_upper_abs_invoice_le_actual_primitive_room
      delta n e q om N cap w epsilon X)

end
end ImbalancedChen.P4AOriginalFull87ActualPrimitiveRosserRoom
