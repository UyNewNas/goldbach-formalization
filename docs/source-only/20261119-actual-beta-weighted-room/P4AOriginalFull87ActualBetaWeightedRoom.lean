import ImbalancedChen.P4AOriginalFull87ActualPrimitiveRosserRoom
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The previous primitive Rosser room card bound discards the value of the
ORIGINAL PLUS beta. Replace it with the literal sum of absolute PLUS
weights on precisely the same complete-modulus integer quotient room.
The argument injects the actual nonzero original prime fibre, not an
invented or deduplicated event source. An accompanying exact identity
shows that the coprimality filter in the old primitive room is ALREADY
automatic on a genuine rough sixth history: it must not be advertised
as an additional quantitative saving.

This is a finite, nonnegative ABSOLUTE upper invoice, NOT a signed mean,
an asymptotic payment, an external PP, or a compiler certificate.
-/

namespace ImbalancedChen.P4AOriginalFull87ActualBetaWeightedRoom
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87ActualPrimitiveRosserRoom
  (actualPrimitiveRosserRoom original_rough_upper_nonzero_in_primitive_room
   frozenSurvivorActualPrimitiveRosserRoomInvoice)
open P4AOriginalFull87FullUpperQuotientRoom (fullUpperQuotientRoom)
open P4AOriginalFull87StoppedUpperHalfCoprimeUnmask
  (original_full_modulus_coprime_target)
open P4AOriginalFull87PlusBetaPowerFilter (largeFifthRosserIndices)
open P4AOriginalFull87StoppedGlobalPrimeLedger
  (upperPrimeFibreTerm upperPrimeFibreEventValue)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_event_joined_history_original_rough)
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

/-- On the ACTUAL rough sixth suffix, the old full-modulus coprimality
condition is automatic once an integer a has the genuine PLUS support.
Thus this condition alone cannot yield a strict numerical saving. -/
theorem actual_primitive_room_eq_plus_support_of_rough
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hrough : ∀ r ∈ p :: pre, r ∈ roughPrimeUniverse N cap w z) :
    actualPrimitiveRosserRoom N cap w L X pre p =
      (fullUpperQuotientRoom N X L pre p).filter
        (fun a => a ∈ largeFifthRosserIndices N cap w X pre) := by
  ext a
  simp only [actualPrimitiveRosserRoom, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · intro h
    exact ⟨h.1, ⟨h.2, original_full_modulus_coprime_target
      N cap w z X pre p a h.2 hrough⟩⟩

/-- The full ORIGINAL Rosser beta stays attached to its original
integer a; zero coefficients contribute zero, without another filter. -/
def betaWeightedPrimitiveRoom
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) : ℝ :=
  ∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
    |actualSmallRosserPlus N cap w L a|

/-- A weighted bill can never exceed the old unweighted cardinality.
This is NOT a signed-saving monotonicity assertion. -/
theorem beta_weighted_room_le_primitive_card
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    betaWeightedPrimitiveRoom N cap w L X pre p ≤
      ((actualPrimitiveRosserRoom N cap w L X pre p).card : ℝ) := by
  unfold betaWeightedPrimitiveRoom
  calc
    (∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
       |actualSmallRosserPlus N cap w L a|) ≤
      ∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
        (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          exact actualSmallRosserPlus_abs_le_one N cap w L a
    _ = _ := by simp

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

/-- A genuinely nonzero original fibre also has nonzero original PLUS
coefficient; the numerical room is not replaced by a Boolean proxy. -/
theorem original_nonzero_upper_plus_weight
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hnon : upperPrimeFibreTerm N cap w L X P pre p ≠ 0) :
    actualSmallRosserPlus N cap w L
      ((N - P) / (p :: pre).prod) ≠ 0 := by
  unfold upperPrimeFibreTerm at hnon
  split_ifs at hnon with hgate
  · exact hnon
  · contradiction

/-- Prime-to-quotient injection with the SAME original PLUS absolute
weight, rather than replacing every nonzero beta by 1. -/
theorem original_rough_upper_prime_abs_sum_le_beta_weighted_room
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hrough : ∀ r ∈ p :: pre, r ∈ roughPrimeUniverse N cap w z) :
    (∑ P ∈ chenPrimePrefix N,
      |upperPrimeFibreTerm N cap w L X P pre p|) ≤
      betaWeightedPrimitiveRoom N cap w L X pre p := by
  classical
  let b : ℕ := (p :: pre).prod
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
        _ = f Q * b := congrArg (fun a : ℕ => a * b) heq
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
  have heqval (P : ℕ) (hP : P ∈ W) :
      |upperPrimeFibreTerm N cap w L X P pre p| =
      |actualSmallRosserPlus N cap w L (f P)| := by
    have hg := full_upper_nonzero_gate N cap w L X P pre p
      (Finset.mem_filter.mp hP).2
    simp [upperPrimeFibreTerm, hg, f, b]
  have himage :
      (∑ a ∈ W.image f, |actualSmallRosserPlus N cap w L a|) =
      (∑ P ∈ W, |actualSmallRosserPlus N cap w L (f P)|) := by
    exact Finset.sum_image (fun P hP Q hQ heq => hinj hP hQ heq)
  rw [hsupport]
  calc
    (∑ P ∈ W, |upperPrimeFibreTerm N cap w L X P pre p|) =
      ∑ P ∈ W, |actualSmallRosserPlus N cap w L (f P)| := by
        apply Finset.sum_congr rfl
        intro P hP
        exact heqval P hP
    _ = ∑ a ∈ W.image f, |actualSmallRosserPlus N cap w L a| :=
      himage.symm
    _ ≤ ∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
        |actualSmallRosserPlus N cap w L a| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro a ha hnot
      exact abs_nonneg _
    _ = betaWeightedPrimitiveRoom N cap w L X pre p := rfl

private theorem prime_list_swap {α : Type*}
    (S : Finset ℕ) (xs : List α) (f : ℕ → α → ℝ) :
    (∑ P ∈ S, (xs.map (fun x => f P x)).sum) =
      (xs.map (fun x => ∑ P ∈ S, f P x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

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

/-- Literal fifth sign, real sixth List and true beta weighted room. -/
def betaWeightedPrimitiveEventBill
    (N cap : ℕ) (w L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      match fifth.kind with
      | .rawOnly | .licensedOnly =>
          |signedTreeCoefficient true fifth.massAfter| *
            (fifth.remainingAfter.map (fun p =>
              betaWeightedPrimitiveRoom N cap w L X
                fifth.selectedAfter p)).sum
      | .both => 0
  | .sixthFromBoth _ _ => 0

theorem actual_upper_event_abs_le_beta_weighted_room
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth delta n e q om N cap w
      L X (receiverTest N) state) :
    (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
      |upperPrimeFibreEventValue N cap w L X P ev|) ≤
      betaWeightedPrimitiveEventBill N cap w L X ev := by
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [upperPrimeFibreEventValue, betaWeightedPrimitiveEventBill]
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
          betaWeightedPrimitiveRoom N cap w L X fifth.selectedAfter p := by
        have hrough : ∀ r ∈ p :: fifth.selectedAfter,
            r ∈ roughPrimeUniverse N cap w z := by
          intro r hr
          rcases List.mem_cons.mp hr with hpr | hpre
          · subst r
            exact hjoined.subset (List.mem_append.mpr (Or.inr hp))
          · have hrev : r ∈ fifth.selectedAfter.reverse := by
              simpa using hpre
            exact hjoined.subset (List.mem_append.mpr (Or.inl hrev))
        have hall := original_rough_upper_prime_abs_sum_le_beta_weighted_room
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
        (fun p => betaWeightedPrimitiveRoom N cap w L X
          fifth.selectedAfter p) hroom
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [upperPrimeFibreEventValue, betaWeightedPrimitiveEventBill,
            hk] using hweight
      | licensedOnly =>
          simpa [upperPrimeFibreEventValue, betaWeightedPrimitiveEventBill,
            hk, abs_neg] using hweight
      | both =>
          simp [upperPrimeFibreEventValue, betaWeightedPrimitiveEventBill, hk]

/-- The same states, true event Lists and post-generation survivor mask. -/
def frozenSurvivorBetaWeightedRoomInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N
          ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (betaWeightedPrimitiveEventBill N cap w ((N : ℝ) ^ epsilon) X)).sum)).sum

theorem frozen_survivor_upper_abs_le_beta_weighted_room
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) :
    frozenSurvivorUpperAbsoluteInvoice
      delta n e q om N cap w epsilon X ≤
    frozenSurvivorBetaWeightedRoomInvoice
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
        (betaWeightedPrimitiveEventBill N cap w
          ((N : ℝ) ^ epsilon) X)).sum)).sum
  rw [prime_two_lists_swap S states events
    (fun P _ ev =>
      |upperPrimeFibreEventValue N cap w
        ((N : ℝ) ^ epsilon) X P ev|)]
  apply ordered_map_sum_le
  intro state hstate
  apply ordered_map_sum_le
  intro ev hev
  exact actual_upper_event_abs_le_beta_weighted_room
    delta n e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
    ((N : ℝ) ^ epsilon) X state hstate ev
    (List.mem_of_mem_filter hev)

/-- Weighted improvement is nonnegative bill monotonicity ONLY. -/
theorem beta_weighted_event_bill_le_old_primitive
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (ev : FifthSixthStoppedEvent ℕ) :
    betaWeightedPrimitiveEventBill N cap w L X ev ≤
      P4AOriginalFull87ActualPrimitiveRosserRoom.actualPrimitiveRosserEventBill
        N cap w L X ev := by
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [betaWeightedPrimitiveEventBill,
        P4AOriginalFull87ActualPrimitiveRosserRoom.actualPrimitiveRosserEventBill]
  | fifthExclusive fifth =>
      have hs :
          (fifth.remainingAfter.map (fun p =>
            betaWeightedPrimitiveRoom N cap w L X fifth.selectedAfter p)).sum ≤
          (fifth.remainingAfter.map (fun p =>
            ((actualPrimitiveRosserRoom N cap w L X
              fifth.selectedAfter p).card : ℝ))).sum := by
        apply ordered_map_sum_le
        intro p hp
        exact beta_weighted_room_le_primitive_card N cap w L X
          fifth.selectedAfter p
      have hw := mul_le_mul_of_nonneg_left hs
        (abs_nonneg (signedTreeCoefficient true fifth.massAfter))
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [betaWeightedPrimitiveEventBill,
            P4AOriginalFull87ActualPrimitiveRosserRoom.actualPrimitiveRosserEventBill,
            hk] using hw
      | licensedOnly =>
          simpa [betaWeightedPrimitiveEventBill,
            P4AOriginalFull87ActualPrimitiveRosserRoom.actualPrimitiveRosserEventBill,
            hk] using hw
      | both =>
          simp [betaWeightedPrimitiveEventBill,
            P4AOriginalFull87ActualPrimitiveRosserRoom.actualPrimitiveRosserEventBill,
            hk]

theorem frozen_survivor_beta_weighted_le_old_primitive
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) :
    frozenSurvivorBetaWeightedRoomInvoice delta n e q om N cap w epsilon X ≤
    frozenSurvivorActualPrimitiveRosserRoomInvoice
      delta n e q om N cap w epsilon X := by
  unfold frozenSurvivorBetaWeightedRoomInvoice
    frozenSurvivorActualPrimitiveRosserRoomInvoice
  apply ordered_map_sum_le
  intro state hstate
  apply ordered_map_sum_le
  intro ev hev
  exact beta_weighted_event_bill_le_old_primitive
    N cap w ((N : ℝ) ^ epsilon) X ev

/-- Original RAW minus LICENSED after ONE lower subtraction.
The new beta-sensitive bill REPLACES the old upper bill. -/
theorem abs_physical_stopped_after_lower_le_beta_weighted
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
    frozenSurvivorBetaWeightedRoomInvoice
      delta n e q om N cap w epsilon X := by
  exact (abs_physical_stopped_after_lower_le_frozen_invoice
    delta n e q om N cap w epsilon X he hN heps hX).trans
    (frozen_survivor_upper_abs_le_beta_weighted_room
      delta n e q om N cap w epsilon X)

end
end ImbalancedChen.P4AOriginalFull87ActualBetaWeightedRoom
