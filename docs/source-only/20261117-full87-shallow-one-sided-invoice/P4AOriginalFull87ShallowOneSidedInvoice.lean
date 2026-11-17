import ImbalancedChen.P4AOriginalFull87RankSevenTerminalPruning
import ImbalancedChen.P4AOriginalFull87SixthBothInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

This is a literal, occurrence-by-occurrence reduction of the EXISTING
fifthSixthWithoutBoth event invoice. On its actual one-sided fifth/sixth
members, replace the original stoppedTest 8 PAYLOAD by stoppedTest 7 at
the SAME selected history, mass, sign and post-query suffix.

No new event population is generated. The old event list is mapped with
a second, computed value, and the two mapped lists are proved equal.
Consequently the old signed and absolute bills are replaced, not added.
The surviving rank-five and rank-six terminal high-q values are NOT zero.
-/

namespace ImbalancedChen.P4AOriginalFull87ShallowOneSidedInvoice
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent firstFifthEvents)
open P4AOriginalFull87FifthSixthStoppedEvents
  (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice
  (fifthSixthWithoutBoth actualFifthSixthWithoutBoth
   actualFifthSixthExclusiveAbsInvoice)
open P4AOriginalFull87RankSevenTerminalPruning
  (actual_one_sided_stopped8_eq_stopped7)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)

/-- Re-evaluate the SAME original one-sided fifth/sixth event at cutoff 7.
The both category is retained unchanged by definition, rather than
silently declared zero. The actual source generator filters it out. -/
def shallowFifthValue (R S : Bool → List ℕ → Bool)
    (T : Bool → List ℕ → ℝ) (ev : FifthStoppedEvent ℕ) : ℝ :=
  match ev.kind with
  | .rawOnly =>
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        ev.selectedAfter ev.positiveAfter ev.massAfter ev.remainingAfter
  | .licensedOnly =>
      -stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        ev.selectedAfter ev.positiveAfter ev.massAfter ev.remainingAfter
  | .both => ev.signedValue

/-- Exact event occurrence and metadata, evaluated with its shallow
literal terminal sum. In particular sixthFromBoth still carries its
original fifth ancestor. -/
def shallowOneSidedValue (R S : Bool → List ℕ → Bool)
    (T : Bool → List ℕ → ℝ) : FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive ev => shallowFifthValue R S T ev
  | .sixthFromBoth _ ev => shallowFifthValue R S T ev

/-- The actual sixth-query event list is filtered ONLY at the former
sixth-BOTH category. The identity is at the List.map level, stronger
than equality of sums: all duplicate occurrences survive in order. -/
private theorem first_filtered_shallow_map
    (R S : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (g : ℝ → ℝ) (pre : List ℕ) (mass : ℝ)
    (remaining : List ℕ)
    (hraw : ∀ p tail,
      stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) true (mass * (1 : ℝ)) tail =
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) true (mass * (1 : ℝ)) tail)
    (hlic : ∀ p tail,
      stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) true (mass * (1 : ℝ)) tail =
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) true (mass * (1 : ℝ)) tail) :
    (((firstFifthEvents R S (fun _ : ℕ => (1 : ℝ))
      T pre false mass remaining).filter
        (fun ev => decide (ev.kind ≠ .both))).map
          (fun ev => g ev.signedValue)) =
    (((firstFifthEvents R S (fun _ : ℕ => (1 : ℝ))
      T pre false mass remaining).filter
        (fun ev => decide (ev.kind ≠ .both))).map
          (fun ev => g (shallowFifthValue R S T ev))) := by
  induction remaining with
  | nil => simp [firstFifthEvents]
  | cons p ps ih =>
      have hr8 := hraw p ps
      have hs8 := hlic p ps
      cases hr : R true (p :: pre) <;>
        cases hs : S true (p :: pre) <;>
        simp [firstFifthEvents, hr, hs, List.filter_append,
          List.map_append, shallowFifthValue, hr8, hs8, ih]

/-- The real fourth-prefix event producer first queries the fifth
candidate, then queries the sixth candidate ONLY in a both-admitted
fifth child. All recursive calls use the original remaining tail. -/
private theorem fourth_one_sided_shallow_map
    (R S : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (g : ℝ → ℝ) (pre : List ℕ) (mass : ℝ)
    (remaining : List ℕ)
    (hraw5 : ∀ p tail,
      stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail =
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail)
    (hlic5 : ∀ p tail,
      stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail =
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail)
    (hraw6 : ∀ p q tail,
      stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail =
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail)
    (hlic6 : ∀ p q tail,
      stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail =
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail) :
    ((fifthSixthWithoutBoth R S (fun _ : ℕ => (1 : ℝ))
      T pre true mass remaining).map
        (fun ev => g ev.signedValue)) =
    ((fifthSixthWithoutBoth R S (fun _ : ℕ => (1 : ℝ))
      T pre true mass remaining).map
        (fun ev => g (shallowOneSidedValue R S T ev))) := by
  induction remaining with
  | nil => simp [fifthSixthWithoutBoth]
  | cons p ps ih =>
      have hinner := first_filtered_shallow_map R S T g
        (p :: pre) (mass * (1 : ℝ)) ps
        (fun q tail => hraw6 p q tail)
        (fun q tail => hlic6 p q tail)
      have hr8 := hraw5 p ps
      have hs8 := hlic5 p ps
      cases hr : R false (p :: pre) <;>
        cases hs : S false (p :: pre) <;>
        simp [fifthSixthWithoutBoth, hr, hs,
          List.map_append, List.map_map, Function.comp_def,
          FifthSixthStoppedEvent.signedValue, shallowOneSidedValue,
          shallowFifthValue, hr8, hs8, hinner, ih]

/-- Full actual RAW/LICENSED instantiation, not a user-supplied
smallness field. It reuses the earlier proved-candidate rank-five and
rank-six cutoff collapse independently for each policy. -/
theorem actual_fourth_prefix_shallow_map
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ)
    (pre : List ℕ) (hlen : pre.length = 4)
    (mass : ℝ) (remaining : List ℕ) (g : ℝ → ℝ) :
    ((fifthSixthWithoutBoth
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon) (highQTest X F))
      pre true mass remaining).map (fun ev => g ev.signedValue)) =
    ((fifthSixthWithoutBoth
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon) (highQTest X F))
      pre true mass remaining).map (fun ev => g (shallowOneSidedValue
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
        (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon) (highQTest X F))
        ev))) := by
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
  let T := attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon) (highQTest X F)
  have hcutR : ∀ s pos m tail,
      ((s.length = 5 ∧ pos = false) ∨ (s.length = 6 ∧ pos = true)) →
      stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T s pos m tail =
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T s pos m tail := by
    intro s pos m tail hlevel
    exact actual_one_sided_stopped8_eq_stopped7
      delta n e q om N cap w he hN epsilon heps X hX F
      R (Or.inl rfl) s pos m tail hlevel
  have hcutS : ∀ s pos m tail,
      ((s.length = 5 ∧ pos = false) ∨ (s.length = 6 ∧ pos = true)) →
      stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T s pos m tail =
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T s pos m tail := by
    intro s pos m tail hlevel
    exact actual_one_sided_stopped8_eq_stopped7
      delta n e q om N cap w he hN epsilon heps X hX F
      S (Or.inr rfl) s pos m tail hlevel
  have hr5 : ∀ p tail,
      stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail =
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail := by
    intro p tail
    exact hcutR (p :: pre) false (mass * (1 : ℝ)) tail
      (Or.inl ⟨by simp [hlen], rfl⟩)
  have hs5 : ∀ p tail,
      stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail =
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail := by
    intro p tail
    exact hcutS (p :: pre) false (mass * (1 : ℝ)) tail
      (Or.inl ⟨by simp [hlen], rfl⟩)
  have hr6 : ∀ p q tail,
      stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail =
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail := by
    intro p q tail
    exact hcutR (q :: p :: pre) true
      ((mass * (1 : ℝ)) * (1 : ℝ)) tail
      (Or.inr ⟨by simp [hlen], rfl⟩)
  have hs6 : ∀ p q tail,
      stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail =
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail := by
    intro p q tail
    exact hcutS (q :: p :: pre) true
      ((mass * (1 : ℝ)) * (1 : ℝ)) tail
      (Or.inr ⟨by simp [hlen], rfl⟩)
  exact fourth_one_sided_shallow_map R S T g
    pre mass remaining hr5 hs5 hr6 hs6


/-- A true shared fourth-frontier source has four selected primes and
positive sign. Both facts come from the SAME original frontier, not
from a new sign certificate. -/
theorem real_fourth_prefix_positive
    (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ sharedRankFour e q om N cap w z) :
    state.selectedPrefix.length = 4 ∧ state.positive = true := by
  have hl : state.selectedPrefix.length = 4 :=
    firstExitDepthFrontier_selected_length 4
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ)) []
      (roughPrimeUniverse N cap w z) true 1 (by simp) state hs
  have hp : state.positive = evenListLength state.selectedPrefix :=
    mem_firstExitDepthFrontier_positive_eq_evenListLength 4
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ))
      (roughPrimeUniverse N cap w z) state hs
  refine ⟨hl, ?_⟩
  rw [hp]
  cases state.selectedPrefix with
  | nil => simp at hl
  | cons a xs =>
      cases xs with
      | nil => simp at hl
      | cons b ys =>
          cases ys with
          | nil => simp at hl
          | cons c zs =>
              cases zs with
              | nil => simp at hl
              | cons d ws =>
                  cases ws with
                  | nil => simp [evenListLength]
                  | cons f rest =>
                      simp only [List.length_cons] at hl
                      omega

/-- Strong actual per-occurrence identity: the original event List is
UNCHANGED, but every event's old cutoff-eight signed payload agrees
with its actual cutoff-seven recomputation. This covers all fourth
parent occurrences and all duplicated carriers. -/
theorem actual_fourth_event_map_eq_shallow
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hs : state ∈ sharedRankFour e q om N cap w z)
    (g : ℝ → ℝ) :
    ((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X F state).map
        (fun ev => g ev.signedValue)) =
    ((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X F state).map
        (fun ev => g (shallowOneSidedValue
          (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
          (P4AOriginalFull87LicensedSixthPolicy.policy
            delta n e q om (N : ℝ))
          (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
            (highQTest X F)) ev))) := by
  obtain ⟨hlen, hpositive⟩ :=
    real_fourth_prefix_positive e q om N cap w z state hs
  simpa only [actualFifthSixthWithoutBoth, hpositive] using
    actual_fourth_prefix_shallow_map
      delta n e q om N cap w he hN epsilon heps X hX F
      state.selectedPrefix hlen state.mass state.remaining g

/-- Same original physical event population and single ABSOLUTE bill,
but the actual shallow rank-five/six values are visible on its RHS.
Not a new source generator, and not an additional paid invoice. -/
def actualShallowExclusiveAbsInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    ((actualFifthSixthWithoutBoth delta n e q om N cap w L X F state).map
      (fun ev => |shallowOneSidedValue
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        (P4AOriginalFull87LicensedSixthPolicy.policy
          delta n e q om (N : ℝ))
        (attachedLeafTest N cap 1 w L (highQTest X F)) ev|)).sum)).sum

/-- Exact replacement of the former absolute bill. No cancellation of
distinct occurrences, no reduction by cap monotonicity, and no second
charge. Both sides may still be quantitatively large. -/
theorem actual_exclusive_abs_eq_shallow
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) :
    actualFifthSixthExclusiveAbsInvoice delta n e q om N cap w z
      ((N : ℝ) ^ epsilon) X F =
    actualShallowExclusiveAbsInvoice delta n e q om N cap w z
      ((N : ℝ) ^ epsilon) X F := by
  unfold actualFifthSixthExclusiveAbsInvoice
    actualShallowExclusiveAbsInvoice
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hs
  exact congrArg List.sum
    (actual_fourth_event_map_eq_shallow
      delta n e q om N cap w z he hN epsilon heps X hX F
      state hs (fun v => |v|))

/-- The original stopped delta has exactly the surviving shallow
rank-five/six SOURCE contributions. No assertion they individually
vanish and no new event source is introduced. -/
theorem actual_stopped_delta_eq_shallow
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) :
    rawStopped e q om N cap w z ((N : ℝ) ^ epsilon) X F -
      licensedStopped delta n e q om N cap w z
        ((N : ℝ) ^ epsilon) X F =
    ((sharedRankFour e q om N cap w z).map (fun state =>
      ((actualFifthSixthWithoutBoth delta n e q om N cap w
        ((N : ℝ) ^ epsilon) X F state).map
        (fun ev => shallowOneSidedValue
          (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
          (P4AOriginalFull87LicensedSixthPolicy.policy
            delta n e q om (N : ℝ))
          (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
            (highQTest X F)) ev)).sum)).sum := by
  rw [P4AOriginalFull87SixthBothInvoice.actual_stopped_difference_eq_fifth_sixth_exclusives
    delta n e q om N cap w z he hN epsilon heps X hX F]
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hs
  simpa only [id_eq] using congrArg List.sum
    (actual_fourth_event_map_eq_shallow
      delta n e q om N cap w z he hN epsilon heps X hX F
      state hs id)

/-- The previous FULL physical high-q inequality now pays the SAME
early stopped bill at cutoff seven, plus the same three outside/producer
classes exactly once. It is NOT a PP or H_N estimate. -/
theorem abs_full_physical_le_shallow_exclusive_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) :
    |P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        N cap w z ((N : ℝ) ^ epsilon) (highQTest X F) -
      P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87LicensedSixthPolicy.policy
          delta n e q om (N : ℝ))
        N cap w z ((N : ℝ) ^ epsilon) (highQTest X F)| ≤
    actualShallowExclusiveAbsInvoice delta n e q om N cap w z
      ((N : ℝ) ^ epsilon) X F +
    ((P4AOriginalFull87RawTrimSignedHighQ.rawOutsideHighQInvoice
        delta e q om N cap w z ((N : ℝ) ^ epsilon) X F +
      P4AOriginalFull87ThreeClassLeafInvoices.actualProducerThreeClassLeafBill
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X F) +
      P4AOriginalFull87LicensedOutsideThreeInvoices.licensedOutsideHighQInvoice
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X F) := by
  have h := P4AOriginalFull87SixthBothInvoice.abs_full_physical_le_exclusive_fifth_sixth_and_frontier
    delta n e q om N cap w z he hN epsilon heps X hX F
  rwa [actual_exclusive_abs_eq_shallow
    delta n e q om N cap w z he hN epsilon heps X hX F] at h

end
end ImbalancedChen.P4AOriginalFull87ShallowOneSidedInvoice
