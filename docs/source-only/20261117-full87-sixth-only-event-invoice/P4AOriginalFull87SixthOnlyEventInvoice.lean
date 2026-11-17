import ImbalancedChen.P4AOriginalFull87FifthGateRankSixOnly
import ImbalancedChen.P4AOriginalFull87ShallowOneSidedInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The actual fifth-exclusive events of the ORIGINAL fifthSixthWithoutBoth
producer have admitted fifth odd gates. At high-q these roots have zero
literal fifth terminal, so their already-reduced cutoff-seven stopped
value is the genuine ordered sum of admitted sixth-positive terminals.
This file performs the substitution on exactly the EXISTING event List.

Sixth-exclusive events arising from a both-admitted fifth root remain
unchanged. Every selected word, sign, mass, post-query carrier, small
Rosser attachment, physical modulus, and List occurrence is preserved.
No sixth-even bound, analytic input, numeric reserve or savings is assumed.
-/

namespace ImbalancedChen.P4AOriginalFull87SixthOnlyEventInvoice
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents
  (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice
  (fifthSixthWithoutBoth actualFifthSixthWithoutBoth)
open P4AOriginalFull87ShallowOneSidedInvoice
  (shallowFifthValue shallowOneSidedValue
   actualShallowExclusiveAbsInvoice)
open P4AOriginalFull87FifthGateRankSixOnly
  (actual_admitted_fifth_stopped7_eq_sixth_only)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)

/-- The actual sixth-positive terminal population below one admitted
fifth-minus root. It is NOT a new source: the existing post-fifth suffix
is traversed by List.map without deduplication or reordering. -/
def sixthPositiveContinuation
    (R : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (mass : ℝ) (remaining : List ℕ) : ℝ :=
  (remaining.map (fun p =>
    if R true (p :: pre) = true then
      signedTreeCoefficient true mass * T true (p :: pre)
    else 0)).sum

/-- Only the fifth-exclusive value is opened into its admitted sixth
continuation; the filtered sixth-from-both event is already a true
sixth-root event and retains its existing cutoff-seven payload. -/
def sixthOnlyFifthValue
    (R S : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (ev : FifthStoppedEvent ℕ) : ℝ :=
  match ev.kind with
  | .rawOnly =>
      sixthPositiveContinuation R T ev.selectedAfter
        ev.massAfter ev.remainingAfter
  | .licensedOnly =>
      -sixthPositiveContinuation S T ev.selectedAfter
        ev.massAfter ev.remainingAfter
  | .both => shallowFifthValue R S T ev

def sixthOnlyOneSidedValue
    (R S : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive ev => sixthOnlyFifthValue R S T ev
  | .sixthFromBoth _ ev => shallowFifthValue R S T ev

/-- Finite occurrence conservation, conditional only on the fifth
roots' actual cutoff-seven identities. The sixth-from-both producer
is never re-evaluated via a fifth admission, and its suffix is kept. -/
private theorem fourth_map_to_sixth_only
    (R S : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (mass : ℝ) (remaining : List ℕ)
    (g : ℝ → ℝ)
    (hraw : ∀ p tail, R false (p :: pre) = true →
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail =
      sixthPositiveContinuation R T
        (p :: pre) (mass * (1 : ℝ)) tail)
    (hlic : ∀ p tail, S false (p :: pre) = true →
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail =
      sixthPositiveContinuation S T
        (p :: pre) (mass * (1 : ℝ)) tail) :
    ((fifthSixthWithoutBoth R S (fun _ : ℕ => (1 : ℝ))
      T pre true mass remaining).map
        (fun ev => g (shallowOneSidedValue R S T ev))) =
    ((fifthSixthWithoutBoth R S (fun _ : ℕ => (1 : ℝ))
      T pre true mass remaining).map
        (fun ev => g (sixthOnlyOneSidedValue R S T ev))) := by
  induction remaining with
  | nil => rfl
  | cons p ps ih =>
      cases hr : R false (p :: pre) with
      | false =>
          cases hs : S false (p :: pre) with
          | false =>
              simp [fifthSixthWithoutBoth, hr, hs,
                List.map_append, ih]
          | true =>
              have hroot := hlic p ps (by simpa using hs)
              simp [fifthSixthWithoutBoth, hr, hs, hroot,
                shallowOneSidedValue, shallowFifthValue,
                sixthOnlyOneSidedValue, sixthOnlyFifthValue,
                List.map_append, ih]
      | true =>
          cases hs : S false (p :: pre) with
          | false =>
              have hroot := hraw p ps (by simpa using hr)
              simp [fifthSixthWithoutBoth, hr, hs, hroot,
                shallowOneSidedValue, shallowFifthValue,
                sixthOnlyOneSidedValue, sixthOnlyFifthValue,
                List.map_append, ih]
          | true =>
              simp [fifthSixthWithoutBoth, hr, hs,
                shallowOneSidedValue, sixthOnlyOneSidedValue,
                List.map_append, List.map_map, Function.comp_def, ih]

/-- The true RAW and LICENSED fifth gates (and NO arbitrary smallness
field) supply the hypotheses of the exact finite event-map lemma. -/
theorem actual_fourth_prefix_map_to_sixth_only
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
    let R := P4AOriginalFull87CompleteSixthDispatch.policy
      e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let T := attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
      (highQTest X F)
    ((fifthSixthWithoutBoth R S (fun _ : ℕ => (1 : ℝ))
      T pre true mass remaining).map
        (fun ev => g (shallowOneSidedValue R S T ev))) =
    ((fifthSixthWithoutBoth R S (fun _ : ℕ => (1 : ℝ))
      T pre true mass remaining).map
        (fun ev => g (sixthOnlyOneSidedValue R S T ev))) := by
  let R := P4AOriginalFull87CompleteSixthDispatch.policy
    e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let T := attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
    (highQTest X F)
  have hr : ∀ p tail, R false (p :: pre) = true →
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail =
      sixthPositiveContinuation R T
        (p :: pre) (mass * (1 : ℝ)) tail := by
    intro p tail hgate
    simpa only [sixthPositiveContinuation] using
      (actual_admitted_fifth_stopped7_eq_sixth_only
        delta n e q om N cap w he hN epsilon heps X hX F
        R (Or.inl rfl) (p :: pre) (by simp [hlen])
        hgate (mass * (1 : ℝ)) tail)
  have hs : ∀ p tail, S false (p :: pre) = true →
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail =
      sixthPositiveContinuation S T
        (p :: pre) (mass * (1 : ℝ)) tail := by
    intro p tail hgate
    simpa only [sixthPositiveContinuation] using
      (actual_admitted_fifth_stopped7_eq_sixth_only
        delta n e q om N cap w he hN epsilon heps X hX F
        S (Or.inr rfl) (p :: pre) (by simp [hlen])
        hgate (mass * (1 : ℝ)) tail)
  exact fourth_map_to_sixth_only R S T pre mass remaining g hr hs

/-- All ACTUAL shared-fourth occurrences inherit the same finite
replacement, with the real positive parity and prefix length supplied
by the unchanged original frontier invariant. -/
theorem actual_fourth_event_map_to_sixth_only
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hst : state ∈ sharedRankFour e q om N cap w z)
    (g : ℝ → ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let T := attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
      (highQTest X F)
    ((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X F state).map
        (fun ev => g (shallowOneSidedValue R S T ev))) =
    ((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X F state).map
        (fun ev => g (sixthOnlyOneSidedValue R S T ev))) := by
  obtain ⟨hlen, hpositive⟩ :=
    P4AOriginalFull87ShallowOneSidedInvoice.real_fourth_prefix_positive
      e q om N cap w z state hst
  simpa only [actualFifthSixthWithoutBoth, hpositive] using
    actual_fourth_prefix_map_to_sixth_only
      delta n e q om N cap w he hN epsilon heps X hX F
      state.selectedPrefix hlen state.mass state.remaining g

/-- Replacement absolute ledger on the SAME event occurrences. No
separate rank-five charge survives; only actual sixth-positive values
remain, including the separately emitted sixth-from-both events. -/
def actualSixthOnlyExclusiveAbsInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    ((actualFifthSixthWithoutBoth delta n e q om N cap w
      L X F state).map (fun ev =>
        |sixthOnlyOneSidedValue
          (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
          (P4AOriginalFull87LicensedSixthPolicy.policy
            delta n e q om (N : ℝ))
          (attachedLeafTest N cap 1 w L (highQTest X F)) ev|)).sum)).sum

theorem actual_shallow_abs_eq_sixth_only
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) :
    actualShallowExclusiveAbsInvoice delta n e q om N cap w z
      ((N : ℝ) ^ epsilon) X F =
    actualSixthOnlyExclusiveAbsInvoice delta n e q om N cap w z
      ((N : ℝ) ^ epsilon) X F := by
  unfold actualShallowExclusiveAbsInvoice actualSixthOnlyExclusiveAbsInvoice
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hst
  exact congrArg List.sum
    (actual_fourth_event_map_to_sixth_only
      delta n e q om N cap w z he hN epsilon heps X hX F
      state hst (fun v => |v|))

/-- The original signed stopped discrepancy has only the sixth-positive
survivor evaluations, not a newly generated source or discarded events. -/
theorem actual_stopped_delta_eq_sixth_only
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
        ((N : ℝ) ^ epsilon) X F state).map (fun ev =>
          sixthOnlyOneSidedValue
            (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
            (P4AOriginalFull87LicensedSixthPolicy.policy
              delta n e q om (N : ℝ))
            (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
              (highQTest X F)) ev)).sum)).sum := by
  rw [P4AOriginalFull87ShallowOneSidedInvoice.actual_stopped_delta_eq_shallow
    delta n e q om N cap w z he hN epsilon heps X hX F]
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hst
  simpa only [id_eq] using congrArg List.sum
    (actual_fourth_event_map_to_sixth_only
      delta n e q om N cap w z he hN epsilon heps X hX F
      state hst id)

/-- Retain the FULL original physical error decomposition. The old
shallow bill is REPLACED once by its equal sixth-only value, while the
raw-outside, producer and licensed-outside invoices remain untouched. -/
theorem abs_full_physical_le_sixth_only_invoice
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
    actualSixthOnlyExclusiveAbsInvoice delta n e q om N cap w z
      ((N : ℝ) ^ epsilon) X F +
    ((P4AOriginalFull87RawTrimSignedHighQ.rawOutsideHighQInvoice
        delta e q om N cap w z ((N : ℝ) ^ epsilon) X F +
      P4AOriginalFull87ThreeClassLeafInvoices.actualProducerThreeClassLeafBill
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X F) +
      P4AOriginalFull87LicensedOutsideThreeInvoices.licensedOutsideHighQInvoice
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X F) := by
  have h := P4AOriginalFull87ShallowOneSidedInvoice.abs_full_physical_le_shallow_exclusive_invoice
    delta n e q om N cap w z he hN epsilon heps X hX F
  rwa [actual_shallow_abs_eq_sixth_only
    delta n e q om N cap w z he hN epsilon heps X hX F] at h

end
end ImbalancedChen.P4AOriginalFull87SixthOnlyEventInvoice
