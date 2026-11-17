import ImbalancedChen.P4AOriginalFull87SixthPositiveCarrierCut
import ImbalancedChen.P4AOriginalFull87SixthBothInvoice
import ImbalancedChen.FirstExitFrontierInvariants
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The previous sixth-positive carrier cutoff required the as-yet-unproved
premise that every prime in the post-fifth suffix belongs to the ORIGINAL
roughPrimeUniverse.  Here that premise is supplied for every occurrence of
the EXISTING fifthSixthWithoutBoth event producer on the actual shared
rank-four frontier.

This is a finite structural proof about the original producer: the suffix
of a fifth-exclusive event is the tail after its real fifth query; a
sixth-from-both event has the tail after its real sixth query. Both tails
are sublists of the unchanged source carrier, including its order. We do
not introduce a new parent, a new event list, a sixth odd gate, or an
unproved high-q numerical estimate.
-/

namespace ImbalancedChen.P4AOriginalFull87ActualSixthSuffix
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent firstFifthEvents)
open P4AOriginalFull87FifthSixthStoppedEvents
  (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice
  (fifthSixthWithoutBoth actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthOnlyEventInvoice (sixthPositiveContinuation)
open P4AOriginalFull87SixthPositiveCarrierCut
  (sixthPositiveContinuation_zero_of_original_rough_cutoff)
open P1Pair12RetainedSignedSource (attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)

/-- The real unprocessed sixth suffix, regardless of which actual
fifth/sixth one-sided constructor produced the event. -/
def eventSixthSuffix {α : Type*} : FifthSixthStoppedEvent α → List α
  | .fifthExclusive ev => ev.remainingAfter
  | .sixthFromBoth _ ev => ev.remainingAfter

/-- A genuine firstFifthEvents occurrence carries a suffix of precisely
the incoming ordered carrier.  No distinctness assumption is used. -/
private theorem first_fifth_suffix_sublist {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) :
    ∀ ev ∈ firstFifthEvents R S h T pre positive mass remaining,
      ev.remainingAfter <+ remaining := by
  induction remaining with
  | nil =>
      intro ev hev
      simp [firstFifthEvents] at hev
  | cons p ps ih =>
      intro ev hev
      have hps : ps <+ p :: ps := List.sublist_cons_self p ps
      by_cases hr : R (!positive) (p :: pre) = true
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp [firstFifthEvents, hr, hs] at hev
          rcases hev with heq | htail
          · subst ev
            exact hps
          · exact (ih ev htail).trans hps
        · simp [firstFifthEvents, hr, hs] at hev
          rcases hev with heq | htail
          · subst ev
            exact hps
          · exact (ih ev htail).trans hps
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp [firstFifthEvents, hr, hs] at hev
          rcases hev with heq | htail
          · subst ev
            exact hps
          · exact (ih ev htail).trans hps
        · have htail : ev ∈ firstFifthEvents R S h T pre positive mass ps := by
            simpa [firstFifthEvents, hr, hs] using hev
          exact (ih ev htail).trans hps

/-- In the ORIGINAL fifthSixthWithoutBoth recursion, every retained
fifth-only or sixth-from-both occurrence has an unmodified suffix which
is a sublist of the input.  The actual sixth-BOTH exclusion is applied
only to the inner event list, never to the carrier itself. -/
private theorem fifth_sixth_suffix_sublist {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) :
    ∀ ev ∈ fifthSixthWithoutBoth R S h T pre positive mass remaining,
      eventSixthSuffix ev <+ remaining := by
  induction remaining with
  | nil =>
      intro ev hev
      simp [fifthSixthWithoutBoth] at hev
  | cons p ps ih =>
      intro ev hev
      have hps : ps <+ p :: ps := List.sublist_cons_self p ps
      by_cases hr : R (!positive) (p :: pre) = true
      · by_cases hs : S (!positive) (p :: pre) = true
        · have hsplit : ev ∈
              (((firstFifthEvents R S h T (p :: pre) (!positive)
                  (mass * h p) ps).filter
                  (fun x => decide (x.kind ≠
                    P4AOriginalFull87FirstFifthStoppedEvents.FifthAdmissionClass.both))).map
                    (FifthSixthStoppedEvent.sixthFromBoth (p :: pre))) ++
              fifthSixthWithoutBoth R S h T pre positive mass ps := by
            simpa [fifthSixthWithoutBoth, hr, hs] using hev
          rcases List.mem_append.mp hsplit with hinner | htail
          · obtain ⟨inner, hfiltered, rfl⟩ := List.mem_map.mp hinner
            have hfirst : inner ∈ firstFifthEvents R S h T
                (p :: pre) (!positive) (mass * h p) ps :=
              (List.mem_filter.mp hfiltered).1
            exact (first_fifth_suffix_sublist R S h T
              (p :: pre) (!positive) (mass * h p) ps inner hfirst).trans hps
          · exact (ih ev htail).trans hps
        · simp [fifthSixthWithoutBoth, hr, hs] at hev
          rcases hev with heq | htail
          · subst ev
            exact hps
          · exact (ih ev htail).trans hps
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp [fifthSixthWithoutBoth, hr, hs] at hev
          rcases hev with heq | htail
          · subst ev
            exact hps
          · exact (ih ev htail).trans hps
        · have htail :
              ev ∈ fifthSixthWithoutBoth R S h T pre positive mass ps := by
            simpa [fifthSixthWithoutBoth, hr, hs] using hev
          exact (ih ev htail).trans hps

/-- ACTUAL fifth/sixth one-sided event suffixes, on every occurrence of
the exact common rank-four producer, stay inside the ORIGINAL rough
universe.  The proof passes through both original ordered-sublist
invariants and does not re-enumerate a single prime. -/
theorem actual_event_suffix_mem_original_rough
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth
      delta n e q om N cap w L X F state)
    (p : ℕ) (hp : p ∈ eventSixthSuffix ev) :
    p ∈ roughPrimeUniverse N cap w z := by
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let T := attachedLeafTest N cap 1 w L (highQTest X F)
  have hsuffix : eventSixthSuffix ev <+ state.remaining :=
    fifth_sixth_suffix_sublist R S (fun _ : ℕ => (1 : ℝ)) T
      state.selectedPrefix state.positive state.mass state.remaining
      ev (by simpa only [actualFifthSixthWithoutBoth] using hev)
  have hfront :
      state.selectedPrefix.reverse ++ state.remaining <+
        roughPrimeUniverse N cap w z :=
    firstExitDepthFrontier_selected_remaining_sublist 4 R
      (fun _ : ℕ => (1 : ℝ)) []
      (roughPrimeUniverse N cap w z) true 1 state
      (by simpa only [sharedRankFour] using hstate)
  have hpState : p ∈ state.remaining := hsuffix.subset hp
  exact hfront.subset (List.mem_append.mpr (Or.inr hpState))

/-- In particular, actual fifth-exclusive stopped subtrees have no
uncontrolled *carrier membership* premise in the earlier cutoff.
This is only a sufficient level condition for the original sixth-plus
continuations, not a theorem that every fifth prefix satisfies it. -/
theorem actual_fifth_exclusive_sixth_zero_of_level
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X F state)
    (hL : 0 ≤ L)
    (hcut : (L * (fifth.selectedAfter.prod : ℝ)) * z ≤ (X : ℝ)) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let T := attachedLeafTest N cap 1 w L (highQTest X F)
    sixthPositiveContinuation R T fifth.selectedAfter fifth.massAfter
      fifth.remainingAfter = 0 ∧
    sixthPositiveContinuation S T fifth.selectedAfter fifth.massAfter
      fifth.remainingAfter = 0 := by
  have hmem : ∀ p ∈ fifth.remainingAfter,
      p ∈ roughPrimeUniverse N cap w z := by
    intro p hp
    exact actual_event_suffix_mem_original_rough
      delta n e q om N cap w z L X F state hstate
      (.fifthExclusive fifth) hfifth p hp
  constructor
  · exact sixthPositiveContinuation_zero_of_original_rough_cutoff
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      N cap w z L X F fifth.selectedAfter fifth.massAfter
      fifth.remainingAfter hL hmem hcut
  · exact sixthPositiveContinuation_zero_of_original_rough_cutoff
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      N cap w z L X F fifth.selectedAfter fifth.massAfter
      fifth.remainingAfter hL hmem hcut

end
end ImbalancedChen.P4AOriginalFull87ActualSixthSuffix
