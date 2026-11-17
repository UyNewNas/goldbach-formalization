import ImbalancedChen.P4AOriginalFull87SixthBothInvoice
import ImbalancedChen.P4AOriginalFull87ShallowOneSidedInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A structural fact of the ACTUAL, already filtered full-87 source:
there are NO surviving `sixthFromBoth` occurrences. This is stronger
than bounding their terminal sum. For a fifth child admitted by both,
the next (sixth, positive) admission is automatic in BOTH original
policies. Hence every event emitted by `firstFifthEvents` at that
sixth query has `kind = .both`; the existing sixth-both filter
removes all of them.

Do NOT conflate this fact with zeroing the fifthExclusive contribution:
its original fifth history and the genuine sixth-positive terminal
remain exactly as before and still carry an unpaid signed high-q tail.
The already established high-q cancellation of sixth-BOTH events is
needed upstream to justify the original reduced invoice; here we
prove that the reduced source has no independent sixthFromBoth class.
-/ 

namespace ImbalancedChen.P4AOriginalFull87NoDirectSixthFromBoth
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent FifthAdmissionClass firstFifthEvents)
open P4AOriginalFull87FifthSixthStoppedEvents
  (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice
  (fifthSixthWithoutBoth actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization
  (sharedRankFour)
open P1Pair12RetainedSignedSource (attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)

/-- On a negative fifth history the queried sixth sign is positive.
If both original policies accept EVERY positive node, the actual
`firstFifthEvents` producer emits only `.both` sixth events.
Filtering this class leaves the empty ORIGINAL list (not a new source
or a set of distinct primes). -/
private theorem even_sixth_filter_nil {α : Type*}
    (R S : Bool → List α → Bool)
    (hR : ∀ xs, R true xs = true)
    (hS : ∀ xs, S true xs = true)
    (h : α → ℝ) (T : Bool → List α → ℝ)
    (pre : List α) (mass : ℝ) (remaining : List α) :
    ((firstFifthEvents R S h T pre false mass remaining).filter
      (fun ev => decide (ev.kind ≠ FifthAdmissionClass.both))) = [] := by
  induction remaining with
  | nil => rfl
  | cons p ps ih =>
      simp [firstFifthEvents, hR (p :: pre), hS (p :: pre),
        List.filter_append, ih]

/-- Structural case analysis of the real fourth-to-fifth-to-sixth
producer. The two one-sided fifth branches are kept, while the both
fifth branch's filtered sixth source is empty, by the preceding proof.
The unaltered recursive skipped-prime tail preserves every occurrence
and the original order. -/
private theorem fifth_sixth_only_fifth_exclusive {α : Type*}
    (R S : Bool → List α → Bool)
    (hR : ∀ xs, R true xs = true)
    (hS : ∀ xs, S true xs = true)
    (h : α → ℝ) (T : Bool → List α → ℝ)
    (pre : List α) (mass : ℝ) (remaining : List α) :
    ∀ ev ∈ fifthSixthWithoutBoth R S h T pre true mass remaining,
      ∃ fifth : FifthStoppedEvent α,
        ev = FifthSixthStoppedEvent.fifthExclusive fifth := by
  induction remaining with
  | nil =>
      intro ev hev
      simp [fifthSixthWithoutBoth] at hev
  | cons p ps ih =>
      intro ev hev
      by_cases hr : R false (p :: pre) = true
      · by_cases hs : S false (p :: pre) = true
        · have hnil :
              ((firstFifthEvents R S h T (p :: pre) false
                  (mass * h p) ps).filter
                (fun inner =>
                  decide (inner.kind ≠ FifthAdmissionClass.both))) = [] :=
            even_sixth_filter_nil R S hR hS h T
              (p :: pre) (mass * h p) ps
          have htail : ev ∈
              fifthSixthWithoutBoth R S h T pre true mass ps := by
            simpa [fifthSixthWithoutBoth, hr, hs, hnil] using hev
          exact ih ev htail
        · simp [fifthSixthWithoutBoth, hr, hs] at hev
          rcases hev with heq | htail
          · subst ev
            exact ⟨_, rfl⟩
          · exact ih ev htail
      · by_cases hs : S false (p :: pre) = true
        · simp [fifthSixthWithoutBoth, hr, hs] at hev
          rcases hev with heq | htail
          · subst ev
            exact ⟨_, rfl⟩
          · exact ih ev htail
        · have htail : ev ∈
              fifthSixthWithoutBoth R S h T pre true mass ps := by
            simpa [fifthSixthWithoutBoth, hr, hs] using hev
          exact ih ev htail

/-- The ORIGINAL shared-rank-four state fixes the positive parity,
and the real policies supply their proven even-gate retention.
Consequently ALL occurrences of the already filtered actual event
list are genuine fifthExclusive events. There is no sixthFromBoth
source requiring an additional independent high-q bill. -/
theorem actual_event_is_fifth_exclusive
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth
      delta n e q om N cap w L X F state) :
    ∃ fifth : FifthStoppedEvent ℕ,
      ev = FifthSixthStoppedEvent.fifthExclusive fifth := by
  have hpositive : state.positive = true :=
    (P4AOriginalFull87ShallowOneSidedInvoice.real_fourth_prefix_positive
      e q om N cap w z state hstate).2
  let R := P4AOriginalFull87CompleteSixthDispatch.policy
    e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let T := attachedLeafTest N cap 1 w L (highQTest X F)
  have hevenR : ∀ xs, R true xs = true := by
    intro xs
    exact P4AOriginalFull87CompleteSixthDispatch.policy_even
      e q om (N : ℝ) xs
  have hevenS : ∀ xs, S true xs = true := by
    intro xs
    exact P4AOriginalFull87LicensedSixthPolicy.policy_even
      delta n e q om (N : ℝ) xs
  have hmem : ev ∈ fifthSixthWithoutBoth
      R S (fun _ : ℕ => (1 : ℝ)) T
      state.selectedPrefix true state.mass state.remaining := by
    simpa only [actualFifthSixthWithoutBoth, hpositive, R, S, T]
      using hev
  exact fifth_sixth_only_fifth_exclusive
    R S hevenR hevenS (fun _ : ℕ => (1 : ℝ)) T
    state.selectedPrefix state.mass state.remaining ev hmem

/-- In particular, no direct sixthFromBoth constructor survives in
the actual reduced source, for ANY fifthSelected or inner sixth event.
This is exact structural absence, not an analytic bound on the
unpaid fifthExclusive continuation. -/
theorem actual_no_sixth_from_both
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifthSelected : List ℕ) (inner : FifthStoppedEvent ℕ) :
    FifthSixthStoppedEvent.sixthFromBoth fifthSelected inner ∉
      actualFifthSixthWithoutBoth delta n e q om N cap w L X F state := by
  intro hmem
  obtain ⟨fifth, hcontra⟩ :=
    actual_event_is_fifth_exclusive
      delta n e q om N cap w z L X F
      state hstate (.sixthFromBoth fifthSelected inner) hmem
  cases hcontra

end
end ImbalancedChen.P4AOriginalFull87NoDirectSixthFromBoth
