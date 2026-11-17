import ImbalancedChen.P4AOriginalFull87NoDirectSixthFromBoth
import ImbalancedChen.P4AOriginalFull87LargeTailInvoice
import ImbalancedChen.P4AOriginalFull87PlusBetaPowerFilter
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The surviving actual fifth-exclusive signed high-q discrepancy uses ONE
sixth-positive arithmetic kernel, not one RAW kernel and a different
LICENSED kernel. Both original sixth gates are automatically true.
Only the REAL fifth-admission decision contributes a +/- sign.

This is an exact, unpaired same-physical-rho identity, not a bound on
the retained large fifth-weight band, PP admission or any H_N saving.
It keeps the original event List, selected history, post-fifth suffix,
small PLUS Rosser indices, physical a*b modulus, sign and multiplicity.
The direct sixthFromBoth case is absent ONLY for actual reduced sources
by the previously established candidate structural theorem.
-/

namespace ImbalancedChen.P4AOriginalFull87CommonSixthSignedKernel
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent FifthAdmissionClass firstFifthEvents)
open P4AOriginalFull87FifthSixthStoppedEvents
  (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice
  (fifthSixthWithoutBoth actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthSixthContinuation largeFifthPlusAttachment
   largeFifthOneSidedEventValue largeFifthOneSidedValue)
open P4AOriginalFull87NoDirectSixthFromBoth (actual_no_sixth_from_both)

/-- The common high-q sixth kernel, using the original filtered PLUS-beta
finite sum and EXACTLY the original post-fifth carrier List.
No arbitrary action mask or inequality is attached to its summands. -/
def commonLargeSixthKernel (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (F : ℕ → ℝ) (fifth : FifthStoppedEvent ℕ) : ℝ :=
  (fifth.remainingAfter.map (fun p =>
    signedTreeCoefficient true fifth.massAfter *
      largeFifthPlusAttachment N cap w L X F fifth.selectedAfter p)).sum

/-- On an automatically accepted positive-sixth gate, the entire
candidate continuation is independent of the policy R.
This is an equality of literal List sums, not two analytic bounds. -/
theorem positive_gate_large_continuation_eq_common
    (R : Bool → List ℕ → Bool)
    (heven : ∀ word, R true word = true)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (fifth : FifthStoppedEvent ℕ) :
    largeFifthSixthContinuation R N cap w L X F fifth =
      commonLargeSixthKernel N cap w L X F fifth := by
  unfold largeFifthSixthContinuation commonLargeSixthKernel
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp [heven (p :: fifth.selectedAfter)]

/-- A fifthExclusive constructor in the LITERAL reduced producer can only
be emitted at a RAW-only or LICENSED-only fifth gate.
BOTH fifth admission emits a sixthFromBoth constructor instead.
The recursion uses the original suffix after each candidate p. -/
private theorem reduced_fifth_exclusive_kind {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) (fifth : FifthStoppedEvent α)
    (hmem : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      fifthSixthWithoutBoth R S h T pre positive mass remaining) :
    fifth.kind = FifthAdmissionClass.rawOnly ∨
      fifth.kind = FifthAdmissionClass.licensedOnly := by
  induction remaining with
  | nil =>
      simp [fifthSixthWithoutBoth] at hmem
  | cons p ps ih =>
      by_cases hr : R (!positive) (p :: pre) = true
      · by_cases hs : S (!positive) (p :: pre) = true
        · have htail : FifthSixthStoppedEvent.fifthExclusive fifth ∈
              fifthSixthWithoutBoth R S h T pre positive mass ps := by
            simpa [fifthSixthWithoutBoth, hr, hs] using hmem
          exact ih htail
        · have hparts :
              fifth.kind = FifthAdmissionClass.rawOnly ∨
              FifthSixthStoppedEvent.fifthExclusive fifth ∈
                fifthSixthWithoutBoth R S h T pre positive mass ps := by
            simpa [fifthSixthWithoutBoth, hr, hs] using hmem
          rcases hparts with hkind | htail
          · exact Or.inl hkind
          · exact ih htail
      · by_cases hs : S (!positive) (p :: pre) = true
        · have hparts :
              fifth.kind = FifthAdmissionClass.licensedOnly ∨
              FifthSixthStoppedEvent.fifthExclusive fifth ∈
                fifthSixthWithoutBoth R S h T pre positive mass ps := by
            simpa [fifthSixthWithoutBoth, hr, hs] using hmem
          rcases hparts with hkind | htail
          · exact Or.inr hkind
          · exact ih htail
        · have htail : FifthSixthStoppedEvent.fifthExclusive fifth ∈
              fifthSixthWithoutBoth R S h T pre positive mass ps := by
            simpa [fifthSixthWithoutBoth, hr, hs] using hmem
          exact ih htail

/-- Instantiation on the SAME actual source: no fifth-both tagged event
may be masquerading as a fifthExclusive event. -/
theorem actual_fifth_exclusive_kind
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ) (fifth : FifthStoppedEvent ℕ)
    (hmem : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X F state) :
    fifth.kind = FifthAdmissionClass.rawOnly ∨
      fifth.kind = FifthAdmissionClass.licensedOnly := by
  exact reduced_fifth_exclusive_kind
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (P1Pair12RetainedSignedSource.attachedLeafTest N cap 1 w L
      (P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest X F))
    state.selectedPrefix state.positive state.mass state.remaining fifth
    (by simpa only [actualFifthSixthWithoutBoth] using hmem)

/-- A signed member value with exactly one common sixth kernel.
The .both and sixthFromBoth fallbacks are purely syntactic: the two
separate source-membership theorems below prove them unreachable.
No real event is erased by a newly imposed zero estimate. -/
def commonSignedEventValue
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      match fifth.kind with
      | .rawOnly => commonLargeSixthKernel N cap w L X F fifth
      | .licensedOnly => -commonLargeSixthKernel N cap w L X F fifth
      | .both => 0
  | .sixthFromBoth _ _ => 0

/-- On every actual reduced source occurrence, original signed arithmetic
has one common PLUS-beta sixth kernel; only the real fifth gate direction
chooses its sign. This is not a positive-mass comparison. -/
theorem actual_event_large_value_eq_common
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X F state) :
    largeFifthOneSidedEventValue
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
      N cap w L X F ev =
    commonSignedEventValue N cap w L X F ev := by
  have hraw : ∀ word,
      P4AOriginalFull87CompleteSixthDispatch.policy
        e q om (N : ℝ) true word = true := by
    intro word
    exact P4AOriginalFull87CompleteSixthDispatch.policy_even
      e q om (N : ℝ) word
  have hlicensed : ∀ word,
      P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ) true word = true := by
    intro word
    exact P4AOriginalFull87LicensedSixthPolicy.policy_even
      delta n e q om (N : ℝ) word
  cases ev with
  | fifthExclusive fifth =>
      have hkind := actual_fifth_exclusive_kind
        delta n e q om N cap w L X F state fifth hev
      rcases hkind with hr | hs
      · simp [largeFifthOneSidedEventValue, largeFifthOneSidedValue,
          commonSignedEventValue, hr,
          positive_gate_large_continuation_eq_common
            (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
            hraw N cap w L X F fifth]
      · simp [largeFifthOneSidedEventValue, largeFifthOneSidedValue,
          commonSignedEventValue, hs,
          positive_gate_large_continuation_eq_common
            (P4AOriginalFull87LicensedSixthPolicy.policy
              delta n e q om (N : ℝ))
            hlicensed N cap w L X F fifth]
  | sixthFromBoth fifthSelected inner =>
      exact False.elim
        ((actual_no_sixth_from_both
          delta n e q om N cap w z L X F state hstate
          fifthSelected inner) hev)

/-- Direct ORIGINAL full-87 stopped signed identity, NOT a subtraction
of independent sieve inequalities. The same unchanged event population
is assigned a single arithmetic kernel with its actual fifth-gate sign.
The large-index PLUS Rosser filter, original full a*b test and actual
post-fifth prime occurrences remain inside commonLargeSixthKernel. -/
theorem actual_stopped_difference_eq_common_signed_sixth_kernel
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
        (commonSignedEventValue N cap w ((N : ℝ) ^ epsilon) X F)).sum)).sum := by
  rw [P4AOriginalFull87LargeTailInvoice.actual_stopped_delta_eq_power_filtered
    delta n e q om N cap w z he hN epsilon heps X hX F]
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hstate
  apply congrArg List.sum
  apply List.map_congr_left
  intro ev hev
  exact actual_event_large_value_eq_common
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X F
    state hstate ev hev

end
end ImbalancedChen.P4AOriginalFull87CommonSixthSignedKernel
