import ImbalancedChen.P4AOriginalFull87PlusBetaPowerFilter
import ImbalancedChen.P4AOriginalFull87SixthOnlyEventInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Replace the ORIGINAL sixth-only signed and absolute stopped bills by the
equal, fifth-power-filtered values on the SAME actual FifthSixthWithoutBoth
event occurrences. The fifthExclusive PLUS Rosser sum retains only its
provably nonzero-eligible large fifth-weight indices; sixthFromBoth is
unchanged. The original full-physical outside, producer and licensed-outside
bills remain untouched and are charged once, not once per presentation.

This is still an EXACT finite identity, not an analytic large-tail estimate.
There is no new source producer, generic smallness input, or numerical saving.
-/

namespace ImbalancedChen.P4AOriginalFull87LargeTailInvoice
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87SixthOnlyEventInvoice
  (sixthOnlyOneSidedValue actualSixthOnlyExclusiveAbsInvoice)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthOneSidedEventValue actual_one_sided_event_map_eq_large)

/-- Charge exactly the retained fifthExclusive Rosser indices and the
unchanged sixthFromBoth occurrences of the old actual event population.
No new event List, cap mask or signed cancellation is introduced. -/
def actualPowerFilteredExclusiveAbsInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    ((actualFifthSixthWithoutBoth delta n e q om N cap w L X F state).map
      (fun ev =>
        |largeFifthOneSidedEventValue
          (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
          (P4AOriginalFull87LicensedSixthPolicy.policy
            delta n e q om (N : ℝ))
          N cap w L X F ev|)).sum)).sum

/-- This equality is on the genuine shared-rank-four parents and the
identical ordered one-sided event List. It holds for the original L,
without hiding a parameter restriction in a replacement invoice. -/
theorem actual_sixth_only_abs_eq_power_filtered
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    actualSixthOnlyExclusiveAbsInvoice delta n e q om N cap w z L X F =
    actualPowerFilteredExclusiveAbsInvoice
      delta n e q om N cap w z L X F := by
  unfold actualSixthOnlyExclusiveAbsInvoice
    actualPowerFilteredExclusiveAbsInvoice
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hstate
  exact congrArg List.sum
    (actual_one_sided_event_map_eq_large
      delta n e q om N cap w z L X F
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      state hstate (fun v : ℝ => |v|))

/-- The signed stopped discrepancy is the sum of the same event
occurrences evaluated with the retained original finite PLUS-Rosser
indices. In particular it is NOT the sum of two independent sieve
bounds, and the direct sixthFromBoth class is not removed. -/
theorem actual_stopped_delta_eq_power_filtered
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
          largeFifthOneSidedEventValue
            (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
            (P4AOriginalFull87LicensedSixthPolicy.policy
              delta n e q om (N : ℝ))
            N cap w ((N : ℝ) ^ epsilon) X F ev)).sum)).sum := by
  rw [P4AOriginalFull87SixthOnlyEventInvoice.actual_stopped_delta_eq_sixth_only
    delta n e q om N cap w z he hN epsilon heps X hX F]
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hstate
  simpa only [id_eq] using congrArg List.sum
    (actual_one_sided_event_map_eq_large
      delta n e q om N cap w z ((N : ℝ) ^ epsilon) X F
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      state hstate id)

/-- Replace, rather than add, the old stopped absolute invoice in
the existing full-physical inequality. The THREE separate pre-existing
outside/producer invoices remain byte-for-byte the same expressions,
in the same order, and are paid only once. -/
theorem abs_full_physical_le_power_filtered_invoice
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
    actualPowerFilteredExclusiveAbsInvoice delta n e q om N cap w z
      ((N : ℝ) ^ epsilon) X F +
    ((P4AOriginalFull87RawTrimSignedHighQ.rawOutsideHighQInvoice
        delta e q om N cap w z ((N : ℝ) ^ epsilon) X F +
      P4AOriginalFull87ThreeClassLeafInvoices.actualProducerThreeClassLeafBill
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X F) +
      P4AOriginalFull87LicensedOutsideThreeInvoices.licensedOutsideHighQInvoice
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X F) := by
  have h :=
    P4AOriginalFull87SixthOnlyEventInvoice.abs_full_physical_le_sixth_only_invoice
      delta n e q om N cap w z he hN epsilon heps X hX F
  rw [actual_sixth_only_abs_eq_power_filtered
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X F] at h
  exact h

end
end ImbalancedChen.P4AOriginalFull87LargeTailInvoice
