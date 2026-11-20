import ImbalancedChen.P1Full87TrueDOwned87Invoice
import ImbalancedChen.P4AOriginalFull87LicensedOutsideThreeInvoices
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A SAME-REAL-POLICY connection not present in the prior owned-RAW packet:
the true physical small-d RAW/LICENSED difference is joined to the
already existing actual LICENSED eighth owner+strict-trim partition and
the one-copy producer change ledger.  Both outside signed sums remain
in the equation, and they are allowed to cancel BEFORE taking abs.

This is NOT a certificate for any archived numerical saving, changed
query licence, signed PP coefficient class, or small H_N reserve.
The underlying finite lists preserve occurrences, signed beta weights,
actual parents, and their different RAW and LICENSED continuations.
-/

namespace ImbalancedChen.P1Full87TrueDThreeBookNetInvoice
noncomputable section
open Classical
open scoped BigOperators

open P1Full87TrueDPolicyDelta (trueDDeltaSupport trueDDeltaRho)
open P1Full87ActualTrueDOrderedGap
  (actual_full87_true_d_eq_ordered_events_and_frontiers)
open P4AOriginalFull87FifthSixthStoppedEvents
  (actualFifthSixthEvents FifthSixthStoppedEvent)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87LicensedOutsideThreeInvoices
  (rawOutsideSigned licensedOutsideSigned
   raw_minus_full_licensed_signed_eq_three_books)
open P4AOriginalFull87ProducerChangeInvoice
  (actualCellLedger licensedProducerInvoice
   actual_trim_to_licensed_signed_eq_ledger
   abs_trim_to_licensed_le_producer_invoice)

/-- Exact conservation for the ONE actual true-small-d coefficient
rho_LICENSED - rho_RAW.  The original RAW-minus-LICENSED ordered
fifth/sixth events are added to the left exactly once.
The RIGHT side contains (licensed outside - raw outside) MINUS the
one-copy raw-trim-to-licensed producer-change ledger.  Its per-Cell
ledger uses full state equality, not archive-label equality. -/
theorem actual_true_d_ordered_eq_net_outside_minus_producer
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let D := trueDDeltaSupport (R false) (S false) N cap w z
    let drho := trueDDeltaRho (R false) (S false) N cap w z L
    let stops := ((sharedRankFour e q om N cap w z).map (fun state =>
      ((actualFifthSixthEvents delta n e q om N cap w L X F state).map
        FifthSixthStoppedEvent.signedValue).sum)).sum
    (∑ d ∈ D, drho d * highQTest X F d) + stops =
      licensedOutsideSigned delta n e q om N cap w z L X F -
      rawOutsideSigned delta e q om N cap w z L X F -
      (∑ c : Cell, (actualCellLedger delta n e q om N cap w z L X F c).1) := by
  dsimp only
  have hphysical :=
    actual_full87_true_d_eq_ordered_events_and_frontiers
      delta n e q om N cap w z L X F
  have hbooks :=
    raw_minus_full_licensed_signed_eq_three_books
      delta n e q om N cap w z L X F
  dsimp only at hphysical
  linarith

/-- The only remaining difference after keeping the EXACT signed net
of both producers' outside lists is the already-counted matched/unmatched
producer ledger. No second raw-outside or licensed-outside absolute
payment occurs in this estimate. -/
theorem abs_true_d_ordered_minus_net_outside_le_producer
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let D := trueDDeltaSupport (R false) (S false) N cap w z
    let drho := trueDDeltaRho (R false) (S false) N cap w z L
    let stops := ((sharedRankFour e q om N cap w z).map (fun state =>
      ((actualFifthSixthEvents delta n e q om N cap w L X F state).map
        FifthSixthStoppedEvent.signedValue).sum)).sum
    |(∑ d ∈ D, drho d * highQTest X F d) + stops -
      (licensedOutsideSigned delta n e q om N cap w z L X F -
       rawOutsideSigned delta e q om N cap w z L X F)| ≤
      licensedProducerInvoice delta n e q om N cap w z L X F := by
  dsimp only
  have hcore := actual_true_d_ordered_eq_net_outside_minus_producer
    delta n e q om N cap w z L X F
  dsimp only at hcore
  have hinvoice := abs_trim_to_licensed_le_producer_invoice
    delta n e q om N cap w z L X F
  have hledger :
      |∑ c : Cell,
        (actualCellLedger delta n e q om N cap w z L X F c).1| ≤
        licensedProducerInvoice delta n e q om N cap w z L X F := by
    rw [← actual_trim_to_licensed_signed_eq_ledger
      delta n e q om N cap w z L X F]
    exact hinvoice
  calc
    |(∑ d ∈ trueDDeltaSupport
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om
          (N : ℝ) false) N cap w z,
        trueDDeltaRho
          (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
          (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om
            (N : ℝ) false) N cap w z L d * highQTest X F d) +
      ((sharedRankFour e q om N cap w z).map (fun state =>
        ((actualFifthSixthEvents delta n e q om N cap w L X F state).map
          FifthSixthStoppedEvent.signedValue).sum)).sum -
      (licensedOutsideSigned delta n e q om N cap w z L X F -
       rawOutsideSigned delta e q om N cap w z L X F)| =
      |-(∑ c : Cell,
        (actualCellLedger delta n e q om N cap w z L X F c).1)| := by
          rw [hcore]
          ring
    _ = |∑ c : Cell,
        (actualCellLedger delta n e q om N cap w z L X F c).1| := abs_neg _
    _ ≤ licensedProducerInvoice delta n e q om N cap w z L X F := hledger

/-- A possibly SHARPER finite envelope than charging both outside
lists separately: take their actual signed difference first.
This is not an H_N estimate; no sign of either source gain is assumed. -/
theorem abs_true_d_ordered_le_net_outside_plus_producer
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let D := trueDDeltaSupport (R false) (S false) N cap w z
    let drho := trueDDeltaRho (R false) (S false) N cap w z L
    let stops := ((sharedRankFour e q om N cap w z).map (fun state =>
      ((actualFifthSixthEvents delta n e q om N cap w L X F state).map
        FifthSixthStoppedEvent.signedValue).sum)).sum
    |(∑ d ∈ D, drho d * highQTest X F d) + stops| ≤
      |licensedOutsideSigned delta n e q om N cap w z L X F -
       rawOutsideSigned delta e q om N cap w z L X F| +
      licensedProducerInvoice delta n e q om N cap w z L X F := by
  dsimp only
  have hcore := actual_true_d_ordered_eq_net_outside_minus_producer
    delta n e q om N cap w z L X F
  dsimp only at hcore
  have hinvoice := abs_true_d_ordered_minus_net_outside_le_producer
    delta n e q om N cap w z L X F
  dsimp only at hinvoice
  let T := (∑ d ∈ trueDDeltaSupport
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
      (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om
        (N : ℝ) false) N cap w z,
      trueDDeltaRho
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om
          (N : ℝ) false) N cap w z L d * highQTest X F d) +
    ((sharedRankFour e q om N cap w z).map (fun state =>
      ((actualFifthSixthEvents delta n e q om N cap w L X F state).map
        FifthSixthStoppedEvent.signedValue).sum)).sum
  let B := licensedOutsideSigned delta n e q om N cap w z L X F -
    rawOutsideSigned delta e q om N cap w z L X F
  change |T| ≤ |B| +
    licensedProducerInvoice delta n e q om N cap w z L X F
  have he : |T - B| ≤
      licensedProducerInvoice delta n e q om N cap w z L X F := hinvoice
  calc
    |T| = |(T - B) + B| := by ring
    _ ≤ |T - B| + |B| := abs_add _ _
    _ ≤ licensedProducerInvoice delta n e q om N cap w z L X F + |B| :=
      add_le_add_right he _
    _ = |B| + licensedProducerInvoice delta n e q om N cap w z L X F :=
      add_comm _ _

end
end ImbalancedChen.P1Full87TrueDThreeBookNetInvoice
