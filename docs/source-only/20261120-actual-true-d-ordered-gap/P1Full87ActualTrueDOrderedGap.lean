import ImbalancedChen.P1Full87TrueDReceiverDelta
import ImbalancedChen.P4AOriginalFull87FifthSixthStoppedEvents
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Correction to the previous true-d policy delta packet: the actual
full87 RAW producer is CompleteSixthDispatch.policy; the actual
LICENSED producer is LicensedSixthPolicy.policy. They are NOT the
generic policy5 / arbitrary rank-six fresh pair.

This packet instantiates the SAME true small/rough physical modulus d
at those literal producers, then connects their signed coefficient
difference to the EXISTING ordered sharedRankFour fifth/sixth stopped
events and the two genuinely different depth-eight frontiers.

Important: rho_licensed - rho_raw has the OPPOSITE sign to the prior
RAW - LICENSED stopped/event invoice. The early stop event source is
not the entire physical coefficient: the two rank-eight frontiers
must both remain present, each with its own actual policy.

No complete manuscript rho_N licence, PP estimate, smooth weight,
H_N payment or numerical saved87 certification is claimed here.
-/

namespace ImbalancedChen.P1Full87ActualTrueDOrderedGap

noncomputable section
open Classical
open scoped BigOperators

open P1Full87TrueDPolicyDelta
  (trueDDeltaSupport trueDDeltaRho trueDDeltaRho_test)
open P1Full87TrueDReceiverDelta
  (trueD_delta_receiver_primitive_invoice)
open P1Pair12RetainedSignedSource
  (signedTest attachedLeafTest physical_test_eq_signedTest)
open P4AOriginalFull87EarlyStopPhysicalGap
  (rawStopped licensedStopped
   actual_full_physical_difference_eq_stops_and_frontiers)
open P4AOriginalFull87FifthSixthStoppedEvents
  (FifthSixthStoppedEvent actualFifthSixthEvents
   actual_stopped_difference_eq_fifth_sixth_events)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87RawOwnerPartition (actualRawFrontier)
open P4AOriginalFull87RawTrimSignedHighQ (rawSignedHighQ)
open P4AOriginalFull87LicensedOutsideThreeInvoices (licensedFrontier)
open P4AOriginalFull87ProducerChangeInvoice (licensedSignedHighQ)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)

/-- A literal full87 RAW/Licensed true-d signed coefficient, tested by
ANY arithmetic function G, is the difference of their signed root
recursions. This is not a difference of two unrelated AP estimates. -/
theorem actual_full87_true_d_eq_signed_roots
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let D := trueDDeltaSupport (R false) (S false) N cap w z
    let drho := trueDDeltaRho (R false) (S false) N cap w z L
    (∑ d ∈ D, drho d * G d) =
      signedTest S (fun _ : ℕ => 1)
        (attachedLeafTest N cap 1 w L G)
        [] true 1 (roughPrimeUniverse N cap w z) -
      signedTest R (fun _ : ℕ => 1)
        (attachedLeafTest N cap 1 w L G)
        [] true 1 (roughPrimeUniverse N cap w z) := by
  dsimp only
  have hdelta := trueDDeltaRho_test
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ) false)
    N cap w z L G
  have hlicensed := physical_test_eq_signedTest
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy_even
      delta n e q om (N : ℝ))
    N cap 1 w z L G
  have hraw := physical_test_eq_signedTest
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87CompleteSixthDispatch.policy_even e q om (N : ℝ))
    N cap 1 w z L G
  simp only [one_mul] at hlicensed hraw
  rw [hdelta, hlicensed, hraw]

/-- Exact ordered full87 physical identity at the true small modulus.
It has the SIGN of rho_licensed-rho_raw, opposite to the stopped
RAW-LICENSED event values. The genuine RAW and Licensed rank-eight
frontier sources are separate. Both ordered lists retain repetitions. -/
theorem actual_full87_true_d_eq_ordered_events_and_frontiers
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let D := trueDDeltaSupport (R false) (S false) N cap w z
    let drho := trueDDeltaRho (R false) (S false) N cap w z L
    (∑ d ∈ D, drho d * highQTest X F d) =
      (((licensedFrontier delta n e q om N cap w z).map
         (licensedSignedHighQ delta n e q om N cap w L X F)).sum -
       ((actualRawFrontier e q om N cap w z
           (fun _ : ℕ => (1 : ℝ))).map
         (rawSignedHighQ e q om N cap w L X F)).sum) -
      ((sharedRankFour e q om N cap w z).map (fun state =>
        ((actualFifthSixthEvents delta n e q om N cap w L X F state).map
          FifthSixthStoppedEvent.signedValue).sum)).sum := by
  dsimp only
  have htest :
      (∑ d ∈ trueDDeltaSupport
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om
          (N : ℝ) false) N cap w z,
        trueDDeltaRho
          (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
          (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om
            (N : ℝ) false) N cap w z L d * highQTest X F d) =
      P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87LicensedSixthPolicy.policy
          delta n e q om (N : ℝ)) N cap w z L (highQTest X F) -
      P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87CompleteSixthDispatch.policy
          e q om (N : ℝ)) N cap w z L (highQTest X F) := by
    simpa only [P4AOriginalLicensedSixthSignedLedger.physical] using
      (trueDDeltaRho_test
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om
          (N : ℝ) false) N cap w z L (highQTest X F))
  have hfull :=
    actual_full_physical_difference_eq_stops_and_frontiers
      delta n e q om N cap w z L X F
  have hstopped :=
    actual_stopped_difference_eq_fifth_sixth_events
      delta n e q om N cap w z L X F
  rw [htest]
  calc
    _ = -(P4AOriginalLicensedSixthSignedLedger.physical
            (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
            N cap w z L (highQTest X F) -
          P4AOriginalLicensedSixthSignedLedger.physical
            (P4AOriginalFull87LicensedSixthPolicy.policy
              delta n e q om (N : ℝ))
            N cap w z L (highQTest X F)) := by ring
    _ = -((rawStopped e q om N cap w z L X F -
              licensedStopped delta n e q om N cap w z L X F) +
          (((actualRawFrontier e q om N cap w z
              (fun _ : ℕ => (1 : ℝ))).map
             (rawSignedHighQ e q om N cap w L X F)).sum -
           ((licensedFrontier delta n e q om N cap w z).map
             (licensedSignedHighQ delta n e q om N cap w L X F)).sum)) := by
      rw [hfull]
    _ = _ := by
      rw [hstopped]
      ring

/-- The same LITERAL full87 raw/licensed true-d coefficient also
controls the exact receiver divisor difference and its three finite
primitive terms. This is not the signed smooth PP estimate. -/
theorem actual_full87_true_d_receiver_primitive_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (hN : Even N) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let D := trueDDeltaSupport (R false) (S false) N cap w z
    let drho := trueDDeltaRho (R false) (S false) N cap w z L
    (∑ r ∈ chenPrimeReceiverSource N,
      (physicalDivisorSum
          (actualSmallRoughModuli (S false) N cap w z)
          (actualSmallRoughRho (S false) N cap w z L) r -
       physicalDivisorSum
          (actualSmallRoughModuli (R false) N cap w z)
          (actualSmallRoughRho (R false) N cap w z L) r)) =
      ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum D drho +
      (∑ d ∈ D, drho d *
        finitePrimitiveDiscrepancy
          (chenAdditivePrimeCarrier N) (fun _ => 1) N d) -
      (∑ d ∈ D, drho d *
        (chenPrimeDivisorCount N d / (Nat.totient d : ℝ))) := by
  dsimp only
  exact trueD_delta_receiver_primitive_invoice
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om
      (N : ℝ) false) N cap w z L hN

end
end ImbalancedChen.P1Full87ActualTrueDOrderedGap
