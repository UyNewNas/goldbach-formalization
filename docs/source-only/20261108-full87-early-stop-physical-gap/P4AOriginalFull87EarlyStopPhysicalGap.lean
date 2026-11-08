import ImbalancedChen.P4AOriginalFull87ThreeClassLeafInvoices
import ImbalancedChen.P4AOriginalFull87CompleteSixthDispatch
import ImbalancedChen.P4AOriginalFull87LicensedSixthPolicy
import ImbalancedChen.P4AOriginalLicensedSixthSignedLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

IMPORTANT CORRECTION TO THE PRECEDING FIVE-CLASS FRONTIER BOUND.
The original complete-sixth RAW producer and the newly LICENSED sixth
producer do not agree on fifth/sixth decisions. Their depth-eight
frontiers are consequently different, but the FULL physical coefficient
also contains branches EXHAUSTED BEFORE depth eight. The five-class
frontier invoice does not cover those stopped branches.

This packet uses the existing genuine stoppedTest, the literal actual
physical small/rough rho, both genuine first-exit frontiers, and the
previous five physical leaf charges. It proves the full physical
difference equals the stopped difference PLUS the existing frontier
difference, then records the previously MISSING stop cost.

No stop cost is declared zero or small. No external PP, Gevrey,
saved87 authentication, H_N bound or reserve payment is supplied.
-/

namespace ImbalancedChen.P4AOriginalFull87EarlyStopPhysicalGap
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
  (signedTest stoppedTest attachedLeafTest
   physical_test_eq_signedTest signedTest_splice_eq_stopped_add_frontier)
open P4AOriginalLicensedSixthSignedLedger (physical)
open P4AOriginalFull87RawOwnerPartition (actualRawFrontier)
open P4AOriginalFull87RawTrimSignedHighQ
  (rawSignedHighQ rawOutsideHighQInvoice)
open P4AOriginalFull87ProducerChangeInvoice (licensedSignedHighQ)
open P4AOriginalFull87LicensedOutsideThreeInvoices
  (licensedFrontier licensedOutsideHighQInvoice)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87ThreeClassLeafInvoices
  (actualProducerThreeClassLeafBill
   abs_full_raw_minus_full_licensed_le_five_source_books)

/-- In any actual even-retaining policy, the rank-eight frontier
contribution is NOT the entire physical sum: exhausted lower-rank
branches are present as a separate literal stoppedTest. The proof
uses the genuine full-modulus sign-attached small Rosser rho. -/
theorem physical_eq_stopped_plus_rank8_frontier
    (R : Bool → List ℕ → Bool) (heven : ∀ pre, R true pre = true)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    physical R N cap w z L (highQTest X F) =
      stoppedTest 8 R (fun _ : ℕ => (1 : ℝ))
        (attachedLeafTest N cap 1 w L (highQTest X F))
        [] true 1 (roughPrimeUniverse N cap w z) +
      ((firstExitDepthFrontier 8 R (fun _ : ℕ => (1 : ℝ))
          [] true 1 (roughPrimeUniverse N cap w z)).map
        (fun s => signedTest R (fun _ : ℕ => (1 : ℝ))
          (attachedLeafTest N cap 1 w L (highQTest X F))
          s.selectedPrefix s.positive s.mass s.remaining)).sum := by
  have hroot := physical_test_eq_signedTest R heven
    N cap 1 w z L (highQTest X F)
  simp only [one_mul] at hroot
  have hsplit := signedTest_splice_eq_stopped_add_frontier 8 R R
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w L (highQTest X F))
    [] (roughPrimeUniverse N cap w z) true 1
  rw [firstExitDepthSplicePolicy_self] at hsplit
  change (∑ d ∈ actualSmallRoughModuli (R false) N cap w z,
    actualSmallRoughRho (R false) N cap w z L d *
      highQTest X F d) = _
  exact hroot.trans hsplit

/-- Exhausted-before-eight source from the ORIGINAL complete-sixth
producer. Its early admission history cannot be inferred from the
licensed producer's distinct fifth/sixth policy. -/
def rawStopped (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ)
    (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  stoppedTest 8
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w L (highQTest X F))
    [] true 1 (roughPrimeUniverse N cap w z)

/-- Exhausted-before-eight source from the actual NEW licensed sixth
producer, with its own potentially different historical admissions. -/
def licensedStopped (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (F : ℕ → ℝ) : ℝ :=
  stoppedTest 8
    (P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w L (highQTest X F))
    [] true 1 (roughPrimeUniverse N cap w z)

/-- The previously unaccounted stopped source is mathematically
unavoidable. The preceding three-/five-class invoice compares only
two frontier continuations, so it cannot by itself be promoted to the
FULL physical rho difference when sixth admission decisions differ.
This exact identity retains all early stopped terms, the original
one-copy frontier matching and all strict full-q tests. -/
theorem actual_full_physical_difference_eq_stops_and_frontiers
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    physical (P4AOriginalFull87CompleteSixthDispatch.policy
        e q om (N : ℝ)) N cap w z L (highQTest X F) -
      physical (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ)) N cap w z L (highQTest X F) =
    (rawStopped e q om N cap w z L X F -
      licensedStopped delta n e q om N cap w z L X F) +
    (((actualRawFrontier e q om N cap w z
        (fun _ : ℕ => (1 : ℝ))).map
        (rawSignedHighQ e q om N cap w L X F)).sum -
      ((licensedFrontier delta n e q om N cap w z).map
        (licensedSignedHighQ delta n e q om N cap w L X F)).sum) := by
  have hr := physical_eq_stopped_plus_rank8_frontier
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87CompleteSixthDispatch.policy_even e q om (N : ℝ))
    N cap w z L X F
  have hl := physical_eq_stopped_plus_rank8_frontier
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy_even
      delta n e q om (N : ℝ))
    N cap w z L X F
  change physical (P4AOriginalFull87CompleteSixthDispatch.policy
      e q om (N : ℝ)) N cap w z L (highQTest X F) =
    rawStopped e q om N cap w z L X F +
      ((actualRawFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map
        (rawSignedHighQ e q om N cap w L X F)).sum at hr
  change physical (P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)) N cap w z L (highQTest X F) =
    licensedStopped delta n e q om N cap w z L X F +
      ((licensedFrontier delta n e q om N cap w z).map
        (licensedSignedHighQ delta n e q om N cap w L X F)).sum at hl
  linarith

/-- Correct FULL coefficient bound: one early-stop discrepancy invoice
in addition to the predecessor's five disjoint depth-eight leaf sources.
This stop bill is NOT assumed zero or bounded by H_N. The earlier five
classes remain valid only for the difference of the two depth-eight
frontier continuations, not automatically for the entire physical rho.
-/
theorem abs_actual_full_physical_difference_le_stop_and_five_leaf_classes
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |physical (P4AOriginalFull87CompleteSixthDispatch.policy
        e q om (N : ℝ)) N cap w z L (highQTest X F) -
      physical (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ)) N cap w z L (highQTest X F)| ≤
      |rawStopped e q om N cap w z L X F -
        licensedStopped delta n e q om N cap w z L X F| +
      ((rawOutsideHighQInvoice delta e q om N cap w z L X F +
        actualProducerThreeClassLeafBill delta n e q om N cap w z L X F) +
        licensedOutsideHighQInvoice delta n e q om N cap w z L X F) := by
  rw [actual_full_physical_difference_eq_stops_and_frontiers]
  have hfront := abs_full_raw_minus_full_licensed_le_five_source_books
    delta n e q om N cap w z L X F
  exact (abs_add _ _).trans (add_le_add_left hfront _)

end
end ImbalancedChen.P4AOriginalFull87EarlyStopPhysicalGap
