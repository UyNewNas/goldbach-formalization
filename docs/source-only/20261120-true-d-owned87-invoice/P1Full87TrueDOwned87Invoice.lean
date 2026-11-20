import ImbalancedChen.P1Full87ActualTrueDOrderedGap
import ImbalancedChen.P4AOriginalFull87RawTrimSignedHighQ
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A missing SAME-POLICY join: the previous true-small-d RAW/LICENSED delta
invoice left the actual RAW rank-eight frontier opaque.  The existing
raw-owner/strict-trim partition is instantiated here on exactly that RAW
frontier, not on the separately produced licensed frontier.

The original Cell type has cardinality 87 and each Cell is the original
source-dictionary owner.  List.filter does not quotient duplicate
occurrences.  Every signed raw source contribution retains the original
selectedPrefix, mass, remaining suffix and full small/rough beta attachment.
The genuine unowned and owned-but-outside-trim signed terms are retained.

No equality of RAW and LICENSED frontiers, archival numerical saving,
smooth PP permission, small H_N budget or complete changed/tagged coverage
is asserted.  The source-only transitive import closure has not been staged.
-/

namespace ImbalancedChen.P1Full87TrueDOwned87Invoice

noncomputable section
open Classical
open scoped BigOperators

open P1Full87TrueDPolicyDelta (trueDDeltaSupport trueDDeltaRho)
open P1Full87ActualTrueDOrderedGap
  (actual_full87_true_d_eq_ordered_events_and_frontiers)
open P4AOriginalFull87RawOwnerPartition
  (actualRawFrontier actualUnownedFrontier)
open P4AOriginalFull87RawTrimSignedHighQ
  (rawSignedHighQ rawOwnedTrimmed rawOwnedTrimOmitted
   rawOutsideHighQInvoice actual_raw_highQ_unowned_trim_omitted
   abs_raw_highQ_minus_trimmed_le_outside_invoice)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87FifthSixthStoppedEvents
  (actualFifthSixthEvents FifthSixthStoppedEvent)
open P4AOriginalFull87LicensedOutsideThreeInvoices (licensedFrontier)
open P4AOriginalFull87ProducerChangeInvoice (licensedSignedHighQ)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87SourceDictionary (Cell)

/-- This is the ACTUAL d-coefficient difference, not a full-shell Q=ab
substitution.  The original raw eighth frontier is split by its actual
87-cell owner and the original strict trim, while the licensed frontier
stays independent.  All terms have their literal signed values. -/
theorem actual_true_d_87_owner_trim_and_outside_exact
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
       (((actualUnownedFrontier e q om N cap w z
            (fun _ : ℕ => (1 : ℝ))).map
           (rawSignedHighQ e q om N cap w L X F)).sum +
        (∑ c : Cell,
          ((rawOwnedTrimmed delta e q om N cap w z c).map
            (rawSignedHighQ e q om N cap w L X F)).sum) +
        (∑ c : Cell,
          ((rawOwnedTrimOmitted delta e q om N cap w z c).map
            (rawSignedHighQ e q om N cap w L X F)).sum))) -
      ((sharedRankFour e q om N cap w z).map (fun state =>
        ((actualFifthSixthEvents delta n e q om N cap w L X F state).map
          FifthSixthStoppedEvent.signedValue).sum)).sum := by
  dsimp only
  have hphysical :=
    actual_full87_true_d_eq_ordered_events_and_frontiers
      delta n e q om N cap w z L X F
  have hraw :=
    actual_raw_highQ_unowned_trim_omitted
      delta e q om N cap w z L X F
  dsimp only at hphysical
  rw [hraw] at hphysical
  linarith

/-- A quantitative FINITE invoice without discarding any real term.
After retaining the same 87 owned-and-trimmed RAW occurrences, the
error in reconstructing the physical true-d delta from the licensed
eighth frontier and RAW-minus-LICENSED fifth/sixth stopped events is
bounded by precisely the already-existing RAW unowned+omitted absolute
invoice.  No new payment is made and no claim it is o(H_N) is made. -/
theorem abs_true_d_delta_minus_owned87_reconstruction_le_outside
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let D := trueDDeltaSupport (R false) (S false) N cap w z
    let drho := trueDDeltaRho (R false) (S false) N cap w z L
    |(∑ d ∈ D, drho d * highQTest X F d) -
      (((licensedFrontier delta n e q om N cap w z).map
          (licensedSignedHighQ delta n e q om N cap w L X F)).sum -
       ((sharedRankFour e q om N cap w z).map (fun state =>
         ((actualFifthSixthEvents delta n e q om N cap w L X F state).map
           FifthSixthStoppedEvent.signedValue).sum)).sum -
       (∑ c : Cell,
         ((rawOwnedTrimmed delta e q om N cap w z c).map
           (rawSignedHighQ e q om N cap w L X F)).sum))| ≤
      rawOutsideHighQInvoice delta e q om N cap w z L X F := by
  dsimp only
  have hphysical :=
    actual_full87_true_d_eq_ordered_events_and_frontiers
      delta n e q om N cap w z L X F
  have houtside :=
    abs_raw_highQ_minus_trimmed_le_outside_invoice
      delta e q om N cap w z L X F
  dsimp only at hphysical
  have hrewrite :
    (∑ d ∈ trueDDeltaSupport
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om
          (N : ℝ) false) N cap w z,
       trueDDeltaRho
         (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
         (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om
           (N : ℝ) false) N cap w z L d * highQTest X F d) -
      (((licensedFrontier delta n e q om N cap w z).map
          (licensedSignedHighQ delta n e q om N cap w L X F)).sum -
       ((sharedRankFour e q om N cap w z).map (fun state =>
         ((actualFifthSixthEvents delta n e q om N cap w L X F state).map
           FifthSixthStoppedEvent.signedValue).sum)).sum -
       (∑ c : Cell,
         ((rawOwnedTrimmed delta e q om N cap w z c).map
           (rawSignedHighQ e q om N cap w L X F)).sum)) =
      -(((actualRawFrontier e q om N cap w z
           (fun _ : ℕ => (1 : ℝ))).map
            (rawSignedHighQ e q om N cap w L X F)).sum -
        (∑ c : Cell,
          ((rawOwnedTrimmed delta e q om N cap w z c).map
            (rawSignedHighQ e q om N cap w L X F)).sum)) := by
    rw [hphysical]
    ring
  rw [hrewrite, abs_neg]
  exact houtside

end
end ImbalancedChen.P1Full87TrueDOwned87Invoice
