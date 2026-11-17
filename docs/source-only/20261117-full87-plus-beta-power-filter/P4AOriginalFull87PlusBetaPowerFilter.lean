import ImbalancedChen.P4AOriginalFull87FifthRankPowerTail
import ImbalancedChen.P4AOriginalFull87SixthOnlyEventInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

This packet plugs the actual fifth-rank fifth-power test into the ORIGINAL
finite PLUS-Rosser attachment.  No a or sixth-prime occurrence is discarded
unless its exact full modulus a*b6 is provably outside the strict high-q
support.  The remaining a^5*b5^6 > X^5 terms retain their original signed
coefficient, sixth-prime order, mass, and physical high-q test.

The original fifthSixthWithoutBoth list is not reconstructed. Its
sixthFromBoth occurrences are unchanged. This is a finite algebraic
restriction, NOT a numerical payment for the large fifth-weight tail.
-/

namespace ImbalancedChen.P4AOriginalFull87PlusBetaPowerFilter
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87SixthOnlyEventInvoice
  (sixthPositiveContinuation sixthOnlyFifthValue sixthOnlyOneSidedValue)
open P4AOriginalFull87ShallowOneSidedInvoice (shallowFifthValue)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87FifthRankPowerTail
  (actual_small_fifth_weight_excludes_highq)

/-- Filter only the ORIGINAL small-Rosser index. The strict endpoint is
the contraposition of the exact fifth-power modulus inequality, and the
index remains a genuine member of the original support finset. -/
def largeFifthRosserIndices
    (N cap : ℕ) (w : ℝ) (X : ℕ) (pre : List ℕ) : Finset ℕ :=
  (actualSmallRosserSupport N cap w).filter
    (fun a => X ^ 5 < a ^ 5 * pre.prod ^ 6)

/-- The literal surviving PLUS-beta finite sum for ONE actual sixth
candidate p, with the original complete modulus a*(p::pre).prod. -/
def largeFifthPlusAttachment
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (p : ℕ) : ℝ :=
  ∑ a ∈ largeFifthRosserIndices N cap w X pre,
    actualSmallRosserPlus N cap w L a *
      highQTest X F (a * (p :: pre).prod)

/-- Exact per-(a,p) support reduction. The complete PLUS-beta finite
sum is retained, not replaced with a rough-only or signed-free test.
Every excluded summand vanishes by the previously proved *actual* fifth
event's power inequality and the strict original high-q indicator. -/
theorem actual_fifth_plus_attachment_eq_large
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X F state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter) :
    attachedLeafTest N cap 1 w L (highQTest X F)
      true (p :: fifth.selectedAfter) =
    largeFifthPlusAttachment N cap w L X F fifth.selectedAfter p := by
  unfold attachedLeafTest largeFifthPlusAttachment largeFifthRosserIndices
  simp only [ite_true, one_mul]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hlarge : X ^ 5 < a ^ 5 * fifth.selectedAfter.prod ^ 6
  · simp [hlarge]
  · have hsmall : a ^ 5 * fifth.selectedAfter.prod ^ 6 ≤ X ^ 5 :=
      Nat.le_of_not_gt hlarge
    have hnot : ¬ X < a * (p :: fifth.selectedAfter).prod :=
      actual_small_fifth_weight_excludes_highq
        delta n e q om N cap w z L X F
        state hstate fifth hfifth p hp a hsmall
    simp [hlarge, highQTest, hnot]

/-- The same ordered actual post-fifth sixth carrier. Both the
acceptance test and signed mass are unchanged; only the finite
PLUS-beta summation has its provably zero small fifth-weight terms
deleted. No occurrence can be merged by this List.map identity. -/
def largeFifthSixthContinuation
    (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (fifth : FifthStoppedEvent ℕ) : ℝ :=
  (fifth.remainingAfter.map (fun p =>
    if R true (p :: fifth.selectedAfter) = true then
      signedTreeCoefficient true fifth.massAfter *
        largeFifthPlusAttachment N cap w L X F fifth.selectedAfter p
    else 0)).sum

theorem actual_fifth_sixth_continuation_eq_large
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (R : Bool → List ℕ → Bool)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X F state) :
    sixthPositiveContinuation R
      (attachedLeafTest N cap 1 w L (highQTest X F))
      fifth.selectedAfter fifth.massAfter fifth.remainingAfter =
    largeFifthSixthContinuation R N cap w L X F fifth := by
  unfold sixthPositiveContinuation largeFifthSixthContinuation
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have h := actual_fifth_plus_attachment_eq_large
    delta n e q om N cap w z L X F state hstate fifth hfifth p hp
  by_cases hr : R true (p :: fifth.selectedAfter) = true
  · simpa [hr] using
      congrArg (fun t : ℝ => signedTreeCoefficient true fifth.massAfter * t) h
  · simp [hr]

/-- Fifth events retain their RAW-only or LICENSED-only sign.
The impossible-to-eliminate both branch is kept unchanged, rather
than being silently assigned an invented mask or analytic bound. -/
def largeFifthOneSidedValue
    (R S : Bool → List ℕ → Bool)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (fifth : FifthStoppedEvent ℕ) : ℝ :=
  match fifth.kind with
  | .rawOnly => largeFifthSixthContinuation R N cap w L X F fifth
  | .licensedOnly => -largeFifthSixthContinuation S N cap w L X F fifth
  | .both => shallowFifthValue R S
      (attachedLeafTest N cap 1 w L (highQTest X F)) fifth

theorem actual_fifth_one_sided_value_eq_large
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (R S : Bool → List ℕ → Bool)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X F state) :
    sixthOnlyFifthValue R S
      (attachedLeafTest N cap 1 w L (highQTest X F)) fifth =
    largeFifthOneSidedValue R S N cap w L X F fifth := by
  have hr := actual_fifth_sixth_continuation_eq_large
    delta n e q om N cap w z L X F R state hstate fifth hfifth
  have hs := actual_fifth_sixth_continuation_eq_large
    delta n e q om N cap w z L X F S state hstate fifth hfifth
  cases hk : fifth.kind with
  | rawOnly =>
      simpa [sixthOnlyFifthValue, largeFifthOneSidedValue, hk] using hr
  | licensedOnly =>
      simpa [sixthOnlyFifthValue, largeFifthOneSidedValue, hk] using
        congrArg (fun t : ℝ => -t) hs
  | both =>
      simp [sixthOnlyFifthValue, largeFifthOneSidedValue, hk]

/-- Replacement evaluation on EXACTLY the old one-sided event list.
Already-sixth sixthFromBoth occurrences retain their old value. -/
def largeFifthOneSidedEventValue
    (R S : Bool → List ℕ → Bool)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      largeFifthOneSidedValue R S N cap w L X F fifth
  | .sixthFromBoth pre fifth =>
      sixthOnlyOneSidedValue R S
        (attachedLeafTest N cap 1 w L (highQTest X F))
        (.sixthFromBoth pre fifth)

theorem actual_one_sided_event_value_eq_large
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (R S : Bool → List ℕ → Bool)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X F state) :
    sixthOnlyOneSidedValue R S
      (attachedLeafTest N cap 1 w L (highQTest X F)) ev =
    largeFifthOneSidedEventValue R S N cap w L X F ev := by
  cases ev with
  | fifthExclusive fifth =>
      simpa only [sixthOnlyOneSidedValue, largeFifthOneSidedEventValue] using
        (actual_fifth_one_sided_value_eq_large
          delta n e q om N cap w z L X F R S state hstate fifth hev)
  | sixthFromBoth pre fifth =>
      rfl

/-- Original event occurrence map conservation. This statement is
polymorphic in g, so both signed (g=id) and absolute (g=abs) ledger
substitutions are obtained WITHOUT changing the List or its order. -/
theorem actual_one_sided_event_map_eq_large
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (R S : Bool → List ℕ → Bool)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (g : ℝ → ℝ) :
    ((actualFifthSixthWithoutBoth delta n e q om N cap w L X F state).map
      (fun ev => g (sixthOnlyOneSidedValue R S
        (attachedLeafTest N cap 1 w L (highQTest X F)) ev))) =
    ((actualFifthSixthWithoutBoth delta n e q om N cap w L X F state).map
      (fun ev => g (largeFifthOneSidedEventValue R S
        N cap w L X F ev))) := by
  apply List.map_congr_left
  intro ev hev
  exact congrArg g (actual_one_sided_event_value_eq_large
    delta n e q om N cap w z L X F R S state hstate ev hev)

end
end ImbalancedChen.P4AOriginalFull87PlusBetaPowerFilter
