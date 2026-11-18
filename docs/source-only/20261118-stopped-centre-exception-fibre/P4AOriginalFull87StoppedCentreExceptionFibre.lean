import ImbalancedChen.P4AOriginalFull87StoppedCentreUpperThird
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Continue the SAME receiverTest N-generated sharedRankFour fifth/sixth event population.
For N%4=0, N>=8, the original strict upper-third centre AP test on each
actual complete coprime a*(p::selectedAfter).prod is the SINGLE exceptional
fibre d=(N-2)/2. Its unchanged PLUS-beta and ordered occurrence sums are
made explicit below. NO substitution of fixed-policy physical rho for
stopped occurrence weights, no smallness assertion, and no new external
prime-distribution input.
-/

namespace ImbalancedChen.P4AOriginalFull87StoppedCentreExceptionFibre
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87StoppedCentreUpperThird
  (upperThirdCentre lowerThirdCentre centre_eq_lower_add_upper
   actual_event_full_modulus_coprime_target)
open P4AOriginalFull87UpperThirdCentreExact
  (centre_upper_third_exception_exact_one)
open P4AOriginalFull87UpperThirdCentreInvoice
  (centre_ap_upper_third_zero_unless_special)
open P4AOriginalFull87OrderedSixthSuffix (eventSelected)
open P4AOriginalFull87ActualSixthSuffix (eventSixthSuffix)
open P4AOriginalFull87FifthSignedPrimitive
  (actualFixedSignedFifthTail actual_fixed_fifth_tail_linear
   actual_stopped_delta_four_sources)
open P4AOriginalFull87EighthPrimeMeanLedger
  (receiverTest primeMass densityTest primitiveError modulusPrimeTerm)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthPlusAttachment largeFifthRosserIndices)
open P4AOriginalFull87CommonSixthSignedKernel
  (commonLargeSixthKernel commonSignedEventValue)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)

/-- The UNIQUE possible upper-third complete modulus; its value is
one when it is actually an allowed coprime centre fibre. -/
def exceptionalCentreFibre (N d : ℕ) : ℝ :=
  if d = (N - 2) / 2 then 1 else 0

/-- At a composite even centre divisible by four (N>=8), original
upper-third centre AP is EXACTLY this one-modulus fibre for every
target-coprime COMPLETE d. No upper-third bound is assumed. -/
theorem upper_third_centre_eq_exceptional_fibre
    (N d : ℕ) (hcomp : ¬ Nat.Prime N)
    (hmod : N % 4 = 0) (hN : 8 ≤ N) (hcop : d.Coprime N) :
    upperThirdCentre N d = exceptionalCentreFibre N d := by
  have heven : N % 2 = 0 := by omega
  have h2le : 2 ≤ N := by omega
  by_cases hd : d = (N - 2) / 2
  · subst d
    have hthird : N < 3 * ((N - 2) / 2) := by omega
    have hspecial : N - 2 = 2 * ((N - 2) / 2) := by omega
    have hcount : chenCentrePrimeAPCount N N ((N - 2) / 2) = 1 :=
      centre_upper_third_exception_exact_one N ((N - 2) / 2)
        hcomp heven h2le hcop hthird hspecial
    simp [upperThirdCentre, exceptionalCentreFibre, hthird, hcount]
  · have hnot : N - 2 ≠ 2 * d := by
      intro heq
      apply hd
      omega
    by_cases hthird : N < 3 * d
    · have hzero : chenCentrePrimeAPCount N N d = 0 :=
        centre_ap_upper_third_zero_unless_special
          N d hcomp hcop hthird hnot
      simp [upperThirdCentre, exceptionalCentreFibre, hthird, hd, hzero]
    · simp [upperThirdCentre, exceptionalCentreFibre, hthird, hd]

/-- Original, uncollapsed occurrence-level PLUS-beta fibre. It retains
each Rosser a in the original Finset and the literal STRICT high-q gate.
This is NOT the fixed physical rho coefficient. -/
def exceptionalFifthPlusFibre
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ) (p : ℕ) : ℝ :=
  ∑ a ∈ largeFifthRosserIndices N cap w X pre,
    if X < a * (p :: pre).prod ∧
         a * (p :: pre).prod = (N - 2) / 2 then
      actualSmallRosserPlus N cap w L a
    else 0

/-- Exact original PLUS-beta sum restricted to complete modulus q0.
This is a finite identity retaining each original a occurrence. -/
theorem large_fifth_exceptional_fibre_eq_plus_sum
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ) (p : ℕ) :
    largeFifthPlusAttachment N cap w L X
      (exceptionalCentreFibre N) pre p =
        exceptionalFifthPlusFibre N cap w L X pre p := by
  unfold largeFifthPlusAttachment exceptionalFifthPlusFibre
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hx : X < a * (p :: pre).prod
  · by_cases hq : a * (p :: pre).prod = (N - 2) / 2
    · simp [P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest,
        exceptionalCentreFibre, hx, hq]
    · simp [P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest,
        exceptionalCentreFibre, hx, hq]
  · simp [P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest,
      exceptionalCentreFibre, hx]

/-- The SAME ordered sixth list sums signed actual masses, not a
deduplicated modulus support or an unrelated fixed physical coefficient. -/
theorem common_sixth_exceptional_fibre_eq_original_weights
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (fifth : FifthStoppedEvent ℕ) :
    commonLargeSixthKernel N cap w L X
        (exceptionalCentreFibre N) fifth =
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          exceptionalFifthPlusFibre N cap w L X fifth.selectedAfter p)).sum := by
  unfold commonLargeSixthKernel
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [large_fifth_exceptional_fibre_eq_plus_sum]

/-- On one genuine original event, upper-third centre and the exceptional
q0 test have equal PLUS-beta sums at EVERY post-fifth occurrence.
The coprimality premise is supplied by the preceding actual history proof. -/
theorem actual_fifth_plus_upper_eq_exceptional
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 0) (hN : 8 ≤ N) :
    largeFifthPlusAttachment N cap w L X (upperThirdCentre N)
      fifth.selectedAfter p =
    largeFifthPlusAttachment N cap w L X (exceptionalCentreFibre N)
      fifth.selectedAfter p := by
  unfold largeFifthPlusAttachment
  apply Finset.sum_congr rfl
  intro a ha
  have haSmall : a ∈ actualSmallRosserSupport N cap w := by
    change a ∈ (actualSmallRosserSupport N cap w).filter
      (fun a => X ^ 5 < a ^ 5 * fifth.selectedAfter.prod ^ 6) at ha
    exact (Finset.mem_filter.mp ha).1
  have hp' : p ∈ eventSixthSuffix
      (FifthSixthStoppedEvent.fifthExclusive fifth) := by
    simpa [eventSixthSuffix] using hp
  have hc' := actual_event_full_modulus_coprime_target
    delta n e q om N cap w z L X
    state hstate (.fifthExclusive fifth) hfifth p hp' a haSmall
  have hc : (a * (p :: fifth.selectedAfter).prod).Coprime N := by
    simpa [eventSelected] using hc'
  rw [upper_third_centre_eq_exceptional_fibre N
    (a * (p :: fifth.selectedAfter).prod) hcomp hmod hN hc]

theorem actual_fifth_common_sixth_upper_eq_exceptional
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 0) (hN : 8 ≤ N) :
    commonLargeSixthKernel N cap w L X (upperThirdCentre N) fifth =
    commonLargeSixthKernel N cap w L X (exceptionalCentreFibre N) fifth := by
  unfold commonLargeSixthKernel
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [actual_fifth_plus_upper_eq_exceptional
    delta n e q om N cap w z L X state hstate fifth hfifth
    p hp hcomp hmod hN]

theorem actual_signed_event_upper_eq_exceptional
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 0) (hN : 8 ≤ N) :
    commonSignedEventValue N cap w L X (upperThirdCentre N) ev =
    commonSignedEventValue N cap w L X (exceptionalCentreFibre N) ev := by
  cases ev with
  | fifthExclusive fifth =>
      have hkern := actual_fifth_common_sixth_upper_eq_exceptional
        delta n e q om N cap w z L X state hstate fifth hev hcomp hmod hN
      cases hk : fifth.kind <;>
        simp [commonSignedEventValue, hk, hkern]
  | sixthFromBoth fifthSelected inner =>
      simp [commonSignedEventValue]

/-- The real original receiver-generated stopped ledger is EXACTLY the
signed coefficient at q0, with occurrence multiplicities and original
RAW/LICENSED signs. It need not be bounded by the physical-rho <=1. -/
theorem actual_fixed_fifth_upper_eq_exceptional_coefficient
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 0) (hN : 8 ≤ N) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (upperThirdCentre N) =
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (exceptionalCentreFibre N) := by
  unfold actualFixedSignedFifthTail
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hstate
  apply congrArg List.sum
  apply List.map_congr_left
  intro ev hev
  exact actual_signed_event_upper_eq_exceptional
    delta n e q om N cap w z L X state hstate ev hev hcomp hmod hN

/-- Original four-source centre invoice now splits into a CLOSED lower-third
and the explicit q0 signed occurrence coefficient, each paid ONCE. -/
theorem actual_fixed_fifth_centre_eq_lower_plus_exception
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 0) (hN : 8 ≤ N) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (chenCentrePrimeAPCount N N) =
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (lowerThirdCentre N) +
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (exceptionalCentreFibre N) := by
  let T : (ℕ → ℝ) → ℝ :=
    actualFixedSignedFifthTail delta n e q om N cap w z L X
  have hlin := actual_fixed_fifth_tail_linear
    delta n e q om N cap w z L X
    (lowerThirdCentre N) (upperThirdCentre N) (1 : ℝ) (1 : ℝ)
  have hfun : chenCentrePrimeAPCount N N =
      fun d => (1 : ℝ) * lowerThirdCentre N d +
        (1 : ℝ) * upperThirdCentre N d := by
    simpa only [one_mul] using centre_eq_lower_add_upper N
  change T (chenCentrePrimeAPCount N N) =
    T (lowerThirdCentre N) + T (exceptionalCentreFibre N)
  rw [hfun, hlin]
  simp only [one_mul]
  rw [actual_fixed_fifth_upper_eq_exceptional_coefficient
    delta n e q om N cap w z L X hcomp hmod hN]

/-- Same physical RAW-minus-LICENSED stopped delta, with the q0 fibre
isolated but NOT assumed small or identified with fixed physical rho. -/
theorem actual_stopped_four_sources_exception_mod_four_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hNr : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 0) (hN : 8 ≤ N) :
    rawStopped e q om N cap w z ((N : ℝ) ^ epsilon) X
        (receiverTest N) -
      licensedStopped delta n e q om N cap w z
        ((N : ℝ) ^ epsilon) X (receiverTest N) =
      primeMass N * actualFixedSignedFifthTail
          delta n e q om N cap w z ((N : ℝ) ^ epsilon) X densityTest +
      actualFixedSignedFifthTail
          delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
            (primitiveError N) -
      actualFixedSignedFifthTail
          delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
            (modulusPrimeTerm N) -
      actualFixedSignedFifthTail
          delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
            (lowerThirdCentre N) -
      actualFixedSignedFifthTail
          delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
            (exceptionalCentreFibre N) := by
  rw [actual_stopped_delta_four_sources
    delta n e q om N cap w z he hNr epsilon heps X hX]
  rw [actual_fixed_fifth_centre_eq_lower_plus_exception
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X hcomp hmod hN]
  ring

end
end ImbalancedChen.P4AOriginalFull87StoppedCentreExceptionFibre
