import ImbalancedChen.P4AOriginalFull87UpperThirdCentreExact
import ImbalancedChen.P4AOriginalFull87FifthSignedPrimitive
import ImbalancedChen.P4AOriginalFull87OrderedSixthSuffix
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The actual receiverTest-generated fifth/sixth event list and sharedRankFour
are held fixed. In the original strict upper-third, the centre-prime
correction vanishes for N % 4 = 2 at EACH complete a*b6 modulus. We prove
actual event full-modulus target-coprimality from ordered source provenance,
then remove upper-third centre payments from the original signed stopped
four-source identity. No physical-rho/occurrence coefficient equality or
asymptotic smallness is assumed. The complementary low-third remains.
-/

namespace ImbalancedChen.P4AOriginalFull87StoppedCentreUpperThird
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87UpperThirdCentreExact
  (centre_upper_third_zero_mod_four_two)
open P4AOriginalFull87OrderedSixthSuffix
  (eventSelected actual_event_joined_history_original_rough)
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

/-- An occurrence word selected from the actual rough universe has
target-coprime product, without converting the List to a set. -/
private theorem rough_word_product_coprime_target
    (N cap : ℕ) (w z : ℝ) (xs : List ℕ) :
    (∀ p ∈ xs, p ∈ roughPrimeUniverse N cap w z) →
      xs.prod.Coprime N := by
  induction xs with
  | nil => intro _; simp
  | cons p ps ih =>
      intro hxs
      have hp : p ∈ roughPrimeUniverse N cap w z :=
        hxs p (by simp)
      have hrest : ∀ t ∈ ps, t ∈ roughPrimeUniverse N cap w z := by
        intro t ht
        exact hxs t (by simp [ht])
      have hpc : p.Coprime N :=
        (mem_roughPrimeUniverse_prime hp).coprime_iff_not_dvd.mpr
          (mem_roughPrimeUniverse_not_dvd hp)
      have hpsc : ps.prod.Coprime N := ih hrest
      simpa [List.prod_cons] using hpc.mul_left hpsc

/-- Complete original a*(p::selected).prod is target-coprime for each
actual fifth/sixth occurrence and each actual PLUS-Rosser index. -/
theorem actual_event_full_modulus_coprime_target
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state)
    (p : ℕ) (hp : p ∈ eventSixthSuffix ev)
    (a : ℕ) (ha : a ∈ actualSmallRosserSupport N cap w) :
    (a * (p :: eventSelected ev).prod).Coprime N := by
  have hjoined := actual_event_joined_history_original_rough
    delta n e q om N cap w z L X (receiverTest N)
    state hstate ev hev
  have hrough : ∀ t ∈ p :: eventSelected ev,
      t ∈ roughPrimeUniverse N cap w z := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | hselected
    · exact hjoined.subset (List.mem_append.mpr (Or.inr hp))
    · have hrev : t ∈ (eventSelected ev).reverse := by
        simpa using hselected
      exact hjoined.subset (List.mem_append.mpr (Or.inl hrev))
  have hb : (p :: eventSelected ev).prod.Coprime N :=
    rough_word_product_coprime_target N cap w z _ hrough
  have haC : a.Coprime N :=
    actualSmallRosserSupport_coprime_target N cap w ha
  exact haC.mul_left hb

/-- Complementary strict upper-third and closed lower-third. -/
def upperThirdCentre (N d : ℕ) : ℝ :=
  if N < 3 * d then chenCentrePrimeAPCount N N d else 0

def lowerThirdCentre (N d : ℕ) : ℝ :=
  if 3 * d ≤ N then chenCentrePrimeAPCount N N d else 0

theorem centre_eq_lower_add_upper (N : ℕ) :
    chenCentrePrimeAPCount N N =
      fun d => lowerThirdCentre N d + upperThirdCentre N d := by
  funext d
  by_cases h : N < 3 * d
  · have hn : ¬ 3 * d ≤ N := Nat.not_le.mpr h
    simp [lowerThirdCentre, upperThirdCentre, h, hn]
  · have hl : 3 * d ≤ N := Nat.le_of_not_gt h
    simp [lowerThirdCentre, upperThirdCentre, h, hl]

/-- Pointwise upper-third centre vanishing retains every original
small-index beta and every post-fifth sixth occurrence. -/
theorem actual_fifth_large_plus_upper_centre_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 2) :
    largeFifthPlusAttachment N cap w L X (upperThirdCentre N)
      fifth.selectedAfter p = 0 := by
  unfold largeFifthPlusAttachment
  apply Finset.sum_eq_zero
  intro a ha
  have haSmall : a ∈ actualSmallRosserSupport N cap w := by
    change a ∈ (actualSmallRosserSupport N cap w).filter
      (fun a => X ^ 5 < a ^ 5 * fifth.selectedAfter.prod ^ 6) at ha
    exact (Finset.mem_filter.mp ha).1
  have hp' : p ∈ eventSixthSuffix
      (FifthSixthStoppedEvent.fifthExclusive fifth) := by
    simpa [eventSixthSuffix] using hp
  have hcop' := actual_event_full_modulus_coprime_target
    delta n e q om N cap w z L X
    state hstate (.fifthExclusive fifth) hfifth p hp' a haSmall
  have hcop : (a * (p :: fifth.selectedAfter).prod).Coprime N := by
    simpa [eventSelected] using hcop'
  have hz :
      upperThirdCentre N (a * (p :: fifth.selectedAfter).prod) = 0 := by
    by_cases ht : N < 3 * (a * (p :: fifth.selectedAfter).prod)
    · have h0 := centre_upper_third_zero_mod_four_two
        N (a * (p :: fifth.selectedAfter).prod) hcomp hmod hcop ht
      simp [upperThirdCentre, ht, h0]
    · simp [upperThirdCentre, ht]
  simp [P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest, hz]

theorem actual_fifth_common_sixth_upper_centre_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 2) :
    commonLargeSixthKernel N cap w L X (upperThirdCentre N) fifth = 0 := by
  have hmap :
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          largeFifthPlusAttachment N cap w L X (upperThirdCentre N)
            fifth.selectedAfter p)) =
        fifth.remainingAfter.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro p hp
    rw [actual_fifth_large_plus_upper_centre_zero
      delta n e q om N cap w z L X state hstate fifth hfifth
      p hp hcomp hmod]
    ring
  unfold commonLargeSixthKernel
  rw [hmap]
  simp

theorem actual_event_signed_upper_centre_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 2) :
    commonSignedEventValue N cap w L X (upperThirdCentre N) ev = 0 := by
  cases ev with
  | fifthExclusive fifth =>
      have hz := actual_fifth_common_sixth_upper_centre_zero
        delta n e q om N cap w z L X state hstate fifth hev hcomp hmod
      cases hk : fifth.kind <;>
        simp [commonSignedEventValue, hk, hz]
  | sixthFromBoth fifthSelected inner =>
      simp [commonSignedEventValue]

/-- Genuine sharedRankFour stopped ledger, unchanged receiverTest
producer, full physical modulus and occurrence multiplicities. -/
theorem actual_fixed_fifth_upper_third_centre_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 2) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (upperThirdCentre N) = 0 := by
  unfold actualFixedSignedFifthTail
  have houter :
      ((sharedRankFour e q om N cap w z).map (fun state =>
        ((actualFifthSixthWithoutBoth delta n e q om N cap w L X
          (receiverTest N) state).map
          (commonSignedEventValue N cap w L X (upperThirdCentre N))).sum)) =
        (sharedRankFour e q om N cap w z).map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro state hstate
    have hinner :
        ((actualFifthSixthWithoutBoth delta n e q om N cap w L X
            (receiverTest N) state).map
          (commonSignedEventValue N cap w L X (upperThirdCentre N))) =
        (actualFifthSixthWithoutBoth delta n e q om N cap w L X
          (receiverTest N) state).map (fun _ => (0 : ℝ)) := by
      apply List.map_congr_left
      intro ev hev
      exact actual_event_signed_upper_centre_zero
        delta n e q om N cap w z L X state hstate ev hev hcomp hmod
    rw [hinner]
    simp
  rw [houter]
  simp

/-- The original stopped centre correction now needs only the
closed lower-third band; not a new centre invoice. -/
theorem actual_fixed_fifth_centre_eq_lower_third
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 2) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (chenCentrePrimeAPCount N N) =
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (lowerThirdCentre N) := by
  let T : (ℕ → ℝ) → ℝ :=
    actualFixedSignedFifthTail delta n e q om N cap w z L X
  have hlin := actual_fixed_fifth_tail_linear
    delta n e q om N cap w z L X
    (lowerThirdCentre N) (upperThirdCentre N) (1 : ℝ) (1 : ℝ)
  have hz := actual_fixed_fifth_upper_third_centre_zero
    delta n e q om N cap w z L X hcomp hmod
  have hfun : chenCentrePrimeAPCount N N =
      fun d => (1 : ℝ) * lowerThirdCentre N d +
        (1 : ℝ) * upperThirdCentre N d := by
    simpa only [one_mul] using centre_eq_lower_add_upper N
  change T (chenCentrePrimeAPCount N N) = T (lowerThirdCentre N)
  rw [hfun, hlin, hz]
  ring

/-- Direct same-parent stopped RAW-minus-LICENSED four-source equation;
primitive, modulus-prime and density tests are unchanged. -/
theorem actual_stopped_four_sources_lower_centre_mod_four_two
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 2) :
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
            (lowerThirdCentre N) := by
  rw [actual_stopped_delta_four_sources
    delta n e q om N cap w z he hN epsilon heps X hX]
  rw [actual_fixed_fifth_centre_eq_lower_third
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X hcomp hmod]

end
end ImbalancedChen.P4AOriginalFull87StoppedCentreUpperThird
