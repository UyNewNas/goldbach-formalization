import ImbalancedChen.P4AOriginalFull87StoppedQ0QuotientDivisor
import ImbalancedChen.P4AOriginalFull87FifthRankPowerTail
import ImbalancedChen.P4AOriginalFull87OrderedSixthSuffix
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A genuine fifth-exclusive event contains FIVE distinct selected rough
primes; every candidate sixth p is strictly smaller than those selected
primes. On the original q0=(N-2)/2 centre-fibre, a nonzero PLUS term
would give a * (p :: selectedAfter).prod = q0. If q0 is prime, both p
and one of the five selected primes would equal q0. This contradicts
their strict chronological order. Hence the whole stopped centre
EXCEPTION coefficient vanishes for prime q0, with NO fixed-physical-rho
identification, no missing fifth events and no occurrence deduplication.

The proof does NOT assert this for composite q0; nor does it pay the
remaining low-third centre or other primitive/modulus-prime invoices.
The real event lists are generated once with receiverTest N.
-/

namespace ImbalancedChen.P4AOriginalFull87StoppedQ0PrimeExclusion
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87StoppedCentreExceptionFibre
  (exceptionalCentreFibre exceptionalFifthPlusFibre
   common_sixth_exceptional_fibre_eq_original_weights
   actual_fixed_fifth_centre_eq_lower_plus_exception
   actual_fixed_fifth_upper_eq_exceptional_coefficient)
open P4AOriginalFull87StoppedQ0QuotientDivisor
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87CommonSixthSignedKernel
  (commonLargeSixthKernel commonSignedEventValue)
open P4AOriginalFull87FifthSignedPrimitive
  (actualFixedSignedFifthTail)
open P4AOriginalFull87FifthRankPowerTail
  (actual_fifth_exclusive_length_five)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_event_joined_history_original_rough
   actual_event_suffix_lt_every_selected)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87StoppedCentreUpperThird (lowerThirdCentre)

/-- Literal list occurrences, even if repeated, divide the literal
product. This helper does NOT turn a list into a set. -/
private theorem member_dvd_list_product
    (xs : List ℕ) (r : ℕ) (hr : r ∈ xs) : r ∣ xs.prod := by
  induction xs with
  | nil => simp at hr
  | cons x tail ih =>
      rcases List.mem_cons.mp hr with h | ht
      · subst r
        refine ⟨tail.prod, ?_⟩
        simp [List.prod_cons]
      · obtain ⟨k, hk⟩ := ih ht
        refine ⟨x * k, ?_⟩
        calc
          (x :: tail).prod = x * tail.prod := rfl
          _ = x * (r * k) := by rw [hk]
          _ = r * (x * k) := by ac_rfl

/-- A prime cannot equal a complete product containing TWO strictly
ordered prime factors. The auxiliary Rosser index a is arbitrary;
in particular a=0 or a=1 is not silently excluded. -/
private theorem prime_cannot_be_two_ordered_factors
    (Q a p r : ℕ) (pre : List ℕ)
    (hQ : Nat.Prime Q) (hp : Nat.Prime p) (hr : Nat.Prime r)
    (hrmem : r ∈ pre) (hpr : p < r)
    (hprod : a * (p :: pre).prod = Q) : False := by
  have hpdiv : p ∣ Q := by
    refine ⟨a * pre.prod, ?_⟩
    calc
      Q = a * (p * pre.prod) := by simpa [List.prod_cons] using hprod.symm
      _ = p * (a * pre.prod) := by ac_rfl
  have hrdiv : r ∣ Q := by
    obtain ⟨k, hk⟩ := member_dvd_list_product pre r hrmem
    refine ⟨a * p * k, ?_⟩
    calc
      Q = a * (p * pre.prod) := by simpa [List.prod_cons] using hprod.symm
      _ = a * (p * (r * k)) := by rw [hk]
      _ = r * (a * p * k) := by ac_rfl
  have heqp : p = Q := (Nat.prime_dvd_prime_iff_eq hp hQ).mp hpdiv
  have heqr : r = Q := (Nat.prime_dvd_prime_iff_eq hr hQ).mp hrdiv
  omega

/-- On the ORIGINAL receiver-generated fifthExclusive event, the
q0 fibre PLUS-beta sum vanishes if q0 itself is prime. The fifth
history is proved to contain five actual selected rough primes; the
sixth p belongs to its genuine remainingAfter LIST. -/
theorem actual_fifth_q0_plus_zero_of_prime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (hQ : Nat.Prime ((N - 2) / 2)) :
    exceptionalFifthPlusFibre N cap w L X fifth.selectedAfter p = 0 := by
  have hlen : fifth.selectedAfter.length = 5 :=
    actual_fifth_exclusive_length_five
      delta n e q om N cap w z L X (receiverTest N)
      state hstate fifth hfifth
  obtain ⟨r, hr⟩ : ∃ r, r ∈ fifth.selectedAfter := by
    cases hs : fifth.selectedAfter with
    | nil => simp [hs] at hlen
    | cons r tail => exact ⟨r, by simp [hs]⟩
  have hjoin :
      fifth.selectedAfter.reverse ++ fifth.remainingAfter <+
        roughPrimeUniverse N cap w z := by
    simpa [P4AOriginalFull87OrderedSixthSuffix.eventSelected,
      P4AOriginalFull87ActualSixthSuffix.eventSixthSuffix] using
      (actual_event_joined_history_original_rough
        delta n e q om N cap w z L X (receiverTest N)
        state hstate (.fifthExclusive fifth) hfifth)
  have hpprime : Nat.Prime p :=
    mem_roughPrimeUniverse_prime
      (hjoin.subset (List.mem_append.mpr (Or.inr hp)))
  have hrmem : r ∈ fifth.selectedAfter.reverse := by
    simpa using hr
  have hrprime : Nat.Prime r :=
    mem_roughPrimeUniverse_prime
      (hjoin.subset (List.mem_append.mpr (Or.inl hrmem)))
  have hpr : p < r :=
    actual_event_suffix_lt_every_selected
      delta n e q om N cap w z L X (receiverTest N)
      state hstate (.fifthExclusive fifth) hfifth p hp r hr
  unfold exceptionalFifthPlusFibre
  apply Finset.sum_eq_zero
  intro a ha
  have hneq :
      a * (p :: fifth.selectedAfter).prod ≠ (N - 2) / 2 := by
    intro heq
    exact prime_cannot_be_two_ordered_factors
      ((N - 2) / 2) a p r fifth.selectedAfter
      hQ hpprime hrprime hr hpr heq
  simp [hneq]

/-- Each original fifth-exclusive event, with every actual sixth
occurrence and the original signed fifth mass, has ZERO q0 contribution.
No absolute-value invoice and no multiplicity collapse is needed. -/
theorem actual_common_sixth_q0_zero_of_prime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (hQ : Nat.Prime ((N - 2) / 2)) :
    commonLargeSixthKernel N cap w L X (exceptionalCentreFibre N) fifth = 0 := by
  rw [common_sixth_exceptional_fibre_eq_original_weights]
  have hmap :
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          exceptionalFifthPlusFibre N cap w L X fifth.selectedAfter p)) =
      fifth.remainingAfter.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro p hp
    rw [actual_fifth_q0_plus_zero_of_prime
      delta n e q om N cap w z L X state hstate fifth hfifth p hp hQ]
    simp
  rw [hmap]
  simp

/-- The other event constructors retain their genuine original
values (syntactically zero in commonSignedEventValue), while a real
fifth-exclusive constructor vanishes by the previous theorem. -/
theorem actual_signed_q0_event_zero_of_prime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state)
    (hQ : Nat.Prime ((N - 2) / 2)) :
    commonSignedEventValue N cap w L X (exceptionalCentreFibre N) ev = 0 := by
  cases ev with
  | fifthExclusive fifth =>
      have hz := actual_common_sixth_q0_zero_of_prime
        delta n e q om N cap w z L X state hstate fifth hev hQ
      cases hk : fifth.kind <;>
        simp [commonSignedEventValue, hk, hz]
  | sixthFromBoth pre fifth =>
      simp [commonSignedEventValue]

/-- Genuine full stopped q0 signed occurrence coefficient vanishes on
the prime-q0 subfamily. This is a conclusion about the SAME actual
sharedRankFour and receiverTest-generated fifth/sixth lists, not an
identification with fixed-policy physical rho. -/
theorem actual_fixed_fifth_q0_zero_of_prime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (hQ : Nat.Prime ((N - 2) / 2)) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (exceptionalCentreFibre N) = 0 := by
  let events : FirstExitDepthState ℕ →
      List (FifthSixthStoppedEvent ℕ) :=
    fun state => actualFifthSixthWithoutBoth
      delta n e q om N cap w L X (receiverTest N) state
  have hstate (state : FirstExitDepthState ℕ)
      (hs : state ∈ sharedRankFour e q om N cap w z) :
      ((events state).map
        (commonSignedEventValue N cap w L X
          (exceptionalCentreFibre N))).sum = 0 := by
    have hmap :
        (events state).map
          (commonSignedEventValue N cap w L X
            (exceptionalCentreFibre N)) =
          (events state).map (fun _ => (0 : ℝ)) := by
      apply List.map_congr_left
      intro ev hev
      exact actual_signed_q0_event_zero_of_prime
        delta n e q om N cap w z L X state hs ev hev hQ
    rw [hmap]
    simp
  change ((sharedRankFour e q om N cap w z).map (fun state =>
    ((events state).map
      (commonSignedEventValue N cap w L X
        (exceptionalCentreFibre N))).sum)).sum = 0
  have houter :
      (sharedRankFour e q om N cap w z).map (fun state =>
        ((events state).map (commonSignedEventValue N cap w L X
          (exceptionalCentreFibre N))).sum) =
        (sharedRankFour e q om N cap w z).map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro state hs
    exact hstate state hs
  rw [houter]
  simp

/-- Consequently, for the prime-q0 subfamily, the ORIGINAL full
centre invoice equals its CLOSED lower-third invoice. The exceptional
upper-third contribution is not paid a second time. -/
theorem actual_fixed_fifth_centre_eq_lower_of_prime_q0
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 0)
    (hN : 8 ≤ N) (hQ : Nat.Prime ((N - 2) / 2)) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (chenCentrePrimeAPCount N N) =
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (lowerThirdCentre N) := by
  rw [actual_fixed_fifth_centre_eq_lower_plus_exception
    delta n e q om N cap w z L X hcomp hmod hN]
  rw [actual_fixed_fifth_q0_zero_of_prime
    delta n e q om N cap w z L X hQ]
  ring

end
end ImbalancedChen.P4AOriginalFull87StoppedQ0PrimeExclusion
