import ImbalancedChen.P4AOriginalFull87StoppedQ0PrimeExclusion
import ImbalancedChen.P4AOriginalFull87FifthRankPowerTail
import ImbalancedChen.P4AOriginalFull87OrderedSixthSuffix
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

P1.4 original stopped q0 exception: an actual fifth-exclusive selected history
has five DISTINCT prime factors, and the actual smaller sixth candidate
is distinct from all of them. Hence any COMPLETE original PLUS-beta fibre
a * (p :: selectedAfter).prod = q0 forces at least SIX DISTINCT
prime divisors of q0. If q0.primeFactors.card < 6 the entire signed
stopped centre exception is EXACTLY zero (including composite prime powers,
semiprimes and all other low-prime-support q0).

The event population remains receiverTest N / sharedRankFour; no change
to beta, sixth ordered occurrence list, high-q strict gate, or signed mass.
The upper-third centre bridge still requires N >= 8, composite and N % 4 = 0.
This is finite arithmetic support, NOT a global signed error estimate.
-/
namespace ImbalancedChen.P4AOriginalFull87StoppedQ0FactorSupportSix
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

/-- Any genuine six-factor COMPLETE modulus fibre contains six
DISTINCT prime divisors. The all-prime and Nodup hypotheses are proved
below from the original joined sublist of roughPrimeUniverse; they are
not synthetic certificates or extra number-theoretic assumptions. -/
private theorem six_distinct_prime_factors_of_product
    (Q a p : ℕ) (pre : List ℕ)
    (hQ : Q ≠ 0) (hlen : pre.length = 5)
    (hprime : ∀ r ∈ p :: pre, Nat.Prime r)
    (hno : (p :: pre).Nodup)
    (hprod : a * (p :: pre).prod = Q) :
    6 ≤ Q.primeFactors.card := by
  have hsubset : (p :: pre).toFinset ⊆ Q.primeFactors := by
    intro r hr
    have hrmem : r ∈ p :: pre := List.mem_toFinset.mp hr
    obtain ⟨k, hk⟩ := member_dvd_list_product (p :: pre) r hrmem
    have hdiv : r ∣ Q := by
      refine ⟨a * k, ?_⟩
      calc
        Q = a * (p :: pre).prod := hprod.symm
        _ = a * (r * k) := by rw [hk]
        _ = r * (a * k) := by ac_rfl
    exact Nat.mem_primeFactors.mpr ⟨hprime r hrmem, hdiv, hQ⟩
  have hcard : (p :: pre).toFinset.card = 6 := by
    rw [List.toFinset_card_of_nodup hno]
    simp [hlen]
  calc
    6 = (p :: pre).toFinset.card := hcard.symm
    _ ≤ Q.primeFactors.card := Finset.card_le_card hsubset

/-- On the ORIGINAL receiver-generated fifthExclusive event, the
q0 fibre PLUS-beta sum vanishes when q0 has fewer than six distinct prime factors. The fifth
history is proved to contain five actual selected rough primes; the
sixth p belongs to its genuine remainingAfter LIST. -/
theorem actual_fifth_q0_plus_zero_of_lt_six_factors
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (hN : 8 ≤ N) (hFew : ((N - 2) / 2).primeFactors.card < 6) :
    exceptionalFifthPlusFibre N cap w L X fifth.selectedAfter p = 0 := by
  have hlen : fifth.selectedAfter.length = 5 :=
    actual_fifth_exclusive_length_five
      delta n e q om N cap w z L X (receiverTest N)
      state hstate fifth hfifth
  have hjoin :
      fifth.selectedAfter.reverse ++ fifth.remainingAfter <+
        roughPrimeUniverse N cap w z := by
    simpa [P4AOriginalFull87OrderedSixthSuffix.eventSelected,
      P4AOriginalFull87ActualSixthSuffix.eventSixthSuffix] using
      (actual_event_joined_history_original_rough
        delta n e q om N cap w z L X (receiverTest N)
        state hstate (.fifthExclusive fifth) hfifth)
  have hjoinedNodup :
      (fifth.selectedAfter.reverse ++ fifth.remainingAfter).Nodup :=
    (roughPrimeUniverse_nodup N cap w z).sublist hjoin
  have hselRev : fifth.selectedAfter.reverse.Nodup :=
    List.Nodup.of_append_left hjoinedNodup
  have hsel : fifth.selectedAfter.Nodup := by
    simpa using hselRev
  have hpnot : p ∉ fifth.selectedAfter := by
    intro hm
    have hlt := actual_event_suffix_lt_every_selected
      delta n e q om N cap w z L X (receiverTest N)
      state hstate (.fifthExclusive fifth) hfifth p hp p hm
    omega
  have hno : (p :: fifth.selectedAfter).Nodup :=
    List.nodup_cons.mpr ⟨hpnot, hsel⟩
  have hprime (r : ℕ) (hr : r ∈ p :: fifth.selectedAfter) :
      Nat.Prime r := by
    rcases List.mem_cons.mp hr with heq | hrest
    · subst r
      exact mem_roughPrimeUniverse_prime
        (hjoin.subset (List.mem_append.mpr (Or.inr hp)))
    · have hrev : r ∈ fifth.selectedAfter.reverse := by
        simpa using hrest
      exact mem_roughPrimeUniverse_prime
        (hjoin.subset (List.mem_append.mpr (Or.inl hrev)))
  have hQpos : (N - 2) / 2 ≠ 0 := by omega
  unfold exceptionalFifthPlusFibre
  apply Finset.sum_eq_zero
  intro a ha
  have hneq :
      a * (p :: fifth.selectedAfter).prod ≠ (N - 2) / 2 := by
    intro heq
    have h6 := six_distinct_prime_factors_of_product
      ((N - 2) / 2) a p fifth.selectedAfter
      hQpos hlen hprime hno heq
    omega
  simp [hneq]

/-- Each original fifth-exclusive event, with every actual sixth
occurrence and the original signed fifth mass, has ZERO q0 contribution.
No absolute-value invoice and no multiplicity collapse is needed. -/
theorem actual_common_sixth_q0_zero_of_lt_six_factors
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (hN : 8 ≤ N) (hFew : ((N - 2) / 2).primeFactors.card < 6) :
    commonLargeSixthKernel N cap w L X (exceptionalCentreFibre N) fifth = 0 := by
  rw [common_sixth_exceptional_fibre_eq_original_weights]
  have hmap :
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          exceptionalFifthPlusFibre N cap w L X fifth.selectedAfter p)) =
      fifth.remainingAfter.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro p hp
    rw [actual_fifth_q0_plus_zero_of_lt_six_factors
      delta n e q om N cap w z L X state hstate fifth hfifth p hp hN hFew]
    simp
  rw [hmap]
  simp

/-- The other event constructors retain their genuine original
values (syntactically zero in commonSignedEventValue), while a real
fifth-exclusive constructor vanishes by the previous theorem. -/
theorem actual_signed_q0_event_zero_of_lt_six_factors
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state)
    (hN : 8 ≤ N) (hFew : ((N - 2) / 2).primeFactors.card < 6) :
    commonSignedEventValue N cap w L X (exceptionalCentreFibre N) ev = 0 := by
  cases ev with
  | fifthExclusive fifth =>
      have hz := actual_common_sixth_q0_zero_of_lt_six_factors
        delta n e q om N cap w z L X state hstate fifth hev hN hFew
      cases hk : fifth.kind <;>
        simp [commonSignedEventValue, hk, hz]
  | sixthFromBoth pre fifth =>
      simp [commonSignedEventValue]

/-- Genuine full stopped q0 signed occurrence coefficient vanishes on
the low-prime-support q0 subfamily. This is a conclusion about the SAME actual
sharedRankFour and receiverTest-generated fifth/sixth lists, not an
identification with fixed-policy physical rho. -/
theorem actual_fixed_fifth_q0_zero_of_lt_six_factors
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (hN : 8 ≤ N) (hFew : ((N - 2) / 2).primeFactors.card < 6) :
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
      exact actual_signed_q0_event_zero_of_lt_six_factors
        delta n e q om N cap w z L X state hs ev hev hN hFew
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

/-- Consequently, for q0 having fewer than six distinct prime factors, the ORIGINAL full
centre invoice equals its CLOSED lower-third invoice. The exceptional
upper-third contribution is not paid a second time. -/
theorem actual_fixed_fifth_centre_eq_lower_of_lt_six_factors_q0
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 0)
    (hN : 8 ≤ N) (hFew : ((N - 2) / 2).primeFactors.card < 6) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (chenCentrePrimeAPCount N N) =
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (lowerThirdCentre N) := by
  rw [actual_fixed_fifth_centre_eq_lower_plus_exception
    delta n e q om N cap w z L X hcomp hmod hN]
  rw [actual_fixed_fifth_q0_zero_of_lt_six_factors
    delta n e q om N cap w z L X hN hFew]
  ring

end
end ImbalancedChen.P4AOriginalFull87StoppedQ0FactorSupportSix
