import ImbalancedChen.P4AOriginalFull87SurvivorFullRoomBridge
import ImbalancedChen.P4AOriginalFull87UpperPrimeActualSupport
import ImbalancedChen.P4AOriginalFull87StoppedUpperHalfCoprimeUnmask
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The original, receiver-generated stopped upper prime coefficient is
pointwise ZERO at every centre-dividing prime P. This is not a
generic prime AP estimate: it follows from the ACTUAL fifth Rosser
support and the ACTUAL ordered rough sixth suffix, whose entire
modulus is coprime to the same Goldbach centre N.

The earlier coprime-unmask theorem established an equality of fibre
sums. Here the deduction is made at the full, signed, dynamically
parented global coefficient and then at the exact frozen-survivor
coefficient. The upper centre-prime correction therefore has zero
finite physical cost; the lower receiver's centre term is untouched.

No original source, survivor selector, Rosser beta, occurrence order,
or signed coefficient changes. No density limit or PP is invoked.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperCentreCoprimeGlobal
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87StoppedGlobalPrimeLedger
  (actualStoppedUpperPrimeCoefficient)
open P4AOriginalFull87UpperPrimeActualSupport
  (actual_upper_prime_nonzero_has_power_filtered_witness)
open P4AOriginalFull87StoppedUpperHalfCoprimeUnmask
  (original_full_modulus_coprime_target)
open P4AOriginalFull87FrozenSurvivorInvoice
  (frozenSurvivorUpperPrimeCoefficient
   actual_upper_prime_eq_frozen_survivor_coefficient)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_event_joined_history_original_rough)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)

/-- A NONZERO original stopped upper coefficient at a genuine prime P
forces the prime itself to be coprime to N. The witnesses come from the
same actual sharedRankFour state and original fifth/sixth event source,
not from an existentially fabricated modulus or a changed producer. -/
theorem actual_stopped_upper_prime_nonzero_coprime_centre
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (hP : P ∈ chenPrimePrefix N)
    (hnon : actualStoppedUpperPrimeCoefficient
      delta n e q om N cap w z L X P ≠ 0) :
    Nat.Coprime P N := by
  obtain ⟨state, hstate, fifth, hfifth, _, p, hp,
      _, _, _, ha, hmul, _⟩ :=
    actual_upper_prime_nonzero_has_power_filtered_witness
      delta n e q om N cap w z L X P hnon
  have hjoined :
      fifth.selectedAfter.reverse ++ fifth.remainingAfter <+
        roughPrimeUniverse N cap w z := by
    simpa [P4AOriginalFull87OrderedSixthSuffix.eventSelected,
      P4AOriginalFull87ActualSixthSuffix.eventSixthSuffix] using
      (actual_event_joined_history_original_rough
        delta n e q om N cap w z L X
        (receiverTest N) state hstate (.fifthExclusive fifth) hfifth)
  have hrough :
      ∀ r ∈ p :: fifth.selectedAfter,
        r ∈ roughPrimeUniverse N cap w z := by
    intro r hr
    rcases List.mem_cons.mp hr with hpr | hpre
    · subst r
      exact hjoined.subset (List.mem_append.mpr (Or.inr hp))
    · have hrev : r ∈ fifth.selectedAfter.reverse := by
        simpa using hpre
      exact hjoined.subset (List.mem_append.mpr (Or.inl hrev))
  let a : ℕ := (N - P) / (p :: fifth.selectedAfter).prod
  have hfull : Nat.Coprime
      (a * (p :: fifth.selectedAfter).prod) N :=
    original_full_modulus_coprime_target N cap w z X
      fifth.selectedAfter p a ha hrough
  have hq : Nat.Coprime (N - P) N := by
    simpa only [a, hmul] using hfull
  exact (Nat.coprime_self_sub_left
    (mem_chenPrimePrefix.mp hP).1).mp hq

/-- The original stopped upper coefficient has NO centre-prime
exception, pointwise. This cannot be claimed for the separate lower
receiver and does not remove its exceptional-prime invoice. -/
theorem actual_stopped_upper_zero_at_centre_prime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (hP : P ∈ chenPrimePrefix N) (hdiv : P ∣ N) :
    actualStoppedUpperPrimeCoefficient
      delta n e q om N cap w z L X P = 0 := by
  by_contra hnon
  have hc := actual_stopped_upper_prime_nonzero_coprime_centre
    delta n e q om N cap w z L X P hP hnon
  exact ((mem_chenPrimePrefix.mp hP).2.coprime_iff_not_dvd.mp hc) hdiv

/-- The exact post-generation frozen survivor upper coefficient
inherits the same zero correction, at its literal fixed parameters.
No additional selector is placed on inherited BOTH events. -/
theorem frozen_survivor_upper_zero_at_centre_prime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X P : ℕ)
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hP : P ∈ chenPrimePrefix N) (hdiv : P ∣ N) :
    frozenSurvivorUpperPrimeCoefficient
      delta n e q om N cap w epsilon X P = 0 := by
  rw [← actual_upper_prime_eq_frozen_survivor_coefficient
    delta n e q om N cap w epsilon X P hN heps]
  exact actual_stopped_upper_zero_at_centre_prime
    delta n e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
    ((N : ℝ) ^ epsilon) X P hP hdiv

/-- Literal FINITE upper centre-divisor correction on the same
frozen-survivor signed coefficient. This is a diagnostic extraction,
not a second physical payment or a changed producer. -/
def frozenSurvivorUpperCentrePrimeBill
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) : ℝ :=
  ∑ P ∈ (chenPrimePrefix N).filter (fun P => P ∣ N ∧ 2 * P < N),
    |frozenSurvivorUpperPrimeCoefficient
      delta n e q om N cap w epsilon X P|

/-- The entire upper centre-divisor bill vanishes EXACTLY. It must
not also be subtracted from the lower-half or ordinary full-q budget. -/
theorem frozen_survivor_upper_centre_prime_bill_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ)) :
    frozenSurvivorUpperCentrePrimeBill
      delta n e q om N cap w epsilon X = 0 := by
  unfold frozenSurvivorUpperCentrePrimeBill
  apply Finset.sum_eq_zero
  intro P hP
  obtain ⟨hprefix, hdiv, _⟩ := Finset.mem_filter.mp hP
  rw [frozen_survivor_upper_zero_at_centre_prime
    delta n e q om N cap w epsilon X P hN heps hprefix hdiv]
  simp

end
end ImbalancedChen.P4AOriginalFull87UpperCentreCoprimeGlobal
