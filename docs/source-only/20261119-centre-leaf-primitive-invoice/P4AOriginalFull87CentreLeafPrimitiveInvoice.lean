import ImbalancedChen.P4AOriginalFull87UpperCentreCoprimeGlobal
import ImbalancedChen.P4AOriginalFull87FrozenSurvivorInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The earlier global upper-centre vanishing holds only AFTER signed
occurrences have been summed. This file strengthens it at each ORIGINAL
fifthExclusive/sixth occurrence, before absolute values and before
either ordered List sum. It then removes the centre-prime correction
from the pre-existing frozenSurvivorUpperAbsoluteInvoice itself.

The actual sharedRankFour and receiver-generated event Lists, frozen
post-generation survivor filter, full Rosser index and modulus, fifth
signs, strict upper half, and occurrence multiplicities are unchanged.
No analytic asymptotic, independent reserve or external PP is assumed.
-/

namespace ImbalancedChen.P4AOriginalFull87CentreLeafPrimitiveInvoice
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87StoppedGlobalPrimeLedger
  (upperPrimeFibreTerm upperPrimeFibreEventValue)
open P4AOriginalFull87StoppedUpperHalfCoprimeUnmask
  (original_full_modulus_coprime_target)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_event_joined_history_original_rough)
open P4AOriginalFull87FrozenSurvivorInvoice
  (keepFrozenUpperSurvivor frozenSurvivorUpperAbsoluteInvoice
   abs_physical_stopped_after_lower_le_frozen_invoice)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthRosserIndices)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect (lowerHalfReceiver)
open P4AOriginalFull87FifthSignedPrimitive (actualFixedSignedFifthTail)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)

/-- At any *actual* rough sixth occurrence, even the individual
full-modulus Rosser fibre is zero for a prime dividing N. No
cancellation between fifth histories is used. -/
theorem actual_upper_fibre_term_zero_at_centre_prime
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hP : P ∈ chenPrimePrefix N) (hdiv : P ∣ N)
    (hrough : ∀ r ∈ p :: pre,
      r ∈ roughPrimeUniverse N cap w z) :
    upperPrimeFibreTerm N cap w L X P pre p = 0 := by
  by_contra hnon
  have hgate :
      2 * P < N ∧ X < N - P ∧
        (N - P) / (p :: pre).prod ∈
          largeFifthRosserIndices N cap w X pre ∧
        ((N - P) / (p :: pre).prod) *
          (p :: pre).prod = N - P := by
    by_contra hnot
    apply hnon
    simp [upperPrimeFibreTerm, hnot]
  have hfull : Nat.Coprime
      (((N - P) / (p :: pre).prod) *
        (p :: pre).prod) N :=
    original_full_modulus_coprime_target
      N cap w z X pre p ((N - P) / (p :: pre).prod)
      hgate.2.2.1 hrough
  have hq : Nat.Coprime (N - P) N := by
    simpa only [hgate.2.2.2] using hfull
  have hcop : Nat.Coprime P N :=
    (Nat.coprime_self_sub_left (mem_chenPrimePrefix.mp hP).1).mp hq
  exact ((mem_chenPrimePrefix.mp hP).2.coprime_iff_not_dvd.mp hcop) hdiv

/-- Centre-divisor vanishing is termwise in the genuine sixth suffix,
for each admitted fifthExclusive event. Inherited BOTH entries still
have their original zero upper valuation; no mask is imposed on them. -/
theorem actual_upper_event_zero_at_centre_prime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth delta n e q om
      N cap w L X (receiverTest N) state)
    (hP : P ∈ chenPrimePrefix N) (hdiv : P ∣ N) :
    upperPrimeFibreEventValue N cap w L X P ev = 0 := by
  cases ev with
  | sixthFromBoth pre fifth =>
      rfl
  | fifthExclusive fifth =>
      have hjoined :
          fifth.selectedAfter.reverse ++ fifth.remainingAfter <+
            roughPrimeUniverse N cap w z := by
        simpa [P4AOriginalFull87OrderedSixthSuffix.eventSelected,
          P4AOriginalFull87ActualSixthSuffix.eventSixthSuffix] using
          (actual_event_joined_history_original_rough
            delta n e q om N cap w z L X
            (receiverTest N) state hstate
            (.fifthExclusive fifth) hev)
      have hterm (p : ℕ) (hp : p ∈ fifth.remainingAfter) :
          upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p = 0 := by
        have hrough : ∀ r ∈ p :: fifth.selectedAfter,
            r ∈ roughPrimeUniverse N cap w z := by
          intro r hr
          rcases List.mem_cons.mp hr with hpr | hpre
          · subst r
            exact hjoined.subset (List.mem_append.mpr (Or.inr hp))
          · have hrev : r ∈ fifth.selectedAfter.reverse := by
              simpa using hpre
            exact hjoined.subset (List.mem_append.mpr (Or.inl hrev))
        exact actual_upper_fibre_term_zero_at_centre_prime
          N cap w z L X P fifth.selectedAfter p hP hdiv hrough
      have hmap :
          (fifth.remainingAfter.map (fun p =>
            signedTreeCoefficient true fifth.massAfter *
              upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)) =
          fifth.remainingAfter.map (fun _ => (0 : ℝ)) := by
        apply List.map_congr_left
        intro p hp
        rw [hterm p hp]
        ring
      have hsum :
          (fifth.remainingAfter.map (fun p =>
            signedTreeCoefficient true fifth.massAfter *
              upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)).sum =
          0 := by
        rw [hmap]
        simp
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [upperPrimeFibreEventValue, hk, hsum]
      | licensedOnly =>
          simpa [upperPrimeFibreEventValue, hk, hsum]
      | both =>
          simp [upperPrimeFibreEventValue, hk]

/-- The original nested absolute leaf cost at one prime. This is
exactly the summand of the PRE-EXISTING absolute physical invoice. -/
private def survivorLeafAbsoluteAtPrime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X P : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N
          ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map (fun ev =>
        |upperPrimeFibreEventValue N cap w
          ((N : ℝ) ^ epsilon) X P ev|)).sum)).sum

/-- Every *leaf* in the absolute invoice is zero at a centre-dividing
prime, not merely the signed global coefficient. In particular there
can be no hidden cancellation creating a positive absolute bill. -/
theorem survivor_leaf_absolute_zero_at_centre_prime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X P : ℕ)
    (hP : P ∈ chenPrimePrefix N) (hdiv : P ∣ N) :
    survivorLeafAbsoluteAtPrime
      delta n e q om N cap w epsilon X P = 0 := by
  unfold survivorLeafAbsoluteAtPrime
  have hout :
      ((sharedRankFour e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
        (((actualFifthSixthWithoutBoth delta n e q om N cap w
          ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
            (keepFrozenUpperSurvivor N
              ((N : ℝ) ^ ((19 : ℝ) / 96))
              ((N : ℝ) ^ epsilon) X)).map (fun ev =>
            |upperPrimeFibreEventValue N cap w
              ((N : ℝ) ^ epsilon) X P ev|)).sum)) =
      (sharedRankFour e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro state hstate
    have hinner :
        (((actualFifthSixthWithoutBoth delta n e q om N cap w
          ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
            (keepFrozenUpperSurvivor N
              ((N : ℝ) ^ ((19 : ℝ) / 96))
              ((N : ℝ) ^ epsilon) X)).map (fun ev =>
            |upperPrimeFibreEventValue N cap w
              ((N : ℝ) ^ epsilon) X P ev|)) =
        ((actualFifthSixthWithoutBoth delta n e q om N cap w
          ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
            (keepFrozenUpperSurvivor N
              ((N : ℝ) ^ ((19 : ℝ) / 96))
              ((N : ℝ) ^ epsilon) X)).map (fun _ => (0 : ℝ)) := by
      apply List.map_congr_left
      intro ev hev
      have hsource :
          ev ∈ actualFifthSixthWithoutBoth delta n e q om
            N cap w ((N : ℝ) ^ epsilon) X (receiverTest N) state :=
        List.mem_of_mem_filter hev
      have hz := actual_upper_event_zero_at_centre_prime
        delta n e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96)) ((N : ℝ) ^ epsilon)
        X P state hstate ev hsource hP hdiv
      simp [hz]
    rw [hinner]
    simp
  rw [hout]
  simp

/-- The same original absolute invoice, reindexed ONLY on its actual
centre-coprime prime carrier. The ordered parent and event axes, their
weights and the original survivor selector are untouched. -/
def frozenSurvivorUpperPrimitiveAbsoluteInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) : ℝ :=
  ∑ P ∈ (chenAdditivePrimeCarrier N).filter (fun P => 2 * P < N),
    survivorLeafAbsoluteAtPrime delta n e q om N cap w epsilon X P

/-- Exact equality of the old absolute invoice and its primitive
reindexing. Unlike global signed vanishing, this removes the full
absolute centre-prime cost, term by term. No new error is paid. -/
theorem frozen_survivor_upper_absolute_invoice_eq_primitive
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) :
    frozenSurvivorUpperAbsoluteInvoice
      delta n e q om N cap w epsilon X =
    frozenSurvivorUpperPrimitiveAbsoluteInvoice
      delta n e q om N cap w epsilon X := by
  unfold frozenSurvivorUpperAbsoluteInvoice
    frozenSurvivorUpperPrimitiveAbsoluteInvoice
  change
    (∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
      survivorLeafAbsoluteAtPrime delta n e q om N cap w epsilon X P) =
    ∑ P ∈ (chenAdditivePrimeCarrier N).filter (fun P => 2 * P < N),
      survivorLeafAbsoluteAtPrime delta n e q om N cap w epsilon X P
  rw [chenAdditivePrimeCarrier_eq_prefix_filter]
  have hfilter :
      ((chenPrimePrefix N).filter (fun P => ¬P ∣ N)).filter
          (fun P => 2 * P < N) =
      ((chenPrimePrefix N).filter (fun P => 2 * P < N)).filter
          (fun P => ¬P ∣ N) := by
    ext P
    simp only [Finset.mem_filter]
    tauto
  rw [hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P hmem
  by_cases hd : P ∣ N
  · have hP : P ∈ chenPrimePrefix N :=
      (Finset.mem_filter.mp hmem).1
    have hz := survivor_leaf_absolute_zero_at_centre_prime
      delta n e q om N cap w epsilon X P hP hd
    simp [hd, hz]
  · simp [hd]

/-- The existing stopped physical inequality has the same numerical
value after primitive reindexing. The lower receiver is subtracted ONCE;
this is not an additional reserve or a new asymptotic premise. -/
theorem abs_physical_stopped_after_lower_le_primitive_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    |(rawStopped e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X (receiverTest N) -
        licensedStopped delta n e q om N cap w
          ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X (receiverTest N)) -
      actualFixedSignedFifthTail delta n e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X (lowerHalfReceiver N)| ≤
    frozenSurvivorUpperPrimitiveAbsoluteInvoice
      delta n e q om N cap w epsilon X := by
  have hbase := abs_physical_stopped_after_lower_le_frozen_invoice
    delta n e q om N cap w epsilon X he hN heps hX
  rw [frozen_survivor_upper_absolute_invoice_eq_primitive] at hbase
  exact hbase

end
end ImbalancedChen.P4AOriginalFull87CentreLeafPrimitiveInvoice
