import ImbalancedChen.P4AOriginalFull87SignedBetaFrozenGlobal
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The exact missing PLUS-Rosser integer-quotient room is not an error term:
apart from zero beta coefficients, its quotient a is missing precisely
when the REFLECTED integer N - a * (p :: pre).prod is absent from the
ORIGINAL chenPrimePrefix N.  The actual room enforces the strict upper
half, strict high-q boundary and complete product without a surrogate
prime carrier. This turns a Boolean nonzero-prime-image definition into
a concrete arithmetic complement, not into a small error.

The second part transports this equality through the ORIGINAL ordered
sixth suffix, fifth RAW/LICENSED signs and actual frozen sharedRankFour
parent/event Lists.  No asymptotic payment is claimed.
-/

namespace ImbalancedChen.P4AOriginalFull87ReflectedNonprimeRoom
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87ActualPrimitiveRosserRoom
  (actualPrimitiveRosserRoom)
open P4AOriginalFull87FullUpperQuotientRoom
  (fullUpperQuotientRoom originalFullUpperNonzeroPrimeCarrier)
open P4AOriginalFull87SignedBetaMissingRoom
  (occupiedOriginalUpperBetaQuotients
   unoccupiedOriginalUpperBetaQuotients
   occupied_original_upper_subset_actual_room)
open P4AOriginalFull87SignedBetaFrozenGlobal
  (originalSignedMissingBetaEvent
   frozenSurvivorSignedMissingBetaRoom
   frozenSurvivorSignedFullBetaRoom
   physical_stopped_after_lower_eq_signed_beta_difference)
open P4AOriginalFull87StoppedGlobalPrimeLedger (upperPrimeFibreTerm)
open P4AOriginalFull87PlusBetaPowerFilter (largeFifthRosserIndices)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_event_joined_history_original_rough)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87FifthSignedPrimitive (actualFixedSignedFifthTail)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect (lowerHalfReceiver)

/-- The true missing room is a sum over missing reflected PRIME
membership, not a bare small error or the complement of arbitrary
independent sieve coefficients. A reflected 0 or 1 also belongs here. -/
def reflectedNonprimeRosserRoom (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) : Finset ℕ :=
  (actualPrimitiveRosserRoom N cap w L X pre p).filter
    (fun a => N - a * (p :: pre).prod ∉ chenPrimePrefix N)

/-- Every member of the actual bounded room has a POSITIVE complete
modulus. The case b=0 makes the original two-sided room empty. The
reflective product is exact, including both strict boundaries. -/
private theorem room_reflected_gate
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p a : ℕ)
    (ha : a ∈ actualPrimitiveRosserRoom N cap w L X pre p) :
    let b := (p :: pre).prod
    2 * (N - a * b) < N ∧
    X < N - (N - a * b) ∧
    a ∈ largeFifthRosserIndices N cap w X pre ∧
    (N - (N - a * b)) / b = a ∧
    ((N - (N - a * b)) / b) * b = N - (N - a * b) := by
  let b : ℕ := (p :: pre).prod
  have haRoom : a ∈ fullUpperQuotientRoom N X L pre p :=
    (Finset.mem_filter.mp ha).1
  have haIndex : a ∈ largeFifthRosserIndices N cap w X pre :=
    (Finset.mem_filter.mp ha).2.1
  change a ∈ Finset.Ico
    ((N / (2 * b) + 1).max (X / b + 1))
    ((Nat.ceil L).min (N / b + 1)) at haRoom
  have hI := Finset.mem_Ico.mp haRoom
  have hb : 0 < b := by
    by_contra hn
    have hz : b = 0 := Nat.eq_zero_of_not_pos hn
    have hl : N / (2 * b) + 1 ≤ a :=
      (le_max_left _ _).trans hI.1
    have hu : a < N / b + 1 :=
      lt_of_lt_of_le hI.2 (min_le_right _ _)
    simp [hz] at hl hu
    omega
  have hloHalf : N / (2 * b) < a := by
    have h := (le_max_left (N / (2 * b) + 1)
      (X / b + 1)).trans hI.1
    omega
  have hloX : X / b < a := by
    have h := (le_max_right (N / (2 * b) + 1)
      (X / b + 1)).trans hI.1
    omega
  have hhi : a ≤ N / b := by
    have h := lt_of_lt_of_le hI.2
      (min_le_right (Nat.ceil L) (N / b + 1))
    omega
  have hN : N < a * (2 * b) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * b)).mp hloHalf
  have hX : X < a * b := (Nat.div_lt_iff_lt_mul hb).mp hloX
  have hle : a * b ≤ N := (Nat.le_div_iff_mul_le hb).mp hhi
  have hdouble : N < 2 * (a * b) := by
    calc
      N < a * (2 * b) := hN
      _ = 2 * (a * b) := by ring
  have hhalf : 2 * (N - a * b) < N := by omega
  have hreflect : N - (N - a * b) = a * b := by omega
  have hquot : (N - (N - a * b)) / b = a := by
    rw [hreflect]
    exact Nat.mul_div_cancel a hb
  change 2 * (N - a * b) < N ∧
    X < N - (N - a * b) ∧
    a ∈ largeFifthRosserIndices N cap w X pre ∧
    (N - (N - a * b)) / b = a ∧
    ((N - (N - a * b)) / b) * b = N - (N - a * b)
  exact ⟨hhalf, by simpa [hreflect] using hX,
    haIndex, hquot, by rw [hquot, hreflect]⟩

/-- Unpack the literal original fibre gate, not a new prime predicate. -/
private theorem nonzero_original_fibre_gate
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hn : upperPrimeFibreTerm N cap w L X P pre p ≠ 0) :
    2 * P < N ∧
    ((N - P) / (p :: pre).prod) * (p :: pre).prod = N - P := by
  unfold upperPrimeFibreTerm at hn
  split_ifs at hn with hg
  · exact ⟨hg.1, hg.2.2.2⟩
  · contradiction

/-- On an actual room member, occupation of the original nonzero
prime fibre is equivalent to reflected prime membership AND nonzero
original PLUS beta. Prime targets with zero beta are unoccupied but
have exactly zero signed cost. -/
theorem occupied_iff_reflected_prime_and_nonzero_beta
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p a : ℕ)
    (ha : a ∈ actualPrimitiveRosserRoom N cap w L X pre p) :
    a ∈ occupiedOriginalUpperBetaQuotients N cap w L X pre p ↔
      N - a * (p :: pre).prod ∈ chenPrimePrefix N ∧
      actualSmallRosserPlus N cap w L a ≠ 0 := by
  let b : ℕ := (p :: pre).prod
  have hr := room_reflected_gate N cap w L X pre p a ha
  have hg :
      2 * (N - a * b) < N ∧
      X < N - (N - a * b) ∧
      (N - (N - a * b)) / b ∈
        largeFifthRosserIndices N cap w X pre ∧
      ((N - (N - a * b)) / b) * b = N - (N - a * b) :=
    ⟨hr.1, hr.2.1, by simpa [hr.2.2.2.1] using hr.2.2.1,
     hr.2.2.2.2⟩
  have hvalue :
      upperPrimeFibreTerm N cap w L X
        (N - a * b) pre p = actualSmallRosserPlus N cap w L a := by
    simp only [upperPrimeFibreTerm, if_pos hg, hr.2.2.2.1]
  constructor
  · intro hocc
    obtain ⟨P, hP, hquotP⟩ := Finset.mem_image.mp hocc
    have hcarrier := Finset.mem_filter.mp hP
    have hgateP := nonzero_original_fibre_gate
      N cap w L X P pre p hcarrier.2
    have hmul : a * b = N - P := by
      rw [← hquotP]
      exact hgateP.2
    have hreflect : N - a * b = P := by omega
    have hvP :
        upperPrimeFibreTerm N cap w L X P pre p =
          actualSmallRosserPlus N cap w L a := by
      simpa [hreflect] using hvalue
    constructor
    · simpa [hreflect] using hcarrier.1
    · intro hz
      apply hcarrier.2
      rw [hvP, hz]
  · rintro ⟨hprime, hbeta⟩
    refine Finset.mem_image.mpr
      ⟨N - a * b, Finset.mem_filter.mpr ⟨hprime, ?_⟩, ?_⟩
    · simpa [hvalue] using hbeta
    · exact hr.2.2.2.1

/-- Exact signed identification of the UNoccupied quotient invoice.
The nonprime condition is on the true reflected additive-prime prefix;
it is not an AP main term and is NOT estimated. -/
theorem unoccupied_signed_eq_reflected_nonprime
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hrough : ∀ r ∈ p :: pre, r ∈ roughPrimeUniverse N cap w z) :
    (∑ a ∈ unoccupiedOriginalUpperBetaQuotients
      N cap w L X pre p, actualSmallRosserPlus N cap w L a) =
    (∑ a ∈ reflectedNonprimeRosserRoom
      N cap w L X pre p, actualSmallRosserPlus N cap w L a) := by
  classical
  let room := actualPrimitiveRosserRoom N cap w L X pre p
  let occupied := occupiedOriginalUpperBetaQuotients N cap w L X pre p
  let beta := actualSmallRosserPlus N cap w L
  let prime := fun a : ℕ => N - a * (p :: pre).prod ∈ chenPrimePrefix N
  have hsub : occupied ⊆ room :=
    occupied_original_upper_subset_actual_room N cap w z L X pre p hrough
  have hsubPrime : occupied ⊆ room.filter prime := by
    intro a ha
    have haroom := hsub ha
    have hprime :=
      (occupied_iff_reflected_prime_and_nonzero_beta
        N cap w L X pre p a haroom).mp ha
    exact Finset.mem_filter.mpr ⟨haroom, hprime.1⟩
  have hsumPrime :
      (∑ a ∈ occupied, beta a) =
      (∑ a ∈ room.filter prime, beta a) := by
    apply Finset.sum_subset hsubPrime
    intro a ha hnot
    have haroom := (Finset.mem_filter.mp ha).1
    have hp := (Finset.mem_filter.mp ha).2
    by_contra hbeta
    exact hnot ((occupied_iff_reflected_prime_and_nonzero_beta
      N cap w L X pre p a haroom).mpr ⟨hp, hbeta⟩)
  have hsplit :
      (∑ a ∈ room.filter prime, beta a) +
      (∑ a ∈ room.filter (fun a => ¬ prime a), beta a) =
      ∑ a ∈ room, beta a := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hp : prime a <;> simp [hp]
  have hpartition :
      (∑ a ∈ room \ occupied, beta a) +
      (∑ a ∈ occupied, beta a) =
      ∑ a ∈ room, beta a :=
    Finset.sum_sdiff hsub
  unfold unoccupiedOriginalUpperBetaQuotients
    reflectedNonprimeRosserRoom
  change (∑ a ∈ room \ occupied, beta a) =
    ∑ a ∈ room.filter (fun a => ¬ prime a), beta a
  linarith

/-- The SAME original fifth history and ordered sixth suffix, with
every repeated occurrence and its actual signedTreeCoefficient. -/
private theorem actual_fifth_missing_eq_reflected_nonprime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hev : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w
        L X (receiverTest N) state) :
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
      (∑ a ∈ unoccupiedOriginalUpperBetaQuotients
        N cap w L X fifth.selectedAfter p,
        actualSmallRosserPlus N cap w L a))).sum =
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
      (∑ a ∈ reflectedNonprimeRosserRoom
        N cap w L X fifth.selectedAfter p,
        actualSmallRosserPlus N cap w L a))).sum := by
  have hjoined : fifth.selectedAfter.reverse ++ fifth.remainingAfter <+
      roughPrimeUniverse N cap w z := by
    simpa [P4AOriginalFull87OrderedSixthSuffix.eventSelected,
      P4AOriginalFull87ActualSixthSuffix.eventSixthSuffix] using
      (actual_event_joined_history_original_rough delta n e q om
        N cap w z L X (receiverTest N) state hstate
        (.fifthExclusive fifth) hev)
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hrough : ∀ r ∈ p :: fifth.selectedAfter,
      r ∈ roughPrimeUniverse N cap w z := by
    intro r hr
    rcases List.mem_cons.mp hr with hpr | hpre
    · subst r
      exact hjoined.subset (List.mem_append.mpr (Or.inr hp))
    · have hrev : r ∈ fifth.selectedAfter.reverse := by
        simpa using hpre
      exact hjoined.subset (List.mem_append.mpr (Or.inl hrev))
  exact congrArg (fun t : ℝ =>
    signedTreeCoefficient true fifth.massAfter * t)
    (unoccupied_signed_eq_reflected_nonprime N cap w z L X
      fifth.selectedAfter p hrough)

/-- Original admission sign: RAW-only positive, LICENSED-only negative.
The two inherited/BOTH constructors remain zero as before. -/
def originalSignedReflectedNonprimeBetaEvent
    (N cap : ℕ) (w L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      let v : ℝ := (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          (∑ a ∈ reflectedNonprimeRosserRoom N cap w L X
            fifth.selectedAfter p, actualSmallRosserPlus N cap w L a))).sum
      match fifth.kind with
      | .rawOnly => v
      | .licensedOnly => -v
      | .both => 0
  | .sixthFromBoth _ _ => 0

private theorem actual_event_missing_eq_reflected_nonprime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth delta n e q om
      N cap w L X (receiverTest N) state) :
    originalSignedMissingBetaEvent N cap w L X ev =
      originalSignedReflectedNonprimeBetaEvent N cap w L X ev := by
  cases ev with
  | sixthFromBoth pre fifth =>
      rfl
  | fifthExclusive fifth =>
      have h := actual_fifth_missing_eq_reflected_nonprime
        delta n e q om N cap w z L X state hs fifth hev
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [originalSignedMissingBetaEvent,
            originalSignedReflectedNonprimeBetaEvent, hk] using h
      | licensedOnly =>
          simpa [originalSignedMissingBetaEvent,
            originalSignedReflectedNonprimeBetaEvent, hk] using
            congrArg (fun t : ℝ => -t) h
      | both =>
          simp [originalSignedMissingBetaEvent,
            originalSignedReflectedNonprimeBetaEvent, hk]

/-- Same frozen parent, original ordered event list and post-generation
survivor selector. No occurrence or inherited branch is reclassified. -/
def frozenSurvivorSignedReflectedNonprimeBetaRoom
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (P4AOriginalFull87FrozenSurvivorInvoice.keepFrozenUpperSurvivor
          N ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (originalSignedReflectedNonprimeBetaEvent N cap w
        ((N : ℝ) ^ epsilon) X)).sum)).sum

theorem frozen_signed_missing_eq_reflected_nonprime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) :
    frozenSurvivorSignedMissingBetaRoom
      delta n e q om N cap w epsilon X =
    frozenSurvivorSignedReflectedNonprimeBetaRoom
      delta n e q om N cap w epsilon X := by
  unfold frozenSurvivorSignedMissingBetaRoom
    frozenSurvivorSignedReflectedNonprimeBetaRoom
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hs
  apply congrArg List.sum
  apply List.map_congr_left
  intro ev hev
  exact actual_event_missing_eq_reflected_nonprime
    delta n e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
    ((N : ℝ) ^ epsilon) X state hs ev
    (List.mem_of_mem_filter hev)

/-- The original physical stopped difference after ONE lower payment
is full PLUS beta minus the reflected-NONPRIME signed obstruction.
The latter is not o(H_N) without an actual same-rho prime estimate. -/
theorem physical_after_lower_eq_full_sub_reflected_nonprime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    (rawStopped e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
      ((N : ℝ) ^ epsilon) X (receiverTest N) -
     licensedStopped delta n e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))
      ((N : ℝ) ^ epsilon) X (receiverTest N)) -
     actualFixedSignedFifthTail delta n e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))
      ((N : ℝ) ^ epsilon) X (lowerHalfReceiver N) =
    frozenSurvivorSignedFullBetaRoom
      delta n e q om N cap w epsilon X -
    frozenSurvivorSignedReflectedNonprimeBetaRoom
      delta n e q om N cap w epsilon X := by
  rw [physical_stopped_after_lower_eq_signed_beta_difference
    delta n e q om N cap w epsilon X he hN heps hX]
  rw [frozen_signed_missing_eq_reflected_nonprime]

end
end ImbalancedChen.P4AOriginalFull87ReflectedNonprimeRoom
