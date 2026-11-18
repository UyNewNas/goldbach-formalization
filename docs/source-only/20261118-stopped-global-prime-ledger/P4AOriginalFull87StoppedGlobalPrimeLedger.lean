import ImbalancedChen.P4AOriginalFull87StoppedUpperHalfCoprimeUnmask
import ImbalancedChen.P4AOriginalFull87FifthSignedPrimitive
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A global prime-indexed coefficient for the SAME actual fifth/sixth stopped
event generator. The earlier exact prime quotient formula held for a single
fifth event and one ordered sixth list. Here the prime sum is interchanged
with both actual event and parent lists, while keeping each occurrence,
fifth-gate sign, complete Rosser quotient, and the strict high-q boundary.

This is a finite exact ledger, not a prime-distribution estimate.
The surviving quotient/support test is an arithmetic filter; the frozen
smooth-weight PP premise is not invoked.
-/

namespace ImbalancedChen.P4AOriginalFull87StoppedGlobalPrimeLedger
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87StoppedUpperHalfPrimeDirect (upperHalfReceiver)
open P4AOriginalFull87StoppedUpperHalfCoprimeUnmask
  (actual_common_sixth_unmasked_prime_prefix)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthRosserIndices)
open P4AOriginalFull87CommonSixthSignedKernel
  (commonLargeSixthKernel commonSignedEventValue)
open P4AOriginalFull87FifthSignedPrimitive
  (actualFixedSignedFifthTail)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents
  (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice
  (actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization
  (sharedRankFour)
open P4AOriginalFull87EighthPrimeMeanLedger
  (receiverTest)

/-- Interchange a finite prime Finset with a literal List of occurrences.
No List-to-Finset conversion is made for the outer source. -/
private theorem list_finset_sum_swap {α : Type*}
    (xs : List α) (S : Finset ℕ) (f : α → ℕ → ℝ) :
    (xs.map (fun x => ∑ P ∈ S, f x P)).sum =
      ∑ P ∈ S, (xs.map (fun x => f x P)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, Finset.sum_add_distrib]

/-- The exact original quotient/support indicator for a fixed prime P,
one actual fifth history, and one sixth occurrence. The Rosser beta is
attached to the same complete modulus N-P; no smooth replacement occurs. -/
def upperPrimeFibreTerm
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ) : ℝ :=
  if 2 * P < N ∧ X < N - P ∧
      (N - P) / (p :: pre).prod ∈
        largeFifthRosserIndices N cap w X pre ∧
      ((N - P) / (p :: pre).prod) *
        (p :: pre).prod = N - P
  then actualSmallRosserPlus N cap w L
      ((N - P) / (p :: pre).prod)
  else 0

/-- EXACT fifth gate sign and actual sixth occurrence sum, now at one
fixed original prime P. Both and direct-sixth constructors are zero only
as in the preexisting common signed event valuation. -/
def upperPrimeFibreEventValue
    (N cap : ℕ) (w L : ℝ) (X P : ℕ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      let v : ℝ :=
        (fifth.remainingAfter.map (fun p =>
          signedTreeCoefficient true fifth.massAfter *
            upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)).sum
      match fifth.kind with
      | .rawOnly => v
      | .licensedOnly => -v
      | .both => 0
  | .sixthFromBoth _ _ => 0

/-- Genuine fifth/sixth prime-exchange on an original admitted event.
The actual receiver-generated history remains fixed and all copies in
fifth.remainingAfter are counted. -/
private theorem actual_fifth_prime_exchange
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state) :
    commonLargeSixthKernel N cap w L X
        (upperHalfReceiver N) fifth =
      ∑ P ∈ chenPrimePrefix N,
        (fifth.remainingAfter.map (fun p =>
          signedTreeCoefficient true fifth.massAfter *
            upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)).sum := by
  rw [actual_common_sixth_unmasked_prime_prefix
    delta n e q om N cap w z L X state hstate fifth hfifth]
  let c : ℝ := signedTreeCoefficient true fifth.massAfter
  change
    (fifth.remainingAfter.map (fun p =>
      c * (∑ P ∈ chenPrimePrefix N,
        upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p))).sum = _
  calc
    _ = (fifth.remainingAfter.map (fun p =>
          ∑ P ∈ chenPrimePrefix N,
            c * upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro p hp
          rw [Finset.mul_sum]
    _ = _ := list_finset_sum_swap fifth.remainingAfter (chenPrimePrefix N)
      (fun p P => c * upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)

/-- Exchange the real event kernel with an original prime index.
The event population is NOT regenerated using the prime indicator. -/
theorem actual_event_upper_prime_exchange
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth delta n e q om
      N cap w L X (receiverTest N) state) :
    commonSignedEventValue N cap w L X (upperHalfReceiver N) ev =
      ∑ P ∈ chenPrimePrefix N,
        upperPrimeFibreEventValue N cap w L X P ev := by
  cases ev with
  | fifthExclusive fifth =>
      have h := actual_fifth_prime_exchange
        delta n e q om N cap w z L X state hstate fifth hev
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [commonSignedEventValue, upperPrimeFibreEventValue, hk]
            using h
      | licensedOnly =>
          simpa [commonSignedEventValue, upperPrimeFibreEventValue, hk,
            Finset.sum_neg_distrib] using congrArg Neg.neg h
      | both =>
          simp [commonSignedEventValue, upperPrimeFibreEventValue, hk]
  | sixthFromBoth pre fifth =>
      simp [commonSignedEventValue, upperPrimeFibreEventValue]

/-- A genuine global stopped coefficient at ONE prime, summing the same
actual sharedRankFour states and same receiver-generated fifth/sixth
events. This definition never substitutes a PP density for the source. -/
def actualStoppedUpperPrimeCoefficient
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    ((actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state).map
        (upperPrimeFibreEventValue N cap w L X P)).sum)).sum

/-- Global finite Fubini. A single actual stopped tree is now expressed
as a prime-indexed sum of its exact SIGNED coefficients, with the same
fifth-gate action, full Rosser support, strict boundaries, and all
original List occurrences. This is not an asymptotic saving. -/
theorem actual_fixed_stopped_upper_primewise
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
        (upperHalfReceiver N) =
      ∑ P ∈ chenPrimePrefix N,
        actualStoppedUpperPrimeCoefficient
          delta n e q om N cap w z L X P := by
  let states := sharedRankFour e q om N cap w z
  let events := fun state =>
    actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state
  let S := chenPrimePrefix N
  have hstate (state : FirstExitDepthState ℕ) (hs : state ∈ states) :
      ((events state).map
        (commonSignedEventValue N cap w L X (upperHalfReceiver N))).sum =
      ∑ P ∈ S,
        ((events state).map
          (upperPrimeFibreEventValue N cap w L X P)).sum := by
    calc
      _ = ((events state).map (fun ev =>
            ∑ P ∈ S,
              upperPrimeFibreEventValue N cap w L X P ev)).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro ev hev
            exact actual_event_upper_prime_exchange
              delta n e q om N cap w z L X state hs ev hev
      _ = _ := list_finset_sum_swap (events state) S
        (fun ev P => upperPrimeFibreEventValue N cap w L X P ev)
  change
    (states.map (fun state =>
      ((events state).map
        (commonSignedEventValue N cap w L X (upperHalfReceiver N))).sum)).sum =
      ∑ P ∈ S,
        (states.map (fun state =>
          ((events state).map
            (upperPrimeFibreEventValue N cap w L X P)).sum)).sum
  calc
    _ = (states.map (fun state =>
          ∑ P ∈ S,
            ((events state).map
              (upperPrimeFibreEventValue N cap w L X P)).sum)).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro state hs
            exact hstate state hs
    _ = _ := list_finset_sum_swap states S (fun state P =>
      ((events state).map
        (upperPrimeFibreEventValue N cap w L X P)).sum)

/-- The strict 2P<N boundary is real: no contribution from primes at
or above the upper-half cutoff, even before global regrouping. -/
theorem upper_prime_fibre_event_zero_outside_half
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (hP : ¬ 2 * P < N) (ev : FifthSixthStoppedEvent ℕ) :
    upperPrimeFibreEventValue N cap w L X P ev = 0 := by
  cases ev with
  | fifthExclusive fifth =>
      simp [upperPrimeFibreEventValue, upperPrimeFibreTerm, hP]
  | sixthFromBoth pre fifth =>
      rfl

theorem actual_stopped_prime_coefficient_zero_outside_half
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (hP : ¬ 2 * P < N) :
    actualStoppedUpperPrimeCoefficient
      delta n e q om N cap w z L X P = 0 := by
  unfold actualStoppedUpperPrimeCoefficient
  simp [upper_prime_fibre_event_zero_outside_half N cap w L X P hP]

/-- Exactly one global prime ledger restricted to the true upper-half
carrier. Equality 2P=N belongs to the OTHER half, not to this term.
No arithmetic quotient mask is discarded or reinterpreted as smooth. -/
theorem actual_fixed_stopped_upper_primewise_strict_half
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
        (upperHalfReceiver N) =
      ∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
        actualStoppedUpperPrimeCoefficient
          delta n e q om N cap w z L X P := by
  rw [actual_fixed_stopped_upper_primewise, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hh : 2 * P < N
  · simp [hh]
  · simp [hh, actual_stopped_prime_coefficient_zero_outside_half
      delta n e q om N cap w z L X P hh]

end
end ImbalancedChen.P4AOriginalFull87StoppedGlobalPrimeLedger
